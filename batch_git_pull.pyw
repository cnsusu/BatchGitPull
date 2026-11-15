#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BatchGitPull —— 批量对「总项目文件夹」下的多个 git 仓库执行 git pull。

用法：
  双击运行（GUI）          batch_git_pull.pyw
  GUI 并指定目录           pythonw batch_git_pull.pyw <目录>
  命令行模式（无界面）     python batch_git_pull.pyw --cli <目录> [--only a,b,c] [--merge] [--jobs N]
  自测                     python batch_git_pull.pyw --selftest

只做 git pull：不 stash / reset / checkout / clean / push，失败如实报告。
"""

import argparse
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    from tkinter import font as tkfont
except ImportError:  # 仅 CLI / 自测时允许没有 Tk
    tk = None

# ---------------------------------------------------------------------------
# 常量
# ---------------------------------------------------------------------------

APP_NAME = "BatchGitPull"
PULL_TIMEOUT = 120
FETCH_TIMEOUT = 60
CHECK_TIMEOUT = 15
CHECK_INTERVALS = (0, 5, 10, 30, 60)   # 自动检查间隔（分钟），0 = 关闭
DEFAULT_CHECK_MINUTES = 10
FOCUS_RECHECK_SECONDS = 15             # 窗口重新获得焦点时，距上次检查超过该秒数就刷新本地状态
MAX_RECENT = 10
MAX_JOBS = 8
DEFAULT_JOBS = 4
DETACHED_LABEL = "(游离 HEAD)"
BRANCH_UNKNOWN = "(读取失败)"

ST_IDLE = "未执行"
ST_WAIT = "等待中"
ST_RUN = "进行中"
ST_UPDATED = "已更新"
ST_UPTODATE = "已是最新"
ST_FAIL = "失败"
ST_TIMEOUT = "超时"
ST_CANCEL = "已取消"
BAD_STATUSES = (ST_FAIL, ST_TIMEOUT)

CREATE_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)

# 失败原因分类表：按顺序匹配（不区分大小写的子串），命中第一条即停
ERROR_RULES = [
    (("would be overwritten by merge", "Please commit your changes or stash them",
      "cannot pull with rebase"),
     "本地有未提交的修改与远端改动冲突，请先提交或贮藏"),
    (("untracked working tree files would be overwritten",),
     "本地未跟踪文件会被远端文件覆盖，请先移走或删除"),
    (("Not possible to fast-forward", "Diverging branches", "Need to specify how to reconcile"),
     "本地与远端已分叉（本地有未推送提交），需手动合并或变基"),
    (("Automatic merge failed", "CONFLICT ("),
     "合并产生冲突，仓库处于合并中状态，需手动解决"),
    (("You have not concluded your merge", "unmerged files"),
     "上次合并未完成，需先解决冲突并提交"),
    (("Authentication failed", "could not read Username", "could not read Password",
      "terminal prompts disabled", "HTTP 401", "error: 401"),
     "认证失败：凭证缺失或已失效，请先用 TortoiseGit/命令行手动拉取一次以更新凭证"),
    (("HTTP 403", "error: 403", "Permission denied"),
     "无权限访问该仓库"),
    (("Repository not found", "does not appear to be a git repository"),
     "远端仓库不存在或地址错误"),
    (("Could not resolve host",),
     "网络错误：无法解析域名"),
    (("Failed to connect", "Connection timed out", "Connection refused", "Connection was reset",
      "unable to access", "SSL", "RPC failed", "early EOF"),
     "网络错误：无法连接远端或传输中断"),
    (("couldn't find remote ref", "no such ref was fetched"),
     "远端对应分支不存在（可能已被删除）"),
    (("There is no tracking information",),
     "当前分支未设置上游分支"),
    (("You are not currently on a branch",),
     "处于游离 HEAD，未在任何分支上"),
    (("index.lock", "Another git process seems to be running"),
     "仓库被其他 git 进程占用（或残留 index.lock）"),
    (("dubious ownership",),
     "仓库目录所有者不受信任（需配置 safe.directory）"),
]

MSG_MERGE_PENDING = "上次合并未完成，需先解决冲突并提交"
MSG_REBASE_PENDING = "上次变基未完成，需先完成或中止变基"
MSG_DETACHED = "处于游离 HEAD，未在任何分支上"
MSG_NO_UPSTREAM = "当前分支未设置上游分支"

_CRED_RE = re.compile(r"([A-Za-z][A-Za-z0-9+.\-]*://)[^/@\s'\"]+@")


# ---------------------------------------------------------------------------
# 数据结构
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Repo:
    name: str
    path: str
    branch: str


@dataclass
class PullResult:
    status: str
    message: str
    detail: str
    seconds: float


@dataclass
class SyncInfo:
    """仓库同步状态（git fetch + git status 的结果）。"""
    ok: bool = False            # git status 成功
    cancelled: bool = False
    error: str = ""             # git status 失败原因
    fetched: bool = False       # 本次是否成功获取了远端
    fetch_error: str = ""       # 获取远端失败原因（此时「待拉取」基于上次获取的结果）
    branch: str = ""
    detached: bool = False
    upstream: str = ""
    upstream_gone: bool = False
    ahead: int = 0              # 本地未推送的提交数
    behind: int = 0             # 远端有而本地没有的提交数
    changed: int = 0            # 已跟踪文件的未提交改动（含已暂存）
    untracked: int = 0
    conflicts: int = 0
    detail: str = ""
    checked_at: float = 0.0


@dataclass
class ScanResult:
    repos: list
    ignored: int
    root_is_repo: bool


@dataclass
class GitOutput:
    cmd: list
    rc: int
    out: str
    err: str
    timed_out: bool
    timeout: float

    @property
    def text(self):
        return (self.out + ("\n" if self.out and self.err else "") + self.err).strip()

    def render(self):
        lines = ["$ " + subprocess.list2cmdline(self.cmd)]
        if self.text:
            lines.append(self.text)
        if self.timed_out:
            lines.append(f"[超时 {self.timeout:.0f}s，已终止]")
        else:
            lines.append(f"[退出码 {self.rc}]")
        return "\n".join(lines)


class ScanError(Exception):
    pass


# ---------------------------------------------------------------------------
# 进程控制
# ---------------------------------------------------------------------------

def kill_tree(proc):
    """终止进程及其子进程（git 会派生 git-remote-https 等子进程）。"""
    if proc.poll() is not None:
        return
    if os.name == "nt":
        try:
            subprocess.run(["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                           stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, creationflags=CREATE_NO_WINDOW, timeout=10)
        except Exception:
            pass
    try:
        proc.kill()
    except Exception:
        pass


class CancelToken:
    """停止信号 + 正在运行的 git 进程登记表。"""

    def __init__(self):
        self._event = threading.Event()
        self._lock = threading.Lock()
        self._procs = set()

    @property
    def cancelled(self):
        return self._event.is_set()

    def register(self, proc):
        with self._lock:
            self._procs.add(proc)
            cancelled = self._event.is_set()
        if cancelled:
            kill_tree(proc)

    def unregister(self, proc):
        with self._lock:
            self._procs.discard(proc)

    def cancel(self):
        self._event.set()
        with self._lock:
            procs = list(self._procs)
        # 杀进程放到后台线程，避免阻塞界面
        for p in procs:
            threading.Thread(target=kill_tree, args=(p,), daemon=True).start()


def git_env():
    env = os.environ.copy()
    env.update({
        "GIT_TERMINAL_PROMPT": "0",   # 凭证缺失时立即失败，不等待输入
        "GCM_INTERACTIVE": "never",   # Git Credential Manager 不弹窗
        "LC_ALL": "C",                # 输出英文，便于错误分类
        "LANG": "C",
        "LANGUAGE": "C",
    })
    return env


def _decode(data):
    return (data or b"").decode("utf-8", errors="replace")


def redact(text):
    """URL 中的凭证段脱敏：https://user:token@host -> https://***@host"""
    return _CRED_RE.sub(r"\1***@", text or "")


def run_git(repo_path, args, timeout, token=None):
    cmd = ["git", "-C", repo_path, "-c", "core.quotepath=false", *args]
    if token is not None and token.cancelled:
        return GitOutput(cmd, -1, "", "", False, timeout)
    try:
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, env=git_env(),
                                creationflags=CREATE_NO_WINDOW)
    except OSError as e:
        return GitOutput(cmd, 127, "", f"无法启动 git：{e}（请确认已安装 Git 并加入 PATH）",
                         False, timeout)
    if token is not None:
        token.register(proc)
    timed_out = False
    try:
        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_tree(proc)
            try:
                out, err = proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                out, err = b"", b""
    finally:
        if token is not None:
            token.unregister(proc)
    rc = proc.returncode if proc.returncode is not None else -1
    return GitOutput(cmd, rc, redact(_decode(out)), redact(_decode(err)), timed_out, timeout)


# ---------------------------------------------------------------------------
# 扫描
# ---------------------------------------------------------------------------

def is_repo_dir(path):
    # .git 可能是目录，也可能是文件（worktree / submodule）
    return os.path.exists(os.path.join(path, ".git"))


def read_branch(path):
    r = run_git(path, ["symbolic-ref", "--short", "-q", "HEAD"], CHECK_TIMEOUT)
    if r.rc == 0 and r.out.strip():
        return r.out.strip()
    if r.rc == 1:
        return DETACHED_LABEL
    return BRANCH_UNKNOWN


def scan_dir(root):
    root = os.path.abspath(root)
    if not os.path.isdir(root):
        raise ScanError(f"目录不存在：{root}")
    try:
        with os.scandir(root) as it:
            entries = list(it)
    except OSError as e:
        raise ScanError(f"无法读取目录：{root}（{e.strerror or e}）")

    candidates = []
    ignored = 0
    for e in sorted(entries, key=lambda x: x.name.lower()):
        try:
            if not e.is_dir() or e.name == ".git":
                continue
        except OSError:
            continue
        if is_repo_dir(e.path):
            candidates.append((e.name, e.path))
        else:
            ignored += 1

    root_is_repo = is_repo_dir(root)
    if root_is_repo:
        base = os.path.basename(root.rstrip("\\/")) or root
        candidates.insert(0, (f"{base} (根目录)", root))

    if candidates:
        with ThreadPoolExecutor(max_workers=8) as ex:
            branches = list(ex.map(lambda c: read_branch(c[1]), candidates))
    else:
        branches = []
    repos = [Repo(n, p, b) for (n, p), b in zip(candidates, branches)]
    return ScanResult(repos, ignored, root_is_repo)


def scan_repos(root):
    return scan_dir(root).repos


# ---------------------------------------------------------------------------
# 拉取
# ---------------------------------------------------------------------------

def classify_error(output):
    text = output or ""
    low = text.lower()
    for keywords, message in ERROR_RULES:
        for kw in keywords:
            if kw.lower() in low:
                return message
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    for ln in reversed(lines):
        if ln.lower().startswith(("fatal:", "error:")):
            return ln
    return lines[-1] if lines else ""


def pull_repo(repo, ff_only=True, token=None):
    token = token or CancelToken()
    t0 = time.monotonic()
    logs = []

    def git(args, timeout=CHECK_TIMEOUT):
        r = run_git(repo.path, args, timeout, token)
        logs.append(r.render())
        return r

    def done(status, message):
        return PullResult(status, message, "\n\n".join(logs), time.monotonic() - t0)

    def stopped(r):
        if token.cancelled:
            return done(ST_CANCEL, "已取消")
        if r.timed_out:
            return done(ST_TIMEOUT, f"命令执行超过 {r.timeout:.0f} 秒，已终止")
        return None

    def failed(r):
        return done(ST_FAIL, classify_error(r.text) or f"git 退出码 {r.rc}")

    if token.cancelled:
        return done(ST_CANCEL, "已取消")

    # 1. 预检（只读）
    r = git(["rev-parse", "--absolute-git-dir"])
    if (x := stopped(r)):
        return x
    if r.rc != 0:
        return failed(r)
    git_dir = r.out.strip()
    if os.path.exists(os.path.join(git_dir, "MERGE_HEAD")):
        return done(ST_FAIL, MSG_MERGE_PENDING)
    if any(os.path.exists(os.path.join(git_dir, d)) for d in ("rebase-merge", "rebase-apply")):
        return done(ST_FAIL, MSG_REBASE_PENDING)

    r = git(["symbolic-ref", "--short", "-q", "HEAD"])
    if (x := stopped(r)):
        return x
    if r.rc == 1:
        return done(ST_FAIL, MSG_DETACHED)
    if r.rc != 0:
        return failed(r)

    r = git(["rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"])
    if (x := stopped(r)):
        return x
    if r.rc != 0:
        return done(ST_FAIL, MSG_NO_UPSTREAM)

    r = git(["rev-parse", "-q", "--verify", "HEAD"])
    if (x := stopped(r)):
        return x
    old = r.out.strip() if r.rc == 0 else ""

    # 2. 拉取
    r = git(["pull", "--ff-only"] if ff_only else ["pull", "--no-rebase"], PULL_TIMEOUT)
    if (x := stopped(r)):
        return x
    if r.rc != 0:
        return failed(r)

    # 3. 判定
    r = git(["rev-parse", "-q", "--verify", "HEAD"])
    new = r.out.strip() if r.rc == 0 else ""
    if new == old:
        return done(ST_UPTODATE, "")
    r = git(["rev-list", "--count", f"{old}..{new}" if old else new])
    try:
        n = int(r.out.strip())
    except ValueError:
        n = 0
    return done(ST_UPDATED, f"+{n} 个提交" if n else "已更新")


def pull_many(items, ff_only, jobs, token, on_start=None, on_result=None):
    """items: [(key, Repo)]；回调在工作线程中调用。"""
    jobs = max(1, min(MAX_JOBS, int(jobs)))

    def one(key, repo):
        if token.cancelled:
            res = PullResult(ST_CANCEL, "已取消", "", 0.0)
        else:
            if on_start:
                on_start(key)
            try:
                res = pull_repo(repo, ff_only, token)
            except Exception:
                res = PullResult(ST_FAIL, "内部错误（详见详情）", traceback.format_exc(), 0.0)
        if on_result:
            on_result(key, res)

    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for key, repo in items:
            ex.submit(one, key, repo)


# ---------------------------------------------------------------------------
# 状态检查（只读工作区：git fetch 只更新远端跟踪分支，不动本地分支与工作区）
# ---------------------------------------------------------------------------

def parse_status_v2(text, info):
    """解析 `git status --porcelain=v2 --branch` 输出，填入 info。"""
    has_ab = False
    for ln in (text or "").splitlines():
        if ln.startswith("# branch.head "):
            head = ln[len("# branch.head "):].strip()
            info.detached = head == "(detached)"
            info.branch = DETACHED_LABEL if info.detached else head
        elif ln.startswith("# branch.upstream "):
            info.upstream = ln[len("# branch.upstream "):].strip()
        elif ln.startswith("# branch.ab "):
            has_ab = True
            for part in ln[len("# branch.ab "):].split():
                try:
                    if part.startswith("+"):
                        info.ahead = int(part[1:])
                    elif part.startswith("-"):
                        info.behind = int(part[1:])
                except ValueError:
                    pass
        elif ln.startswith(("1 ", "2 ")):
            info.changed += 1
        elif ln.startswith("u "):
            info.conflicts += 1
        elif ln.startswith("? "):
            info.untracked += 1
    # 配置了上游但远端跟踪分支不存在时，git 不输出 branch.ab
    info.upstream_gone = bool(info.upstream) and not has_ab
    return info


def check_repo(repo, fetch=True, token=None):
    token = token or CancelToken()
    info = SyncInfo()
    logs = []

    def git(args, timeout=CHECK_TIMEOUT):
        r = run_git(repo.path, args, timeout, token)
        logs.append(r.render())
        return r

    def status():
        # --no-optional-locks：不刷新 index，避免与用户同时进行的 git 操作争抢 index.lock
        return git(["--no-optional-locks", "status", "--porcelain=v2", "--branch"])

    def finish():
        info.detail = "\n\n".join(logs)
        info.checked_at = time.time()
        info.cancelled = token.cancelled
        return info

    r = status()
    if token.cancelled:
        return finish()
    if r.rc != 0 or r.timed_out:
        info.error = (f"命令执行超过 {r.timeout:.0f} 秒" if r.timed_out
                      else classify_error(r.text) or f"git 退出码 {r.rc}")
        return finish()
    parse_status_v2(r.out, info)

    # 只有设置了上游才有比较对象；不带参数的 fetch 取当前分支上游所在的 remote（与 pull 一致）
    if fetch and info.upstream:
        r = git(["-c", "gc.auto=0", "-c", "maintenance.auto=false", "fetch", "--quiet"],
                FETCH_TIMEOUT)
        if token.cancelled:
            return finish()
        if r.timed_out:
            info.fetch_error = f"获取远端超过 {r.timeout:.0f} 秒"
        elif r.rc != 0:
            info.fetch_error = classify_error(r.text) or f"git fetch 退出码 {r.rc}"
        else:
            info.fetched = True
            r = status()
            if token.cancelled:
                return finish()
            if r.rc == 0 and not r.timed_out:
                ok_info = SyncInfo()
                parse_status_v2(r.out, ok_info)
                for k in ("branch", "detached", "upstream", "upstream_gone", "ahead", "behind",
                          "changed", "untracked", "conflicts"):
                    setattr(info, k, getattr(ok_info, k))
    info.ok = True
    return finish()


def sync_parts(info):
    """把同步状态转成简短的中文片段列表；空列表表示已同步、无需处理。"""
    if info.error:
        return [f"检查失败：{info.error}"]
    parts = []
    if info.fetch_error:
        parts.append("远端获取失败")
    if info.detached:
        parts.append("游离 HEAD")
    elif not info.upstream:
        parts.append("无上游分支")
    elif info.upstream_gone:
        parts.append("上游分支已删除")
    if info.behind:
        parts.append(f"待拉取 {info.behind}")
    if info.ahead:
        parts.append(f"未推送 {info.ahead}")
    if info.conflicts:
        parts.append(f"冲突 {info.conflicts}")
    if info.changed:
        parts.append(f"未提交 {info.changed}")
    if info.untracked:
        parts.append(f"未跟踪 {info.untracked}")
    return parts


def sync_text(info):
    if info is None:
        return ""
    return " · ".join(sync_parts(info)) or "已同步"


def check_many(items, fetch, jobs, token, on_result=None):
    """items: [(key, Repo)]；回调在工作线程中调用。"""
    jobs = max(1, min(MAX_JOBS, int(jobs)))

    def one(key, repo):
        if token.cancelled:
            res = SyncInfo(cancelled=True)
        else:
            try:
                res = check_repo(repo, fetch, token)
            except Exception:
                res = SyncInfo(error="内部错误（详见详情）", detail=traceback.format_exc(),
                               checked_at=time.time())
        if on_result:
            on_result(key, res)

    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for key, repo in items:
            ex.submit(one, key, repo)


# ---------------------------------------------------------------------------
# 配置
# ---------------------------------------------------------------------------

DEFAULT_CONFIG = {
    "last_dir": "",
    "recent": [],
    "unchecked": {},
    "ff_only": True,
    "jobs": DEFAULT_JOBS,
    "check_minutes": DEFAULT_CHECK_MINUTES,
    "width": 1000,
    "height": 680,
}


def config_path():
    base = os.environ.get("APPDATA") or os.path.expanduser("~")
    return os.path.join(base, APP_NAME, "config.json")


def dir_key(path):
    return os.path.normcase(os.path.abspath(path))


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    try:
        with open(config_path(), encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            for k, default in DEFAULT_CONFIG.items():
                v = data.get(k)
                if isinstance(default, bool):
                    if isinstance(v, bool):
                        cfg[k] = v
                elif isinstance(v, type(default)) and not isinstance(v, bool):
                    cfg[k] = v
    except Exception:
        pass
    try:
        cfg["recent"] = [p for p in cfg["recent"] if isinstance(p, str) and os.path.isdir(p)][:MAX_RECENT]
        cfg["unchecked"] = {k: [n for n in v if isinstance(n, str)]
                            for k, v in cfg["unchecked"].items() if isinstance(v, list)}
        cfg["jobs"] = max(1, min(MAX_JOBS, cfg["jobs"]))
        if cfg["check_minutes"] not in CHECK_INTERVALS:
            cfg["check_minutes"] = DEFAULT_CHECK_MINUTES
        cfg["width"] = max(760, cfg["width"])
        cfg["height"] = max(480, cfg["height"])
    except Exception:
        cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    return cfg


def save_config(cfg):
    try:
        path = config_path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

def set_dpi_awareness():
    if os.name != "nt":
        return
    try:
        import ctypes
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


STATUS_TAG = {
    ST_UPDATED: "ok", ST_FAIL: "bad", ST_TIMEOUT: "bad", ST_RUN: "run",
    ST_CANCEL: "muted", ST_IDLE: "muted",
}


class App:
    def __init__(self, initial_dir=None):
        set_dpi_awareness()
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.cfg = load_config()
        self.scale = max(1.0, self.root.winfo_fpixels("1i") / 96.0)
        self.root.geometry(f"{self.px(self.cfg['width'])}x{self.px(self.cfg['height'])}")
        self.root.minsize(self.px(760), self.px(480))

        self.events = queue.Queue()
        self.rows = {}           # iid -> dict
        self.root_dir = None
        self.running = False
        self.scanning = False
        self.closing = False
        self.destroyed = False
        self.scan_gen = 0
        self.token = None
        self.run_total = 0
        self.run_done = 0
        self.run_t0 = 0.0
        self.menu_iid = None
        # 状态检查
        self.checking = False
        self.check_token = None
        self.check_gen = 0
        self.check_quiet = False
        self.check_after = None      # 自动检查定时器
        self.last_check = 0.0        # 上次检查结束的 monotonic 时间
        self.last_fetch = 0.0        # 最近一次含 fetch 的检查的开始时间（time.time）
        self.check_started = 0.0
        self.check_full = True
        self.check_iids = set()
        self.stale_after = None      # 重新勾选后的补查定时器
        self.pending_pull = None     # 检查进行中时点了拉取：(only,)，检查停止后再开始

        self._setup_style()
        self._build()
        self._update_controls()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.bind("<FocusIn>", self._on_focus, add="+")
        self.root.after(100, self._poll)

        start = initial_dir or self.cfg.get("last_dir") or ""
        if start and os.path.isdir(start):
            self.root.after(50, lambda: self.open_dir(start))
        elif initial_dir:
            self._set_status(f"目录不存在：{initial_dir}")
        else:
            self._set_status("请选择总项目文件夹")

    def px(self, v):
        return int(v * self.scale)

    # ---- 界面构建 ----
    def _setup_style(self):
        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(name).configure(family="Microsoft YaHei UI", size=9)
            except Exception:
                pass
        style = ttk.Style(self.root)
        if "vista" in style.theme_names():
            style.theme_use("vista")
        lh = tkfont.nametofont("TkDefaultFont").metrics("linespace")
        style.configure("Treeview", rowheight=int(lh * 1.6))

    def _build(self):
        root = self.root
        pad = self.px(6)

        top = ttk.Frame(root, padding=(pad, pad, pad, 2))
        top.pack(fill="x")
        ttk.Label(top, text="目录:").pack(side="left")
        self.dir_var = tk.StringVar()
        self.dir_box = ttk.Combobox(top, textvariable=self.dir_var, values=self.cfg["recent"])
        self.dir_box.pack(side="left", fill="x", expand=True, padx=4)
        self.dir_box.bind("<Return>", lambda e: self.open_dir(self.dir_var.get()))
        self.dir_box.bind("<<ComboboxSelected>>", lambda e: self.open_dir(self.dir_var.get()))
        self.btn_browse = ttk.Button(top, text="浏览…", command=self.browse)
        self.btn_browse.pack(side="left", padx=2)
        self.btn_rescan = ttk.Button(top, text="重新扫描", command=self.rescan)
        self.btn_rescan.pack(side="left", padx=2)
        self.btn_check = ttk.Button(top, text="检查状态", command=lambda: self.start_check(True))
        self.btn_check.pack(side="left", padx=2)

        bar = ttk.Frame(root, padding=(pad, 2, pad, 4))
        bar.pack(fill="x")
        self.sel_buttons = []
        for text, cmd in (("全选", self.check_all), ("全不选", self.check_none),
                          ("反选", self.check_invert), ("选中失败项", self.check_failed),
                          ("选中待拉取", self.check_behind)):
            b = ttk.Button(bar, text=text, command=cmd)
            b.pack(side="left", padx=(0, 4))
            self.sel_buttons.append(b)
        self.interval_labels = {m: (f"{m} 分钟" if m else "关闭") for m in CHECK_INTERVALS}
        self.interval_var = tk.StringVar(value=self.interval_labels[self.cfg["check_minutes"]])
        self.interval_box = ttk.Combobox(bar, textvariable=self.interval_var, width=7,
                                         state="readonly", values=list(self.interval_labels.values()))
        self.interval_box.bind("<<ComboboxSelected>>", self._on_interval)
        self.interval_box.pack(side="right")
        ttk.Label(bar, text="自动检查:").pack(side="right", padx=(12, 2))
        self.jobs_var = tk.StringVar(value=str(self.cfg["jobs"]))
        self.jobs_box = ttk.Combobox(bar, textvariable=self.jobs_var, width=3, state="readonly",
                                     values=[str(i) for i in range(1, MAX_JOBS + 1)])
        self.jobs_box.pack(side="right")
        ttk.Label(bar, text="并发:").pack(side="right", padx=(12, 2))
        self.ff_var = tk.BooleanVar(value=self.cfg["ff_only"])
        self.ff_check = ttk.Checkbutton(bar, text="仅快进（--ff-only）", variable=self.ff_var)
        self.ff_check.pack(side="right")

        # 底部（先 pack，保证缩小窗口时仍可见）
        sb = ttk.Frame(root, padding=(pad, 2, pad, pad))
        sb.pack(side="bottom", fill="x")
        self.sync_var = tk.StringVar()
        ttk.Label(sb, textvariable=self.sync_var, anchor="e").pack(side="right")
        self.status_var = tk.StringVar()
        ttk.Label(sb, textvariable=self.status_var, anchor="w").pack(side="left", fill="x", expand=True)
        act = ttk.Frame(root, padding=(pad, 4, pad, 2))
        act.pack(side="bottom", fill="x")
        self.btn_start = ttk.Button(act, text="开始拉取", command=self.start_pull)
        self.btn_start.pack(side="left")
        self.btn_stop = ttk.Button(act, text="停止", command=self.stop)
        self.btn_stop.pack(side="left", padx=4)
        self.progress = ttk.Progressbar(act, length=self.px(180), mode="determinate")
        self.progress.pack(side="left", padx=(8, 4))
        self.progress_var = tk.StringVar(value="")
        ttk.Label(act, textvariable=self.progress_var).pack(side="left")
        self.summary_var = tk.StringVar(value="")
        ttk.Label(act, textvariable=self.summary_var).pack(side="left", padx=12)
        self.btn_copy = ttk.Button(act, text="复制失败摘要", command=self.copy_failures)
        self.btn_copy.pack(side="right")

        paned = ttk.PanedWindow(root, orient="vertical")
        paned.pack(fill="both", expand=True, padx=pad)

        tf = ttk.Frame(paned)
        cols = ("check", "name", "branch", "sync", "status", "message", "time")
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", selectmode="extended")
        heads = {"check": "☑", "name": "项目", "branch": "分支", "sync": "本地/远端",
                 "status": "拉取状态", "message": "说明", "time": "耗时"}
        widths = {"check": 36, "name": 170, "branch": 100, "sync": 230, "status": 80,
                  "message": 300, "time": 60}
        left = ("name", "branch", "sync", "message")
        for c in cols:
            self.tree.heading(c, text=heads[c], anchor="w" if c in left else "center")
            self.tree.column(c, width=self.px(widths[c]),
                             stretch=(c == "message"),
                             anchor="w" if c in left else "center")
        self.tree.heading("check", command=self.toggle_all_heading)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.tag_configure("ok", foreground="#1a7f37")
        self.tree.tag_configure("bad", foreground="#cf222e")
        self.tree.tag_configure("run", foreground="#0969da")
        self.tree.tag_configure("muted", foreground="#808080")
        self.tree.tag_configure("warn", foreground="#bc4c00")
        self.tree.bind("<Button-1>", self._on_click)
        self.tree.bind("<Double-1>", self._on_double)
        self.tree.bind("<Button-3>", self._on_right_click)
        self.tree.bind("<space>", self._on_space)
        self.tree.bind("<<TreeviewSelect>>", lambda e: self._show_detail())
        paned.add(tf, weight=3)

        df = ttk.Frame(paned)
        self.detail = tk.Text(df, height=8, wrap="none", font=("Consolas", 10), undo=False)
        dsb = ttk.Scrollbar(df, orient="vertical", command=self.detail.yview)
        hsb = ttk.Scrollbar(df, orient="horizontal", command=self.detail.xview)
        self.detail.configure(yscrollcommand=dsb.set, xscrollcommand=hsb.set)
        hsb.pack(side="bottom", fill="x")
        self.detail.pack(side="left", fill="both", expand=True)
        dsb.pack(side="right", fill="y")
        self.detail.bind("<Key>", self._detail_key)
        for seq in ("<<Paste>>", "<<Cut>>", "<<Clear>>"):
            self.detail.bind(seq, lambda e: "break")
        paned.add(df, weight=1)

        self.menu = tk.Menu(root, tearoff=0)
        self.menu.add_command(label="打开目录", command=lambda: self._open_folder(self.menu_iid))
        self.menu.add_command(label="复制说明", command=lambda: self._copy_message(self.menu_iid))
        self.menu.add_command(label="仅重试此项", command=lambda: self.start_pull([self.menu_iid]))

    # ---- 状态 ----
    def _set_status(self, text):
        self.status_var.set(text)

    def _update_controls(self):
        busy = self.running or self.scanning
        has_rows = bool(self.rows)
        for w in [self.btn_browse, self.btn_rescan, self.dir_box, self.ff_check, self.jobs_box,
                  self.interval_box,
                  *self.sel_buttons]:
            w.state(["disabled"] if busy else ["!disabled"])
        self.btn_start.state(["!disabled"] if (not busy and has_rows) else ["disabled"])
        self.btn_stop.state(["!disabled"] if (self.running and not self.token.cancelled) else ["disabled"])
        self.btn_check.configure(text="检查中…" if self.checking else "检查状态")
        self.btn_check.state(["!disabled"] if (not busy and has_rows and not self.checking)
                             else ["disabled"])

    def _render_row(self, iid):
        r = self.rows[iid]
        secs = r["seconds"]
        t = f"{secs:.1f}s" if secs else ""
        sync = r["sync"]
        values = ("☑" if r["checked"] else "☐", r["repo"].name, r["repo"].branch,
                  sync_text(sync), r["status"], r["message"], t)
        tag = STATUS_TAG.get(r["status"])
        if r["status"] == ST_IDLE and r["checked"] and sync is not None:
            tag = "warn" if sync_parts(sync) else None
        # 未勾选：不再检查，整行置灰，保留上次结果仅供参考
        self.tree.item(iid, values=values, tags=(tag,) if tag else ())

    def _update_sync_summary(self):
        infos = [r["sync"] for r in self.rows.values() if r["checked"] and r["sync"] is not None]
        if self.checking:
            self.sync_var.set("正在检查本地/远端状态…")
            return
        if not infos:
            self.sync_var.set("")
            return
        cnt = lambda pred: sum(1 for i in infos if pred(i))
        parts = []
        for label, n in (("待拉取", cnt(lambda i: i.behind)),
                         ("未推送", cnt(lambda i: i.ahead)),
                         ("未提交", cnt(lambda i: i.changed or i.untracked or i.conflicts)),
                         ("检查/获取失败", cnt(lambda i: i.error or i.fetch_error))):
            if n:
                parts.append(f"{label} {n} 个")
        head = "，".join(parts) if parts else "全部已同步"
        last = max(i.checked_at for i in infos)
        self.sync_var.set(f"{head}（检查于 {time.strftime('%H:%M', time.localtime(last))}）")

    def _update_summary(self):
        cnt = {}
        for r in self.rows.values():
            cnt[r["status"]] = cnt.get(r["status"], 0) + 1
        parts = [f"已更新 {cnt.get(ST_UPDATED, 0)}", f"已是最新 {cnt.get(ST_UPTODATE, 0)}",
                 f"失败 {cnt.get(ST_FAIL, 0)}"]
        if cnt.get(ST_TIMEOUT):
            parts.append(f"超时 {cnt[ST_TIMEOUT]}")
        if cnt.get(ST_CANCEL):
            parts.append(f"已取消 {cnt[ST_CANCEL]}")
        self.summary_var.set("  ".join(parts) if self.run_total else "")
        self.progress.configure(maximum=max(1, self.run_total), value=self.run_done)
        self.progress_var.set(f"{self.run_done}/{self.run_total}" if self.run_total else "")

    # ---- 目录 ----
    def browse(self):
        if self.running or self.scanning:
            return
        init = self.root_dir or self.dir_var.get() or os.path.expanduser("~")
        path = filedialog.askdirectory(parent=self.root, initialdir=init, title="选择总项目文件夹")
        if path:
            self.open_dir(path)

    def rescan(self):
        self.open_dir(self.dir_var.get() or self.root_dir or "")

    def open_dir(self, path):
        if self.running or self.scanning:
            return
        path = (path or "").strip().strip('"').strip()
        if not path:
            self._set_status("请选择总项目文件夹")
            return
        path = os.path.abspath(os.path.expanduser(path))
        if not os.path.isdir(path):
            self._set_status(f"目录不存在：{path}")
            return
        self._save_checks()
        self._abandon_check()
        self.root_dir = path
        self.dir_var.set(path)
        # 目录名放最前：任务栏会截断长标题，多开时靠它区分；同名目录再靠完整路径区分
        name = os.path.basename(path.rstrip("\\/")) or path
        self.root.title(f"{name} - {APP_NAME} - {path}")
        self._remember_dir(path)
        self.tree.delete(*self.tree.get_children())
        self.rows.clear()
        self.run_total = self.run_done = 0
        self._update_summary()
        self._update_sync_summary()
        self._show_detail()
        self.scanning = True
        self._update_controls()
        self._set_status(f"正在扫描 {path} …")
        self.scan_gen += 1
        threading.Thread(target=self._scan_worker, args=(self.scan_gen, path), daemon=True).start()

    def _scan_worker(self, gen, path):
        try:
            self.events.put(("scan_done", gen, scan_dir(path)))
        except ScanError as e:
            self.events.put(("scan_error", gen, str(e)))
        except Exception as e:
            self.events.put(("scan_error", gen, f"扫描失败：{type(e).__name__}: {e}"))

    def _remember_dir(self, path):
        key = dir_key(path)
        recent = [path] + [p for p in self.cfg["recent"] if dir_key(p) != key]
        self.cfg["recent"] = recent[:MAX_RECENT]
        self.cfg["last_dir"] = path
        self.dir_box.configure(values=self.cfg["recent"])

    def _save_checks(self):
        if not self.root_dir or not self.rows:
            return
        key = dir_key(self.root_dir)
        names = sorted(r["repo"].name for r in self.rows.values() if not r["checked"])
        if names:
            self.cfg["unchecked"][key] = names
        else:
            self.cfg["unchecked"].pop(key, None)

    def _on_scan_done(self, res):
        unchecked = set(self.cfg["unchecked"].get(dir_key(self.root_dir), []))
        for i, repo in enumerate(res.repos):
            iid = f"r{i}"
            self.rows[iid] = {"repo": repo, "checked": repo.name not in unchecked,
                              "status": ST_IDLE, "message": "", "detail": "",
                              "seconds": None, "order": i, "sync": None}
            self.tree.insert("", "end", iid=iid)
            self._render_row(iid)
        parts = []
        if res.repos:
            parts.append(f"共 {len(res.repos)} 个仓库")
        else:
            parts.append("该目录下没有找到 git 仓库")
        if res.root_is_repo:
            parts.append("该目录本身是一个仓库，已作为第一项列出")
        if res.ignored:
            parts.append(f"已忽略 {res.ignored} 个非 git 目录")
        self._set_status("；".join(parts))
        if res.repos:
            self.tree.selection_set("r0")
            self.tree.focus("r0")
            self.start_check(True, quiet=True)  # 结果汇总在右下角，左侧保留扫描提示

    # ---- 勾选 ----
    def _set_checked(self, iids, value_fn):
        if self.running or self.scanning:
            return
        for iid in iids:
            if iid in self.rows:
                self.rows[iid]["checked"] = value_fn(self.rows[iid])
                self._render_row(iid)
        self._update_sync_summary()
        if self._stale_checked():
            self._schedule_stale_check()

    def check_all(self):
        self._set_checked(list(self.rows), lambda r: True)

    def check_none(self):
        self._set_checked(list(self.rows), lambda r: False)

    def check_invert(self):
        self._set_checked(list(self.rows), lambda r: not r["checked"])

    def check_failed(self):
        if not any(r["status"] in BAD_STATUSES for r in self.rows.values()):
            self._set_status("没有失败项")
            return
        self._set_checked(list(self.rows), lambda r: r["status"] in BAD_STATUSES)

    def check_behind(self):
        behind = lambda r: bool(r["sync"] and r["sync"].behind)
        if not any(behind(r) for r in self.rows.values()):
            self._set_status("没有待拉取的仓库（以最近一次状态检查为准）")
            return
        self._set_checked(list(self.rows), behind)

    def toggle_all_heading(self):
        if all(r["checked"] for r in self.rows.values()):
            self.check_none()
        else:
            self.check_all()

    def _on_click(self, e):
        if (self.tree.identify_region(e.x, e.y) == "cell"
                and self.tree.identify_column(e.x) == "#1"):
            iid = self.tree.identify_row(e.y)
            if iid:
                self._set_checked([iid], lambda r: not r["checked"])

    def _on_double(self, e):
        iid = self.tree.identify_row(e.y)
        if not iid:
            return
        if self.tree.identify_column(e.x) == "#1":
            self._set_checked([iid], lambda r: not r["checked"])
            return "break"
        self._open_folder(iid)
        return "break"

    def _on_space(self, e):
        self._set_checked(list(self.tree.selection()), lambda r: not r["checked"])
        return "break"

    def _on_right_click(self, e):
        iid = self.tree.identify_row(e.y)
        if not iid:
            return
        if iid not in self.tree.selection():
            self.tree.selection_set(iid)
        self.tree.focus(iid)
        self.menu_iid = iid
        busy = self.running or self.scanning
        self.menu.entryconfigure(2, state="disabled" if busy else "normal")
        try:
            self.menu.tk_popup(e.x_root, e.y_root)
        finally:
            self.menu.grab_release()

    def _open_folder(self, iid):
        if iid in self.rows:
            try:
                os.startfile(self.rows[iid]["repo"].path)
            except Exception as ex:
                self._set_status(f"无法打开目录：{ex}")

    def _copy_message(self, iid):
        if iid in self.rows:
            r = self.rows[iid]
            text = f"{r['repo'].name} [{r['repo'].branch}]: {r['status']} {r['message']}".rstrip()
            if r["sync"] is not None:
                text += f"（本地/远端：{sync_text(r['sync'])}）"
            self._to_clipboard(text)
            self._set_status("已复制到剪贴板")

    def _to_clipboard(self, text):
        self.root.clipboard_clear()
        self.root.clipboard_append(text)

    # ---- 详情 ----
    def _detail_key(self, e):
        ctrl = bool(e.state & 0x4)
        key = e.keysym.lower()
        if ctrl and key == "a":
            self.detail.tag_add("sel", "1.0", "end")
            return "break"
        if ctrl and key in ("c", "insert"):
            return None
        if e.keysym in ("Left", "Right", "Up", "Down", "Home", "End", "Prior", "Next"):
            return None
        return "break"

    def _show_detail(self):
        sel = self.tree.selection()
        text = ""
        if sel and sel[0] in self.rows:
            r = self.rows[sel[0]]
            repo = r["repo"]
            sync = r["sync"]
            lines = [f"项目：{repo.name}", f"路径：{repo.path}", f"分支：{repo.branch}"]
            if sync is not None:
                when = time.strftime("%H:%M:%S", time.localtime(sync.checked_at))
                how = "已获取远端" if sync.fetched else "仅本地，未获取远端"
                lines.append(f"本地/远端：{sync_text(sync)}（检查于 {when}，{how}）")
                if not r["checked"]:
                    lines.append("（未勾选，已暂停检查；以上为勾选时的最后结果）")
                if sync.upstream:
                    lines.append(f"上游分支：{sync.upstream}")
                if sync.fetch_error:
                    lines.append(f"远端获取失败：{sync.fetch_error}（「待拉取」为上次获取时的结果）")
            lines.append(f"拉取状态：{r['status']}")
            if r["message"]:
                lines.append(f"说明：{r['message']}")
            if r["seconds"]:
                lines.append(f"耗时：{r['seconds']:.1f}s")
            lines.append("")
            lines.append(r["detail"] or "（尚无拉取输出）")
            if sync is not None and sync.detail:
                lines += ["", "—— 最近一次状态检查 ——", sync.detail]
            text = "\n".join(lines)
        self.detail.delete("1.0", "end")
        self.detail.insert("1.0", text)

    # ---- 执行 ----
    def start_pull(self, only=None):
        if self.running or self.scanning:
            return
        if self.checking:
            # 后台 fetch 与 pull 同时写同一仓库会争抢引用锁：先停检查，检查线程结束后再拉取
            self.pending_pull = (only,)
            self.check_token.cancel()
            self._set_status("正在停止状态检查，随后开始拉取…")
            return
        if only is None:
            targets = [iid for iid in self.tree.get_children() if self.rows[iid]["checked"]]
        else:
            targets = [iid for iid in only if iid in self.rows]
        if not targets:
            self._set_status("请先勾选要拉取的仓库")
            return
        try:
            jobs = max(1, min(MAX_JOBS, int(self.jobs_var.get())))
        except ValueError:
            jobs = DEFAULT_JOBS
        ff_only = bool(self.ff_var.get())
        self.cfg["jobs"] = jobs
        self.cfg["ff_only"] = ff_only
        self._save_checks()
        save_config(self.cfg)

        target_set = set(targets)
        for iid, r in self.rows.items():
            if iid in target_set:
                r.update(status=ST_WAIT, message="", detail="", seconds=None)
            elif only is None:
                r.update(status=ST_IDLE, message="", detail="", seconds=None)
            else:
                continue
            self._render_row(iid)

        self.token = CancelToken()
        self.running = True
        self.run_total = len(targets)
        self.run_done = 0
        self.run_t0 = time.monotonic()
        self.btn_stop.configure(text="停止")
        self._update_controls()
        self._update_summary()
        self._show_detail()
        mode = "仅快进" if ff_only else "合并"
        self._set_status(f"正在拉取 {len(targets)} 个仓库（{mode}，并发 {jobs}）…")
        items = [(iid, self.rows[iid]["repo"]) for iid in targets]
        threading.Thread(target=self._run_worker, args=(items, ff_only, jobs, self.token),
                         daemon=True).start()

    def _run_worker(self, items, ff_only, jobs, token):
        try:
            pull_many(items, ff_only, jobs, token,
                      on_start=lambda k: self.events.put(("start", k)),
                      on_result=lambda k, res: self.events.put(("result", k, res)))
        except Exception:
            self.events.put(("error", traceback.format_exc()))
        finally:
            self.events.put(("run_done",))

    def stop(self):
        if not self.running or self.token is None or self.token.cancelled:
            return
        self.token.cancel()
        self.btn_stop.configure(text="正在停止…")
        self._update_controls()
        self._set_status("正在停止…")

    def _on_run_done(self):
        self.running = False
        bad = lambda iid: 0 if self.rows[iid]["status"] in BAD_STATUSES else 1
        order = sorted(self.rows, key=lambda iid: (bad(iid), self.rows[iid]["order"]))
        for idx, iid in enumerate(order):
            self.tree.move(iid, "", idx)
        elapsed = time.monotonic() - self.run_t0
        stopped = self.token is not None and self.token.cancelled
        self.btn_stop.configure(text="停止")
        self._update_controls()
        self._update_summary()
        nbad = sum(1 for r in self.rows.values() if r["status"] in BAD_STATUSES)
        head = "已停止" if stopped else "完成"
        tail = f"，{nbad} 个失败项已置顶" if nbad else ""
        self._set_status(f"{head}：共 {self.run_total} 项，用时 {elapsed:.1f}s{tail}")
        if self.closing:
            self._destroy()
            return
        # pull 已获取过远端，这里只刷新本地状态
        self.start_check(False, quiet=True)

    # ---- 状态检查 ----
    def _jobs(self):
        try:
            return max(1, min(MAX_JOBS, int(self.jobs_var.get())))
        except ValueError:
            return DEFAULT_JOBS

    def start_check(self, fetch=True, quiet=False, only=None):
        """只检查已勾选的仓库（未勾选的不 fetch、不看状态）。
        fetch=True：先获取远端再看状态；quiet=True：完成后不改左侧状态栏；
        only：只检查其中这些行（重新勾选后补查）。返回是否已启动。"""
        if self.running or self.scanning or self.checking or self.destroyed:
            return False
        iids = [iid for iid, r in self.rows.items()
                if r["checked"] and (only is None or iid in only)]
        if not iids:
            return False
        self.checking = True
        self.check_quiet = quiet
        self.check_full = only is None
        self.check_started = time.time()
        self.check_token = CancelToken()
        self.check_gen += 1
        self._update_controls()
        self._update_sync_summary()
        self.check_iids = set(iids)
        items = [(iid, self.rows[iid]["repo"]) for iid in iids]
        threading.Thread(target=self._check_worker,
                         args=(self.check_gen, items, fetch, self._jobs(), self.check_token),
                         daemon=True).start()
        return True

    def _check_worker(self, gen, items, fetch, jobs, token):
        try:
            check_many(items, fetch, jobs, token,
                       on_result=lambda k, res: self.events.put(("check_result", gen, k, res)))
        except Exception:
            pass
        finally:
            self.events.put(("check_done", gen, fetch))

    def _abandon_check(self):
        """切换目录时丢弃进行中的检查（旧结果按代号忽略）。"""
        if self.checking:
            self.check_token.cancel()
            self.check_gen += 1
            self.checking = False
        self.pending_pull = None

    def _on_check_result(self, iid, res):
        if iid not in self.rows or res.cancelled:
            return
        r = self.rows[iid]
        r["sync"] = res
        if res.ok and res.branch and res.branch != r["repo"].branch:
            r["repo"] = Repo(r["repo"].name, r["repo"].path, res.branch)  # 用户在别处切了分支
        self._render_row(iid)
        if iid in self.tree.selection():
            self._show_detail()

    def _on_check_done(self, fetch):
        self.checking = False
        self.last_check = time.monotonic()
        cancelled = self.check_token is not None and self.check_token.cancelled
        self._update_controls()
        self._update_sync_summary()
        if self.pending_pull is not None:
            (only,) = self.pending_pull
            self.pending_pull = None
            self.start_pull(only)
            return
        if fetch and not cancelled and self.check_full:
            # 只有全量检查才推进基准时间；补查若也推进，会把其他行判成过期而循环重查
            self.last_fetch = self.check_started
            self._schedule_auto_check()
        if not self.check_quiet and not cancelled:
            self._set_status(f"状态检查完成：{self.sync_var.get()}")
        if not cancelled:
            self._check_stale(exclude=self.check_iids)  # 检查期间新勾选的仓库

    def _stale_checked(self):
        """已勾选、但从没检查过或上次结果早于最近一次获取远端的行。"""
        return [iid for iid, r in self.rows.items() if r["checked"] and
                (r["sync"] is None or r["sync"].checked_at < self.last_fetch)]

    def _schedule_stale_check(self):
        # 防抖：连续点「全选」/勾选多行时合并成一次检查
        if self.stale_after is not None:
            self.root.after_cancel(self.stale_after)
        self.stale_after = self.root.after(600, self._check_stale)

    def _check_stale(self, exclude=()):
        self.stale_after = None
        # exclude：刚查过的行即使结果异常也不立刻重查，避免循环
        stale = [iid for iid in self._stale_checked() if iid not in exclude]
        if stale:
            # 正在检查时会在 _on_check_done 里再调用一次
            self.start_check(True, quiet=True, only=set(stale))

    def _schedule_auto_check(self, delay_ms=None):
        if self.check_after is not None:
            self.root.after_cancel(self.check_after)
            self.check_after = None
        minutes = self.cfg["check_minutes"]
        if minutes and not self.destroyed:
            self.check_after = self.root.after(delay_ms or minutes * 60_000, self._auto_check)

    def _auto_check(self):
        self.check_after = None
        if self.start_check(True, quiet=True):
            return
        busy = self.running or self.scanning or self.checking
        self._schedule_auto_check(60_000 if busy else None)  # 正忙则 1 分钟后再试

    def _on_interval(self, _e=None):
        label = self.interval_var.get()
        minutes = next((m for m, s in self.interval_labels.items() if s == label),
                       DEFAULT_CHECK_MINUTES)
        self.cfg["check_minutes"] = minutes
        save_config(self.cfg)
        self._schedule_auto_check()
        self._set_status(f"自动检查：每 {minutes} 分钟获取一次远端" if minutes else "已关闭自动检查")

    def _on_focus(self, _e=None):
        # 用户可能刚在别处提交/推送过，切回窗口时刷新本地状态（不访问网络）
        if self.rows and time.monotonic() - self.last_check > FOCUS_RECHECK_SECONDS:
            self.start_check(False, quiet=True)

    def copy_failures(self):
        blocks = []
        for iid in self.tree.get_children():
            r = self.rows[iid]
            if r["status"] not in BAD_STATUSES:
                continue
            lines = [f"{r['repo'].name} [{r['repo'].branch}]: {r['status']} - {r['message']}"]
            tail = [ln for ln in r["detail"].splitlines() if ln.strip()][-5:]
            lines += ["    " + ln for ln in tail]
            blocks.append("\n".join(lines))
        if not blocks:
            self._set_status("没有失败项")
            return
        self._to_clipboard("\n\n".join(blocks))
        self._set_status(f"已复制 {len(blocks)} 个失败项到剪贴板")

    # ---- 事件循环 ----
    def _poll(self):
        if self.destroyed:
            return
        try:
            while True:
                ev = self.events.get_nowait()
                try:
                    self._handle(ev)
                except Exception as ex:
                    self._set_status(f"界面更新出错：{type(ex).__name__}: {ex}")
        except queue.Empty:
            pass
        if not self.destroyed:
            self.root.after(100, self._poll)

    def _handle(self, ev):
        kind = ev[0]
        if kind in ("scan_done", "scan_error"):
            if ev[1] != self.scan_gen:
                return
            self.scanning = False
            if kind == "scan_done":
                self._on_scan_done(ev[2])
            else:
                self._set_status(ev[2])
            self._update_controls()
        elif kind == "start":
            if ev[1] in self.rows:
                self.rows[ev[1]]["status"] = ST_RUN
                self._render_row(ev[1])
        elif kind == "result":
            iid, res = ev[1], ev[2]
            if iid in self.rows:
                self.rows[iid].update(status=res.status, message=res.message,
                                      detail=res.detail, seconds=res.seconds)
                self._render_row(iid)
                if iid in self.tree.selection():
                    self._show_detail()
            self.run_done += 1
            self._update_summary()
        elif kind == "error":
            self._set_status("执行出错，详见详情区")
            self.detail.delete("1.0", "end")
            self.detail.insert("1.0", ev[1])
        elif kind == "run_done":
            self._on_run_done()
        elif kind == "check_result":
            if ev[1] == self.check_gen:
                self._on_check_result(ev[2], ev[3])
        elif kind == "check_done":
            if ev[1] == self.check_gen:
                self._on_check_done(ev[2])

    def on_close(self):
        if self.running:
            if not messagebox.askyesno(APP_NAME, "正在拉取，确定停止并退出吗？", parent=self.root):
                return
            self.closing = True
            self.stop()
            self.root.after(5000, self._destroy)  # 兜底
            return
        self._destroy()

    def _destroy(self):
        if self.destroyed:
            return
        if self.check_token is not None:
            self.check_token.cancel()
        try:
            self._save_checks()
            self.cfg["width"] = int(self.root.winfo_width() / self.scale)
            self.cfg["height"] = int(self.root.winfo_height() / self.scale)
            self.cfg["ff_only"] = bool(self.ff_var.get())
            save_config(self.cfg)
        except Exception:
            pass
        self.destroyed = True
        self.root.destroy()

    def run(self):
        self.root.mainloop()


def run_gui(initial_dir=None):
    if tk is None:
        out("未找到 tkinter，无法启动图形界面；可使用 --cli 模式。")
        return 2
    App(initial_dir).run()
    return 0


# ---------------------------------------------------------------------------
# 命令行
# ---------------------------------------------------------------------------

def out(msg=""):
    s = sys.stdout
    if s is None:  # pythonw 下没有控制台
        return
    try:
        s.write(msg + "\n")
        s.flush()
    except Exception:
        pass


def setup_console():
    if os.environ.get("PYTHONIOENCODING"):
        return
    for s in (sys.stdout, sys.stderr):
        try:
            if s is not None:
                s.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass


def run_cli(argv):
    setup_console()
    p = argparse.ArgumentParser(prog="batch_git_pull.pyw --cli",
                                description="批量对目录下第一层的 git 仓库执行 git pull")
    p.add_argument("root", help="总项目文件夹")
    p.add_argument("--only", help="只拉取指定仓库，逗号分隔")
    p.add_argument("--merge", action="store_true", help="允许合并（默认仅快进 --ff-only）")
    p.add_argument("--jobs", type=int, default=DEFAULT_JOBS, help=f"并发数 1-{MAX_JOBS}")
    p.add_argument("--status", action="store_true",
                   help="不拉取，只检查状态（git fetch 后比较：待拉取/未推送/未提交）")
    ns = p.parse_args(argv)

    try:
        res = scan_dir(ns.root)
    except ScanError as e:
        out(f"错误：{e}")
        return 2
    repos = res.repos
    if ns.only:
        wanted = {n.strip().lower() for n in ns.only.split(",") if n.strip()}
        missing = wanted - {r.name.lower() for r in repos}
        if missing:
            out(f"警告：未找到这些仓库：{', '.join(sorted(missing))}")
        repos = [r for r in repos if r.name.lower() in wanted]
        if not repos:
            return 2
    if not repos:
        out(f"{os.path.abspath(ns.root)} 下没有找到 git 仓库")
        return 0

    jobs = max(1, min(MAX_JOBS, ns.jobs))
    if ns.status:
        return _cli_status(ns.root, repos, jobs)
    ff_only = not ns.merge
    out(f"目录：{os.path.abspath(ns.root)}  仓库：{len(repos)}  "
        f"模式：{'仅快进' if ff_only else '合并'}  并发：{jobs}")
    token = CancelToken()
    results = {}
    lock = threading.Lock()

    def on_result(repo, r):
        with lock:
            results[repo] = r
            msg = f"  {r.message}" if r.message else ""
            out(f"{r.status}\t{repo.name} [{repo.branch}]{msg}  ({r.seconds:.1f}s)")

    t0 = time.monotonic()
    t = threading.Thread(target=pull_many, args=([(r, r) for r in repos], ff_only, jobs, token),
                         kwargs={"on_result": on_result}, daemon=True)
    t.start()
    try:
        while t.is_alive():
            t.join(0.2)
    except KeyboardInterrupt:
        out("正在停止…")
        token.cancel()
        t.join()

    cnt = {}
    for r in results.values():
        cnt[r.status] = cnt.get(r.status, 0) + 1
    out("")
    out(f"汇总：已更新 {cnt.get(ST_UPDATED, 0)}，已是最新 {cnt.get(ST_UPTODATE, 0)}，"
        f"失败 {cnt.get(ST_FAIL, 0)}，超时 {cnt.get(ST_TIMEOUT, 0)}，已取消 {cnt.get(ST_CANCEL, 0)}，"
        f"用时 {time.monotonic() - t0:.1f}s")
    bad = [(repo, r) for repo, r in results.items() if r.status not in (ST_UPDATED, ST_UPTODATE)]
    for repo, r in sorted(bad, key=lambda x: x[0].name.lower()):
        out(f"\n[{r.status}] {repo.name} [{repo.branch}]: {r.message}")
        for ln in [ln for ln in r.detail.splitlines() if ln.strip()][-5:]:
            out("    " + ln)
    return 1 if bad else 0


def _cli_status(root, repos, jobs):
    """逐行打印 `状态  项目 [分支]`；有检查失败或远端获取失败时退出码 1。"""
    out(f"目录：{os.path.abspath(root)}  仓库：{len(repos)}  检查状态（含 git fetch）  并发：{jobs}")
    results = {}
    check_many([(r, r) for r in repos], True, jobs, CancelToken(),
               on_result=lambda repo, info: results.__setitem__(repo, info))
    for repo in repos:
        info = results.get(repo) or SyncInfo(error="未执行")
        out(f"{sync_text(info)}\t{repo.name} [{info.branch or repo.branch}]")
        if info.error or info.fetch_error:
            out(f"    {info.error or info.fetch_error}")
    return 1 if any(i.error or i.fetch_error for i in results.values()) else 0


# ---------------------------------------------------------------------------
# 自测（本地 bare 仓库，不访问网络，不触碰用户目录）
# ---------------------------------------------------------------------------

def _rmtree(path):
    def fix(func, p, *_):
        try:
            os.chmod(p, 0o700)
            func(p)
        except Exception:
            pass
    if sys.version_info >= (3, 12):
        shutil.rmtree(path, onexc=fix)
    else:
        shutil.rmtree(path, onerror=fix)


def run_selftest():
    setup_console()
    passed = 0
    failed = []

    def check(name, cond, info=""):
        nonlocal passed
        if cond:
            passed += 1
            out(f"  PASS  {name}")
        else:
            failed.append(name)
            out(f"  FAIL  {name}  {info}")

    out("== classify_error / redact ==")
    for keywords, msg in ERROR_RULES:
        for kw in keywords:
            got = classify_error(f"From somewhere\n{kw} blah\n")
            check(f"classify: {kw}", got == msg, repr(got))
    check("classify: fallback fatal", classify_error("hint: x\nfatal: something odd\nhint: y") ==
          "fatal: something odd")
    check("classify: fallback last line", classify_error("a\n  last line  \n") == "last line")
    check("classify: empty", classify_error("") == "")
    red = redact("fatal: unable to access 'https://u:p@h/x.git/' and ssh://git@h2/y")
    check("redact", "u:p" not in red and "https://***@h/x.git" in red and "git@" not in red, red)

    tmp = tempfile.mkdtemp(prefix="bgp_selftest_")
    saved = {k: os.environ.get(k) for k in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_NOSYSTEM")}
    try:
        gcfg = os.path.join(tmp, "gitconfig")
        with open(gcfg, "w", encoding="utf-8", newline="\n") as f:
            f.write("[user]\n\tname = selftest\n\temail = selftest@example.invalid\n"
                    "[init]\n\tdefaultBranch = main\n[core]\n\tautocrlf = false\n")
        os.environ["GIT_CONFIG_GLOBAL"] = gcfg
        os.environ["GIT_CONFIG_NOSYSTEM"] = "1"
        work = os.path.join(tmp, "work")
        os.makedirs(work)

        def g(cwd, *args):
            r = subprocess.run(["git", *args], cwd=cwd, stdin=subprocess.DEVNULL,
                               capture_output=True, env=git_env(),
                               creationflags=CREATE_NO_WINDOW, timeout=60)
            if r.returncode != 0:
                raise RuntimeError(f"git {' '.join(args)} 失败：{_decode(r.stderr)}")
            return _decode(r.stdout).strip()

        def write(path, content):
            with open(path, "w", encoding="utf-8", newline="\n") as f:
                f.write(content)

        def read(path):
            with open(path, encoding="utf-8") as f:
                return f.read()

        def new_remote(tag):
            bare = os.path.join(tmp, "remotes", tag + ".git")
            os.makedirs(bare)
            g(bare, "init", "-q", "--bare", "-b", "main")
            seed = os.path.join(tmp, "seeds", tag)
            os.makedirs(os.path.dirname(seed), exist_ok=True)
            g(tmp, "clone", "-q", bare, seed)
            g(seed, "checkout", "-q", "-b", "main")
            write(os.path.join(seed, "a.txt"), "a1\n")
            write(os.path.join(seed, "b.txt"), "b1\n")
            g(seed, "add", "-A")
            g(seed, "commit", "-q", "-m", "init")
            g(seed, "push", "-q", "-u", "origin", "main")
            return bare, seed

        def push_change(seed, fname, content):
            write(os.path.join(seed, fname), content)
            g(seed, "add", "-A")
            g(seed, "commit", "-q", "-m", f"change {fname}")
            g(seed, "push", "-q", "origin", "main")

        def clone(bare, name):
            dst = os.path.join(work, name)
            g(work, "clone", "-q", bare, dst)
            return dst

        def repo_of(path, name):
            return Repo(name, path, read_branch(path))

        def head(path):
            return g(path, "rev-parse", "HEAD")

        out("\n== 拉取场景 ==")
        # 已是最新
        bare, seed = new_remote("uptodate")
        p = clone(bare, "uptodate")
        r = pull_repo(repo_of(p, "uptodate"))
        check("已是最新", r.status == ST_UPTODATE, f"{r.status} {r.message}")

        # 落后远端
        bare, seed = new_remote("behind")
        p = clone(bare, "behind")
        push_change(seed, "a.txt", "a2\n")
        push_change(seed, "a.txt", "a3\n")
        r = pull_repo(repo_of(p, "behind"))
        check("落后远端 -> 已更新 +2", r.status == ST_UPDATED and "+2" in r.message,
              f"{r.status} {r.message}")

        # 脏工作区冲突
        bare, seed = new_remote("dirty_conflict")
        p = clone(bare, "dirty_conflict")
        push_change(seed, "a.txt", "remote\n")
        write(os.path.join(p, "a.txt"), "local\n")
        r = pull_repo(repo_of(p, "dirty_conflict"))
        check("脏工作区冲突 -> 失败", r.status == ST_FAIL and r.message.startswith("本地有未提交的修改"),
              f"{r.status} {r.message}")
        check("脏工作区冲突 -> 本地修改保留", read(os.path.join(p, "a.txt")) == "local\n")

        # 脏工作区不冲突
        bare, seed = new_remote("dirty_ok")
        p = clone(bare, "dirty_ok")
        push_change(seed, "a.txt", "remote\n")
        write(os.path.join(p, "b.txt"), "local b\n")
        r = pull_repo(repo_of(p, "dirty_ok"))
        check("脏工作区不冲突 -> 已更新", r.status == ST_UPDATED, f"{r.status} {r.message}")
        check("脏工作区不冲突 -> b.txt 保留", read(os.path.join(p, "b.txt")) == "local b\n")

        # 分叉
        bare, seed = new_remote("diverged")
        p = clone(bare, "diverged")
        push_change(seed, "a.txt", "remote\n")
        write(os.path.join(p, "b.txt"), "local commit\n")
        g(p, "commit", "-q", "-am", "local")
        before = head(p)
        r = pull_repo(repo_of(p, "diverged"), ff_only=True)
        check("分叉 -> 失败", r.status == ST_FAIL and "已分叉" in r.message, f"{r.status} {r.message}")
        check("分叉 -> HEAD 未变", head(p) == before)

        # 无上游
        bare, seed = new_remote("noupstream")
        p = clone(bare, "noupstream")
        g(p, "checkout", "-q", "-b", "feature")
        r = pull_repo(repo_of(p, "noupstream"))
        check("无上游 -> 失败", r.status == ST_FAIL and "未设置上游分支" in r.message,
              f"{r.status} {r.message}")

        # 游离 HEAD
        bare, seed = new_remote("detached")
        p = clone(bare, "detached")
        g(p, "checkout", "-q", "--detach")
        rp = repo_of(p, "detached")
        check("游离 HEAD -> 分支显示", rp.branch == DETACHED_LABEL, rp.branch)
        r = pull_repo(rp)
        check("游离 HEAD -> 失败", r.status == ST_FAIL and "游离 HEAD" in r.message,
              f"{r.status} {r.message}")

        # 远端不可达
        bare, seed = new_remote("unreachable")
        p = clone(bare, "unreachable")
        g(p, "remote", "set-url", "origin", "http://127.0.0.1:9/x.git")
        t0 = time.monotonic()
        r = pull_repo(repo_of(p, "unreachable"))
        el = time.monotonic() - t0
        check("远端不可达 -> 网络错误", r.status == ST_FAIL and r.message.startswith("网络错误"),
              f"{r.status} {r.message}")
        check("远端不可达 -> 30 秒内返回", el < 30, f"{el:.1f}s")

        # 特殊目录名
        bare, seed = new_remote("cjk")
        p = clone(bare, "中文 项目")
        push_change(seed, "a.txt", "remote\n")
        r = pull_repo(repo_of(p, "中文 项目"))
        check("中文与空格目录名 -> 已更新", r.status == ST_UPDATED, f"{r.status} {r.message}")

        # remote 非 origin
        bare, seed = new_remote("renamed")
        p = clone(bare, "renamed")
        g(p, "remote", "rename", "origin", "upstream")
        push_change(seed, "a.txt", "remote\n")
        r = pull_repo(repo_of(p, "renamed"))
        check("remote 非 origin -> 已更新", r.status == ST_UPDATED, f"{r.status} {r.message}")

        # 取消
        tok = CancelToken()
        tok.cancel()
        r = pull_repo(repo_of(os.path.join(work, "uptodate"), "uptodate"), True, tok)
        check("已取消的令牌 -> 已取消", r.status == ST_CANCEL, r.status)

        out("\n== 状态检查 ==")
        sp = parse_status_v2("# branch.oid abc\n# branch.head dev\n# branch.upstream origin/dev\n"
                             "# branch.ab +2 -3\n1 .M N... 100644 100644 100644 a a a.txt\n"
                             "2 R. N... 100644 100644 100644 a a R100 n.txt\to.txt\n"
                             "u UU N... 1 1 1 1 a a a c.txt\n? new.txt\n", SyncInfo())
        check("parse_status_v2", (sp.branch, sp.upstream, sp.ahead, sp.behind, sp.changed,
                                  sp.conflicts, sp.untracked, sp.upstream_gone) ==
              ("dev", "origin/dev", 2, 3, 2, 1, 1, False), str(sp))
        sp = parse_status_v2("# branch.head dev\n# branch.upstream origin/dev\n", SyncInfo())
        check("parse_status_v2: 上游已删除", sp.upstream_gone and "上游分支已删除" in sync_text(sp))
        check("sync_text: 已同步", sync_text(SyncInfo(ok=True, upstream="o/m")) == "已同步")

        swork = os.path.join(tmp, "swork")
        os.makedirs(swork)

        def sclone(bare, name):
            dst = os.path.join(swork, name)
            g(swork, "clone", "-q", bare, dst)
            return Repo(name, dst, read_branch(dst))

        bare, seed = new_remote("s_clean")
        rp = sclone(bare, "s_clean")
        s = check_repo(rp)
        check("检查: 已同步", s.ok and s.fetched and sync_text(s) == "已同步", sync_text(s))

        bare, seed = new_remote("s_behind")
        rp = sclone(bare, "s_behind")
        push_change(seed, "a.txt", "a2\n")
        push_change(seed, "a.txt", "a3\n")
        before = head(rp.path)
        s = check_repo(rp, fetch=False)
        check("检查(不获取远端): 看不到远端新提交", s.ok and s.behind == 0 and not s.fetched, sync_text(s))
        s = check_repo(rp)
        check("检查: 待拉取 2", s.behind == 2 and "待拉取 2" in sync_text(s), sync_text(s))
        check("检查: fetch 不改 HEAD 与工作区",
              head(rp.path) == before and read(os.path.join(rp.path, "a.txt")) == "a1\n")

        bare, seed = new_remote("s_local")
        rp = sclone(bare, "s_local")
        write(os.path.join(rp.path, "b.txt"), "local commit\n")
        g(rp.path, "commit", "-q", "-am", "local")
        write(os.path.join(rp.path, "a.txt"), "dirty\n")
        write(os.path.join(rp.path, "c.txt"), "new\n")
        push_change(seed, "b.txt", "remote\n")
        s = check_repo(rp)
        check("检查: 分叉+脏工作区", (s.ahead, s.behind, s.changed, s.untracked) == (1, 1, 1, 1),
              sync_text(s))
        check("检查: 文案", sync_text(s) == "待拉取 1 · 未推送 1 · 未提交 1 · 未跟踪 1", sync_text(s))
        check("检查: 未产生 index.lock",
              not os.path.exists(os.path.join(rp.path, ".git", "index.lock")))

        bare, seed = new_remote("s_noup")
        rp = sclone(bare, "s_noup")
        g(rp.path, "checkout", "-q", "-b", "feature")
        s = check_repo(rp)
        check("检查: 无上游 -> 不 fetch", s.ok and not s.fetched and "无上游分支" in sync_text(s),
              sync_text(s))

        bare, seed = new_remote("s_detached")
        rp = sclone(bare, "s_detached")
        g(rp.path, "checkout", "-q", "--detach")
        s = check_repo(rp)
        check("检查: 游离 HEAD", s.detached and "游离 HEAD" in sync_text(s), sync_text(s))

        bare, seed = new_remote("s_unreach")
        rp = sclone(bare, "s_unreach")
        write(os.path.join(rp.path, "a.txt"), "dirty\n")
        g(rp.path, "remote", "set-url", "origin", "http://127.0.0.1:9/x.git")
        t0 = time.monotonic()
        s = check_repo(rp)
        el = time.monotonic() - t0
        check("检查: 远端不可达仍给出本地状态",
              s.ok and s.fetch_error.startswith("网络错误") and s.changed == 1
              and sync_text(s).startswith("远端获取失败"), f"{sync_text(s)} {s.fetch_error}")
        check("检查: 远端不可达 30 秒内返回", el < 30, f"{el:.1f}s")

        tok = CancelToken()
        tok.cancel()
        s = check_repo(Repo("s_clean", os.path.join(swork, "s_clean"), "main"), True, tok)
        check("检查: 已取消的令牌", s.cancelled)

        rc = run_cli([swork, "--status", "--only", "s_clean,s_behind"])
        check("CLI --status 正常 -> 退出码 0", rc == 0, str(rc))
        rc = run_cli([swork, "--status", "--only", "s_unreach"])
        check("CLI --status 获取失败 -> 退出码 1", rc == 1, str(rc))

        out("\n== 扫描 ==")
        os.makedirs(os.path.join(work, "plain"))
        write(os.path.join(work, "readme.txt"), "x")
        res = scan_dir(work)
        names = {x.name for x in res.repos}
        expected = {"uptodate", "behind", "dirty_conflict", "dirty_ok", "diverged", "noupstream",
                    "detached", "unreachable", "中文 项目", "renamed"}
        check("扫描 -> 只列出仓库", names == expected, str(names ^ expected))
        check("扫描 -> 非 git 目录不在列表", "plain" not in names)
        check("扫描 -> 忽略计数", res.ignored == 1, str(res.ignored))
        check("扫描 -> 读取分支", {x.name: x.branch for x in res.repos}["noupstream"] == "feature")
        empty = os.path.join(tmp, "empty")
        os.makedirs(empty)
        check("空的总目录 -> 空列表", scan_repos(empty) == [])
        res2 = scan_dir(os.path.join(work, "behind"))
        check("目录自身是仓库 -> 列为第一项",
              res2.root_is_repo and len(res2.repos) == 1 and res2.repos[0].name.endswith("(根目录)"))
        try:
            scan_dir(os.path.join(tmp, "not_exist"))
            check("不存在的目录 -> ScanError", False)
        except ScanError:
            check("不存在的目录 -> ScanError", True)

        out("\n== CLI ==")
        rc = run_cli([work, "--only", "uptodate,behind", "--jobs", "2"])
        check("CLI 全部成功 -> 退出码 0", rc == 0, str(rc))
        rc = run_cli([work, "--only", "noupstream"])
        check("CLI 有失败 -> 退出码 1", rc == 1, str(rc))
    except Exception:
        failed.append("自测异常")
        out(traceback.format_exc())
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        _rmtree(tmp)

    out(f"\n结果：通过 {passed}，失败 {len(failed)}")
    for n in failed:
        out(f"  - {n}")
    return 0 if not failed else 1


# ---------------------------------------------------------------------------
# 入口
# ---------------------------------------------------------------------------

def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "--selftest":
        return run_selftest()
    if argv and argv[0] == "--cli":
        return run_cli(argv[1:])
    if argv and argv[0] in ("-h", "--help"):
        setup_console()
        out(__doc__.strip())
        return 0
    return run_gui(argv[0] if argv else None)


if __name__ == "__main__":
    sys.exit(main())
