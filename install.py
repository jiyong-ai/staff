#!/usr/bin/env python3
"""短剧剪辑助手 · 安装器（公开；只用 Python 3.8+ 标准库；只在豆包云电脑上运行）

两种运行方式：
  - 一行命令（技能库里的 SKILL.md 首次使用时、install.md、重装命令）：
    python3 -c "import urllib.request as u;exec(u.urlopen('<分发地址>/install.py').read())" --skills-dir "<你的 Skill 目录>" [--order "<用户原话>"] [--terms-agreed <版本>]
  - 以文件方式从技能目录运行：python3 <技能目录>/install.py [--order "<订单号>"]（老的 Gitee 分发仓库就是这样）。

安装器做的事：
  1. 下载 bootstrap.json，用内置公钥验签；下载引导包，校验 sha256；
  2. 原子安装到 <数据目录>/app（数据目录 = CLIPFLOW_HOME 或 ~/.clipflow），同一时间只允许一个安装；
  3. 在 --skills-dir、豆包技能库（~/.doubao/agent_mode/workspace/.user_skills/，存在时）和 ~/.agents/skills/ 下
     写入薄入口 short-drama-clip-doubao/SKILL.md；已有旧版完整 Skill 或分发仓库的安装器（name 相同）时整个目录换成
     薄入口，name 不同的目录不碰；本文件所在的安装器目录在技能库里却叫别的名字时，写好入口后删掉它；
     同一目录下我们以前写的旧入口（OLD_SKILL_NAMES，name 相同且引用 clipflow.py）删掉，免得 agent 还触发它；
     --upload-zip：另在桌面（~/Desktop 或 ~/桌面）生成 short-drama-clip-doubao.zip，给只能在界面上传 Skill 的助手用；
  4. 带了 --terms-agreed <版本>：用户在安装之前已经同意过这一版用户服务协议（install.md、SKILL.md 先请用户同意，
     同意后才让运行安装命令），记进 <数据目录>/consent.json，装好后不再问第二次；
  5. 本机激活过 → 运行 upgrade 补全完整功能（装的已经是完整包时改为运行 status）；
     带了 --order → 运行 setup 激活；都没有 → 请用户发订单号。
  0. 先确认是豆包云电脑（_doubao_check）；不是就 unsupported_env 结束，不下载、不写任何文件。
最后三行固定是 STATUS / SAY / NEXT（和 clipflow.py 一样）。

维护者测试：--from <本地 zip> 跳过下载，直接从本地包安装（引导包、核心包都可以）。
被 exec 运行时没有 __file__、sys.argv[0] 是 "-c"：参数一律取 sys.argv[1:]，不依赖脚本自身的位置。
"""
import argparse
import base64
import binascii
import hashlib
import hmac
import json
import os
import platform
import re
import shlex
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import types
import urllib.error
import urllib.request
import zipfile
from datetime import datetime
from pathlib import Path

# 分发地址（GitHub 公开仓库 raw 根地址），由 scripts/release.py build 填入；源码里为空，只能 --from 本地安装
# --- dist-base begin ---
DIST_BASE = "https://raw.githubusercontent.com/jiyong-ai/staff/main"
# --- dist-base end ---

# --- release-pubkey begin ---
PUBKEY_N = 0xc199296f717639d3be61cf30c60e25e91512317c70ee30b76aab0f7671566d3203367d93655a3699c68743910a819fe529d0465cb1cc67e6bc9bd67e4e0ca1bd8d48ff69dc1ce8c8c380b2ae1194c2a3b63bf5cbaea0eadf1fde33adf34f45744ce0fe35620233a935c6d0e118a49747079b8cb5f255a6d5513cad2bbcae8eeb5230e6bf804b5e5effc8b45e507c0aa7728fc25322ea89ac108c4c08384b57082d769e47b07d5aad5fa4b19548dec668e7474cafab38fe7fc7a80f1b956eb58287592e2b9103709773c2ddd68881f9782caf9cafc35ace312ab18ece075681392e2951d5eee0dc505ec73a4ae8c8abbaa5927c8eccda14580004ef040b9203108ea64ad73a9139b1c7a2f6c6d273b5ff31a5f892f05a8c88b1e16e40b07d098a3727e40a9b9672a2494d703f94fd5a4c1f80c9b2dd5f5b51959f6ba7f666d569442ea0da4084b064680c4f0a4f72d299d0e93ee69b33eeefce01036c0553e0ae5e0f96df441d2d3cde33190748055f985d205553339279c0f9da61b907e32777
PUBKEY_E = 65537
# --- release-pubkey end ---

SKILL_NAME = "short-drama-clip-doubao"
# 以前版本写过的入口名：写好新入口后，同一目录下这些名字的旧入口（确认是我们写的）删掉
OLD_SKILL_NAMES = ("short-drama-pipeline-v2",)
MIN_PYTHON = (3, 8)
TIMEOUT = 30      # 单次下载超时（秒）
RETRIES = 2       # 下载失败后再试几次
RETRY_WAIT = 3    # 第 i 次重试前等 RETRY_WAIT * i 秒
_SHA256_PREFIX = bytes.fromhex("3031300d060960864801650304020105000420")


# ── 豆包云电脑检查（与 scripts/doubao_env.py 相同：本文件被 exec 运行，导入不了它；tests/skill/test_doubao_env.py 核对两处一致）──
PLATFORM_BROWSER = "/opt/browser/chrome"
UNSUPPORTED_SAY = "当前环境暂不支持剪辑，请在豆包对话处切换到豆包工作云电脑～"


def _doubao_check():
    system, machine = platform.system(), platform.machine()
    if system != "Linux" or machine != "x86_64":
        return False, "系统不是 Linux x86_64（%s %s）" % (system or "?", machine or "?")
    if not (os.path.isfile(PLATFORM_BROWSER) and os.access(PLATFORM_BROWSER, os.X_OK)):  # 目录也算 X_OK
        return False, "找不到平台浏览器 %s" % PLATFORM_BROWSER
    if not (os.environ.get("DOUBAO_SANDBOX_TYPE") or "DoubaoWorkVM" in os.environ.get("BROWSER_USER_AGENT", "")):
        return False, "没有豆包云电脑的环境变量（DOUBAO_SANDBOX_TYPE、BROWSER_USER_AGENT）"
    return True, ""


def _unsupported_next(reason):
    return "把 SAY 转告用户，不要尝试绕过。用户切换到豆包工作云电脑后，在那边再说一次。检查结果（排查用，不用发给用户；用户或即用客服问起时如实说）：" + str(reason)[:200]


# ── 输出协议（与 clipflow.py 相同，安装器不能 import clipflow）──
class Finish(Exception):
    def __init__(self, status, say="", nxt="", code=0):
        super().__init__(status)
        self.status, self.say, self.nxt, self.code = status, say, nxt, code


def finish(status, say="", nxt="", code=0):
    raise Finish(status, say, nxt, code)


def log(msg=""):
    print(msg, flush=True)


def emit(f) -> int:
    log("")
    log(f"STATUS: {f.status}")
    log(f"SAY: {f.say or '（无）'}")
    log(f"NEXT: {f.nxt or '（无）'}")
    return f.code


def _sh_quote(p: str) -> str:
    """POSIX shell 引号：含单引号、但没有 shell 在双引号里还会展开的字符时用双引号
    （重装命令 -c "...urlopen('...')..." 就是这种，和 install.md 一致），其余交给 shlex.quote"""
    if "'" in p and not any(ch in p for ch in '"$`\\!'):
        return f'"{p}"'
    return shlex.quote(p)


def quote(parts) -> str:
    return " ".join(_sh_quote(str(p)) for p in parts)


class InstallError(Exception):
    pass


# ── 本机位置（测试会打桩）──────────────────────────
def clipflow_home() -> Path:
    return Path(os.environ.get("CLIPFLOW_HOME") or (Path.home() / ".clipflow"))


def shared_skills_dir() -> Path:
    """各 agent 共用的用户级 Skill 目录"""
    return Path.home() / ".agents" / "skills"


def doubao_skills_dir() -> Path:
    """豆包云电脑的技能库（2026-11-03 实测：软链接到 /runtime/user_skills，「安装到技能库」就装在这里）"""
    return Path.home() / ".doubao" / "agent_mode" / "workspace" / ".user_skills"


def installer_dir():
    """以文件方式从分发仓库的副本运行（豆包装进技能库后运行 <技能目录>/install.py）时，本文件所在目录；
    被 exec 运行（没有 __file__）或者旁边没有 name 相同的 SKILL.md（引导包里的 scripts/install.py）时为 None"""
    f = globals().get("__file__")
    if not f:
        return None
    d = Path(os.path.abspath(f)).parent
    return d if _entry_name(d) == SKILL_NAME else None


def desktop_dir() -> Path:
    home = Path.home()
    for d in (home / "Desktop", home / "桌面"):
        if d.is_dir():
            return d
    return home


# ── 发版签名（与 updater.py 相同：去掉 sig 的规范化 JSON，RSA-3072 / PKCS#1 v1.5 / SHA-256）──
def canonical(obj) -> bytes:
    body = {k: v for k, v in obj.items() if k != "sig"}
    return json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def verify_sig(obj, pubkey=None) -> bool:
    n, e = pubkey or (PUBKEY_N, PUBKEY_E)
    if not isinstance(obj, dict) or not isinstance(obj.get("sig"), str):
        return False
    try:
        sig = base64.b64decode(obj["sig"].encode("ascii"), validate=True)
    except (binascii.Error, ValueError, UnicodeEncodeError):
        return False
    k = (n.bit_length() + 7) // 8
    if len(sig) != k:
        return False
    s = int.from_bytes(sig, "big")
    if s >= n:
        return False
    try:
        t = _SHA256_PREFIX + hashlib.sha256(canonical(obj)).digest()
    except (TypeError, ValueError):
        return False
    if k < len(t) + 11:
        return False
    expected = b"\x00\x01" + b"\xff" * (k - len(t) - 3) + b"\x00" + t
    return hmac.compare_digest(pow(s, e, n).to_bytes(k, "big"), expected)


# ── 下载（走系统代理：用户可能只能通过代理上网；urllib 默认跟随 302）──
def fetch(url: str) -> bytes:
    last = None
    for i in range(RETRIES + 1):
        if i:
            time.sleep(RETRY_WAIT * i)
        req = urllib.request.Request(url, headers={"User-Agent": "clipflow-installer"})
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code}"
            if 400 <= e.code < 500 and e.code not in (408, 429):
                break  # 文件不存在之类的错误，重试也没用
        except (urllib.error.URLError, socket.timeout, OSError) as e:
            last = str(getattr(e, "reason", e))
    raise InstallError(f"下载失败（{last}）")


def _python_ok(required) -> bool:
    try:
        need = tuple(int(x) for x in str(required).split("."))
    except ValueError:
        return True
    return tuple(sys.version_info[:len(need)]) >= need


def download(tmpdir: Path):
    """下载并校验引导包，返回 (zip 路径, 版本信息)"""
    if not DIST_BASE:
        raise InstallError("这个安装器没有配置下载地址，只能用 --from 从本地安装")
    raw = fetch(DIST_BASE.rstrip("/") + "/bootstrap.json")
    try:
        info = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as e:
        raise InstallError(f"版本信息不是合法的 JSON：{e}") from e
    if not verify_sig(info):
        raise InstallError("版本信息的发版签名校验没通过")
    if not _python_ok(info.get("min_python")):
        finish("python_too_old", "这台电脑上有个基础工具版本太旧了，我先帮你升级一下～",
               f"安装 Python {info.get('min_python')} 或更新的版本，再重新运行安装命令", 1)
    url = str(info.get("file") or "")
    if "://" not in url:
        url = DIST_BASE.rstrip("/") + "/" + url.lstrip("/")
    data = fetch(url)
    if hashlib.sha256(data).hexdigest() != str(info.get("sha256") or "").lower():
        raise InstallError("下载的安装包和版本信息对不上（sha256 不一致）")
    p = tmpdir / "clipflow-bootstrap.zip"
    p.write_bytes(data)
    return p, info


def load_updater(zip_path: Path):
    """用安装包自带的 updater.py 安装（原子替换、manifest 校验、安装锁），安装器里不再写一份"""
    try:
        with zipfile.ZipFile(str(zip_path)) as zf:
            src = zf.read("scripts/updater.py")
    except KeyError as e:
        raise InstallError("安装包里缺少 scripts/updater.py") from e
    except (OSError, zipfile.BadZipFile) as e:
        raise InstallError(f"安装包打不开：{e}") from e
    mod = types.ModuleType("clipflow_updater")
    mod.__file__ = "updater.py"
    exec(compile(src, "updater.py", "exec"), mod.__dict__)
    return mod


# ── 薄入口 ──────────────────────────────────────────
def _entry_name(d: Path):
    """目录里 SKILL.md 的 name；没有 SKILL.md 返回 None，读不出 name 返回空串"""
    try:
        text = (d / "SKILL.md").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    text = text.replace("\r\n", "\n").lstrip("﻿")
    m = re.match(r"---[ \t]*\n(.*?)\n---", text, re.S)
    if not m:
        return ""
    n = re.search(r"^name:[ \t]*['\"]?([^'\"\n]*?)['\"]?[ \t]*$", m.group(1), re.M)
    return n.group(1).strip() if n else ""


def _rmtree(p: Path):
    if p.is_symlink() or p.is_file():
        p.unlink()
    elif p.exists():
        shutil.rmtree(str(p))


def write_entry(root: Path, text: str) -> str:
    """在 root/short-drama-clip-doubao/ 写入薄入口；返回空串表示写好了，否则是跳过的原因"""
    target = root / SKILL_NAME
    if target.is_symlink():
        # 维护者常把 Skill 目录软链到源码：只删链接本身，绝不跟进去删
        if target.exists() and _entry_name(target) != SKILL_NAME:
            return "同名目录是别的 Skill"
    elif target.is_dir():
        name = _entry_name(target)
        if name is None and any(target.iterdir()):
            return "同名目录里有别的文件，不是这个 Skill"
        if name is not None and name != SKILL_NAME:
            return "同名目录是别的 Skill"
    elif target.exists():
        return "同名的不是目录"
    root.mkdir(parents=True, exist_ok=True)
    new = Path(tempfile.mkdtemp(prefix=f".{SKILL_NAME}.new-", dir=str(root)))
    try:
        (new / "SKILL.md").write_text(text, encoding="utf-8")
        aside = None
        if target.is_symlink() or target.exists():
            # 老用户迁移：整个旧目录（完整说明和脚本）换成薄入口
            aside = root / f".{SKILL_NAME}.old-{os.getpid()}"
            _rmtree(aside)
            os.replace(str(target), str(aside))
        os.replace(str(new), str(target))
        if aside is not None:
            try:
                _rmtree(aside)
            except OSError:
                pass
    finally:
        if new.exists():
            shutil.rmtree(str(new), ignore_errors=True)
    return ""


def _is_our_old_entry(d: Path, name: str) -> bool:
    """d 是我们以前写的入口：SKILL.md 的 name 是 name，并且正文引用 clipflow.py（薄入口和更早的完整版都是）"""
    if _entry_name(d) != name:
        return False
    try:
        return "clipflow.py" in (d / "SKILL.md").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False


def remove_old_entries(root: Path) -> list:
    """删掉 root 下我们以前写的旧入口；软链接只删链接本身。返回删掉的目录"""
    removed = []
    for old in OLD_SKILL_NAMES:
        d = root / old
        if not (d.is_symlink() or d.is_dir()) or not _is_our_old_entry(d, old):
            continue
        aside = root / f".{old}.old-{os.getpid()}"
        _rmtree(aside)
        os.replace(str(d), str(aside))
        try:
            _rmtree(aside)
        except OSError:
            pass
        removed.append(d)
    return removed


def render_entry(app: Path, reinstall: str) -> str:
    template = (app / "entry" / "SKILL.md").read_text(encoding="utf-8")
    guide = quote([sys.executable, app / "scripts" / "clipflow.py", "guide"])
    return (template.replace("{{APP_DIR}}", str(app)).replace("{{GUIDE_CMD}}", guide)
            .replace("{{INSTALL_CMD}}", reinstall))


def _reinstall_of(text: str) -> str:
    """旧入口末尾的重装命令：最后一个四空格缩进、并且引用 install.py 的行（模板里 {{INSTALL_CMD}} 那一行）；
    更早的完整版说明里没有这样的行，返回空串"""
    for line in reversed(text.replace("\r\n", "\n").split("\n")):
        if re.match(r"^ {4}\S", line) and "install.py" in line:
            return line.strip()
    return ""


def _skills_dir_of(reinstall: str):
    """重装命令里当初带的 --skills-dir（老用户的自定义技能库）；没带或读不出返回 None"""
    try:
        parts = shlex.split(reinstall)
    except ValueError:
        return None
    for i, p in enumerate(parts):
        if p == "--skills-dir" and i + 1 < len(parts):
            return Path(os.path.abspath(os.path.expanduser(parts[i + 1])))
        if p.startswith("--skills-dir="):
            return Path(os.path.abspath(os.path.expanduser(p[len("--skills-dir="):])))
    return None


def refresh_entries(app: Path, fallback: str) -> list:
    """自动更新之后：把技能库里我们以前写的入口 SKILL.md 换成 app/entry 里的新模板（新的显示名、描述）。
    要看的目录：豆包技能库、~/.agents/skills/，加上这些目录里旧入口的重装命令带的 --skills-dir（老用户当初的自定义目录）。
    只换 SKILL.md 一个文件，不换整个目录（调用方可能待在这个目录里）；跳过：目录不存在（不新建）、软链接、
    name 相同但不是我们写的（_is_our_old_entry 为假）、内容已经一样。重装命令沿用旧入口里的，读不出来用 fallback。
    不打印任何东西；写不进去的目录记下原因，其余目录照常处理，最后抛 OSError（调用方下一条命令再试）。
    返回这次写了的 SKILL.md"""
    pending = [doubao_skills_dir(), shared_skills_dir()]
    seen, written, errors = set(), [], []
    while pending:
        root = Path(os.path.abspath(str(pending.pop(0))))
        if _real(root) in seen:
            continue
        seen.add(_real(root))
        target = root / SKILL_NAME
        entry = target / "SKILL.md"
        if target.is_symlink() or not target.is_dir() or entry.is_symlink() or not _is_our_old_entry(target, SKILL_NAME):
            continue
        try:
            old = entry.read_text(encoding="utf-8", errors="replace")
            reinstall = _reinstall_of(old) or fallback
            if not reinstall:
                continue  # 旧入口里没有、也拿不到重装命令（源码目录开发时）：写出来的入口没法重装，宁可不动
            custom = _skills_dir_of(reinstall)
            if custom is not None:
                pending.append(custom)
            text = render_entry(app, reinstall)
            if old == text:
                continue
            fd, tmp = tempfile.mkstemp(prefix=".SKILL.md.new-", dir=str(target))
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    f.write(text)
                try:
                    os.chmod(tmp, entry.stat().st_mode & 0o777)
                except OSError:
                    pass
                os.replace(tmp, str(entry))
            except BaseException:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass
                raise
            written.append(entry)
        except OSError as e:
            errors.append(f"{entry}：{e}")
    if errors:
        raise OSError("；".join(errors))
    return written


def _real(p: Path) -> str:
    return os.path.realpath(str(p))


def entry_roots(a) -> list:
    """要写薄入口的 Skill 目录：--skills-dir、安装器所在的技能库、豆包技能库（存在时）、~/.agents/skills/。
    按真实路径去重（豆包技能库是软链接，agent 传 --skills-dir 时可能给的是链接后的路径）"""
    cands = [Path(a.skills_dir).expanduser()] if a.skills_dir else []
    inst = installer_dir()
    if inst is not None and inst.name == SKILL_NAME:
        # 豆包装进技能库的分发仓库：它的上一级就是技能库，入口原地换掉这个目录
        cands.append(inst.parent)
    if doubao_skills_dir().is_dir():
        cands.append(doubao_skills_dir())
    cands.append(shared_skills_dir())
    roots, seen = [], set()
    for r in cands:
        r = Path(os.path.abspath(str(r)))
        if _real(r) not in seen:
            seen.add(_real(r))
            roots.append(r)
    return roots


def remove_installer_copy(written_roots) -> str:
    """分发仓库的安装器被装进技能库、却没有叫 short-drama-clip-doubao（同名目录被占用时 agent 另起了名字）：
    同一技能库的薄入口写好后删掉它，免得两个 name 相同的技能抢着触发。返回删掉的目录，没删返回空串"""
    inst = installer_dir()
    if inst is None or inst.name == SKILL_NAME or not inst.is_dir():
        return ""
    if _real(inst.parent) not in {_real(r) for r in written_roots}:
        return ""  # 不在技能库里（比如 agent clone 到的 /tmp），留着不碍事
    _rmtree(inst)
    return str(inst)


def write_entries(a, app: Path, reinstall: str) -> list:
    text = render_entry(app, reinstall)
    roots = entry_roots(a)
    written_roots = []
    written = []
    for r in roots:
        try:
            why = write_entry(r, text)
        except OSError as e:
            why = f"写入失败：{e}"
        if why:
            log(f"跳过 {r / SKILL_NAME}：{why}")
        else:
            written.append(r / SKILL_NAME / "SKILL.md")
            written_roots.append(r)
            log(f"已写入入口：{r / SKILL_NAME / 'SKILL.md'}")
            # 新入口写好了才删旧的：新入口被同名目录挡住时，旧入口至少还能用
            try:
                for d in remove_old_entries(r):
                    log(f"已删除旧入口：{d}")
            except OSError as e:
                log(f"旧入口没删掉：{e}")
    try:
        gone = remove_installer_copy(written_roots)
        if gone:
            log(f"已删除装进技能库的安装器副本：{gone}")
    except OSError as e:
        log(f"安装器副本没删掉：{e}")
    if a.upload_zip:
        z = desktop_dir() / f"{SKILL_NAME}.zip"
        tmp = z.with_name(z.name + ".tmp")
        with zipfile.ZipFile(str(tmp), "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr(f"{SKILL_NAME}/SKILL.md", text)
        os.replace(str(tmp), str(z))
        written.append(z)
        log(f"已在桌面生成 Skill 压缩包：{z}")
    return written


def reinstall_cmd(a) -> str:
    """写进薄入口的重装命令：和用户发来的那条一样（不带订单号）"""
    extra = (["--skills-dir", os.path.abspath(os.path.expanduser(a.skills_dir))] if a.skills_dir else []) \
        + (["--upload-zip"] if a.upload_zip else [])
    if DIST_BASE:
        # 字符串用单引号，和 install.md 里的命令一致
        code = "import urllib.request as u;exec(u.urlopen('" + DIST_BASE.rstrip("/") + "/install.py').read())"
        return quote([sys.executable, "-c", code, *extra])
    # 从技能库里的分发仓库副本运行时，那个目录稍后会换成薄入口，重装改用 app 里的安装器
    me = (None if installer_dir() else globals().get("__file__")) \
        or str(clipflow_home() / "app" / "scripts" / "install.py")
    src = ["--from", os.path.abspath(a.from_zip)] if a.from_zip else []
    return quote([sys.executable, os.path.abspath(me), *src, *extra])


# ── 激活 ────────────────────────────────────────────
def has_activation(home: Path, app: Path) -> bool:
    """本机激活过：config.json 里有订单号和 kid，系统密钥库里有密钥（老用户迁移就是这种情况）"""
    try:
        cfg = json.loads((home / "config.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    if not isinstance(cfg, dict) or not (cfg.get("order_no") and cfg.get("kid")):
        return False
    sys.path.insert(0, str(app / "scripts"))
    try:
        import device
        return bool(device.load_secret(home))
    except Exception:  # noqa: BLE001  读不出来就当没激活，交给后面的 setup / 要订单号
        return False
    finally:
        try:
            sys.path.remove(str(app / "scripts"))
        except ValueError:
            pass


def run_clipflow(home: Path, app: Path, argv) -> int:
    """运行刚装好的 clipflow.py，把它的输出原样转发；它的三行就是安装器最后的三行"""
    env = dict(os.environ, CLIPFLOW_HOME=str(home), PYTHONIOENCODING="utf-8")
    r = subprocess.run([sys.executable, str(app / "scripts" / "clipflow.py"), *argv], env=env, cwd=str(home),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = r.stdout.decode("utf-8", "replace")
    sys.stdout.write(out)
    sys.stdout.flush()
    if not re.search(r"^STATUS: ", out, re.M):
        finish("install_failed", "安装好了，但即用创作小助手没能正常启动，请联系即用客服。",
               f"运行 clipflow.py {argv[0]} 出错，把下面的错误原文转告即用客服：{out.strip()[-300:]}", 1)
    return r.returncode


# ── 用户服务协议的同意记录（和 clipflow.py 的 consent.json 同一个格式：{version, agreed_at, ts}）──
CONSENT_FILE = "consent.json"


def record_consent(home: Path, version: int):
    """安装前用户已同意第 version 版协议：记下来，已记着更高版本时保留更高的。写不进去只记一笔，
    装好后 clipflow 会再请用户同意一次（不影响安装）"""
    p = home / CONSENT_FILE
    try:
        old = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        old = {}
    v = old.get("version") if isinstance(old, dict) else None
    old_v = v if isinstance(v, int) and not isinstance(v, bool) else 0
    now_dt = datetime.now()
    rec = {"version": max(version, old_v), "agreed_at": now_dt.isoformat(timespec="seconds"),
           "ts": int(now_dt.timestamp())}
    try:
        home.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(p.suffix + ".tmp")
        tmp.write_text(json.dumps(rec, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(str(tmp), str(p))
    except OSError as e:
        log(f"没记下用户同意的协议版本，装好后会再请用户确认一次（{str(e)[:200]}）")


def install(a) -> int:
    if sys.version_info[:2] < MIN_PYTHON:
        finish("python_too_old", "这台电脑上有个基础工具版本太旧了，我先帮你升级一下～",
               "安装 Python 3.8 或更新的版本，再重新运行安装命令", 1)
    ok, reason = _doubao_check()  # 下载之前、写任何文件之前
    if not ok:
        finish("unsupported_env", UNSUPPORTED_SAY, _unsupported_next(reason), 1)
    home = clipflow_home()
    reinstall = reinstall_cmd(a)
    tmpdir = Path(tempfile.mkdtemp(prefix="clipflow-install-"))
    try:
        try:
            if a.from_zip:
                zip_path, info = Path(a.from_zip), {}
                if not zip_path.is_file():
                    raise InstallError(f"找不到本地安装包：{zip_path}")
            else:
                zip_path, info = download(tmpdir)
            upd = load_updater(zip_path)
        except InstallError as e:
            finish("install_failed", "安装没成功，可能是网络不太稳定，我稍后再试一下。",
                   f"稍后重新运行安装命令：{reinstall}（错误：{str(e)[:200]}）", 1)
        try:
            m = upd.install_zip(zip_path, home, expect_sha256=info.get("sha256"))
        except upd.LockBusy:
            finish("install_failed", "即用创作小助手正在安装，我等一会儿再看看。",
                   f"另一个安装或更新正在进行，等半分钟后重新运行安装命令：{reinstall}", 1)
        except upd.UpdateError as e:
            finish("install_failed", "安装没成功，我稍后再试一下；一直不行请联系即用客服。",
                   f"稍后重新运行安装命令：{reinstall}；不要修改安装包或跳过校验（错误：{str(e)[:200]}）", 1)
    finally:
        shutil.rmtree(str(tmpdir), ignore_errors=True)
    app = home / "app"
    # agent 常在技能目录里运行安装器（豆包会先 cd 进去），写入口时这个目录会被整个换掉：先离开，
    # 免得后面的步骤和子进程待在已删除的目录里
    try:
        os.chdir(str(home))
    except OSError:
        pass
    full = len(set(m["files"]) - set(m["bootstrap_files"])) > 0
    log(f"即用创作小助手 {m['version']} 已安装到 {app}（{'完整版' if full else '待激活'}）")
    try:
        write_entries(a, app, reinstall)
    except OSError as e:
        finish("install_failed", "安装没成功，我稍后再试一下；一直不行请联系即用客服。",
               f"写入 Skill 入口失败，检查目录权限后重新运行安装命令：{reinstall}（错误：{str(e)[:200]}）", 1)
    if a.terms_agreed > 0:
        record_consent(home, a.terms_agreed)
    if has_activation(home, app):
        if full:
            # 装的就是完整包（维护者 --from 核心包）：不用再下载，直接看状态。status 开头会照常定期检查新版，
            # 检查失败也不影响输出，免得线上暂时不可用时以 upgrade_failed 结尾、看起来像没装好
            log("这台电脑之前激活过，完整功能已经装好，接着检查当前状态")
            return run_clipflow(home, app, ["status"])
        log("这台电脑之前激活过，不用再输订单号，接着下载完整功能")
        return run_clipflow(home, app, ["upgrade"])
    if a.order:
        return run_clipflow(home, app, ["setup", "--order", a.order])
    finish("installed_need_order",
           "即用创作小助手装好啦！请发我你的抖音订单编号（抖音订单详情里的一串数字），我用它激活。",
           "拿到订单号后运行："
           + quote([sys.executable, app / "scripts" / "clipflow.py", "setup", "--order", "<用户发来的订单号原话>"]))


def main(argv=None) -> int:
    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(encoding="utf-8", errors="replace")
        except Exception:  # noqa: BLE001
            pass
    argv = list(sys.argv[1:] if argv is None else argv)
    ap = argparse.ArgumentParser(prog="install.py", description="短剧剪辑助手安装器")

    def usage_error(message):
        log(f"参数错误：{message}")
        raise Finish("usage_error", "", "检查安装命令的参数（--skills-dir、--order、--from、--upload-zip、--terms-agreed）后重新运行", 2)

    ap.error = usage_error
    ap.add_argument("--skills-dir", default="", help="当前 agent 的用户级 Skill 目录（不知道就省略）")
    ap.add_argument("--order", default="", help="用户消息里的订单号（可直接传原话）")
    ap.add_argument("--from", dest="from_zip", default="", help="从本地 zip 安装（维护者测试用）")
    ap.add_argument("--upload-zip", action="store_true", help="另在桌面生成入口 zip（只能界面上传 Skill 的 agent）")
    ap.add_argument("--terms-agreed", type=int, default=0, help="用户安装前已同意的用户服务协议版本（安装说明里写好的数字）")
    try:
        return install(ap.parse_args(argv))
    except Finish as f:
        return emit(f)
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
