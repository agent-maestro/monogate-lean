#!/usr/bin/env python3
"""GATE: a public claim that a Lean theorem is proved holds only while its build is green NOW.

WHY THIS EXISTS. The 2026-09-12 monogate.dev audit found "Lean-verified" labels that nothing
re-checked. T17's evidence cited a file that never existed. StrictBarrier.lean, the home of T19, failed
to compile on its last two lines while the site called T19 Lean-verified. A label survives exactly as
long as nobody runs the build, so the build now runs on every deploy.

WHAT A CLAIM MEANS HERE. The theorem is declared in the claimed file at the pinned revision; that file
compiles in the declared Lean environment; and the theorem's own `#print axioms` report has no sorryAx
and nothing outside the axioms the registry allows. A file that merely compiles is NOT a proof of every
theorem in it: a `sorry` compiles with a warning. So each claimed theorem's report is read on its own,
and an error on one theorem's `#print axioms` line fails that theorem, not the whole file.

WHAT "PINNED" COVERS. A revision is a full 40-hex commit sha; a branch, `HEAD` or `sha^` can move. The
claimed file is read with `git show <revision>:<file>`, never from a working tree. Its imports are
compiled .olean files, and each is pinned by where it comes from:
  * Lean core -- by the declared toolchain.
  * a lake package -- the registry declares exactly the revisions lake-manifest.json pins, and every
    package checkout must sit at its pin.
  * a LOCAL source tree -- the environment project's own modules, or a path dependency such as
    monogate-lean's MachLib. The environment declares the tree under `sources`, with a repository and
    a full sha. Every module the claim reaches in it, transitively, must be byte-identical to that
    revision, and `lake build --no-build` must report their build current.
An import from anywhere else, or one nothing resolves, is refused (IMPORT). The gate never builds: a
stale build is ENVIRONMENT, because an .olean older than its source is not the pinned source's proof.
`lake build --no-build` exits 3 both when a module is out of date and when its last build failed;
either way the .olean cannot be trusted, so both refuse.

COVERAGE, BOTH DIRECTIONS. The site's sources are scanned for the claim labels. Every occurrence must
be a registered claim site or an exemption that gives its reason, and every registered site must still
appear on the page. A new "Lean-verified" with no registry entry fails, and so does an entry for a
line that has gone.

REGISTRY (JSON; paths are relative to --root):
  environments  {name: {"project": dir holding lean-toolchain, "toolchain": "leanprover/lean4:vX",
                        "packages": {name: revision, ...} -- exactly what lake-manifest.json pins,
                        "sources": {tree dir: {"repository": git repo dir, "revision": full sha}}}}
                        (`sources` is needed only when a claim imports local modules)
  scan          {"paths": [...], "extensions": [...], "labels": [case-insensitive regex, ...]}
  claims        [{id, statement, sites: [{file, line}], repository, revision, file, environment,
                  theorems: [fully qualified names], allowed_axioms: [...] (optional)}]
  exempt        [{file, line, reason}]

CODES:
  UNPINNED      a claim's revision is not a full commit sha
  ENVIRONMENT   the toolchain or a package revision is not the declared one, or the build of the
                claim's local imports is not current
  IMPORT        an import from an unpinned source, or a local module that differs from its pinned revision
  COMPILE       the pinned file does not compile (an error outside the appended #print axioms lines)
  NOT_DECLARED  a claimed theorem is not declared in the claimed file: misspelt, commented out, or elsewhere
  NO_REPORT     a claimed theorem produced no axiom report (e.g. declared in a namespace, claimed unqualified)
  SORRY         a claimed theorem depends on sorryAx
  AXIOM         a claimed theorem depends on an axiom outside allowed_axioms
  STALE_SITE    a registered claim site or exemption no longer appears in its file
  UNREGISTERED  a label occurrence is neither a claim site nor an exemption
  UNAVAILABLE   repository, revision, environment or `lake` missing, or Lean timed out: exit 2, never a pass

Usage:
  python3 tools/lean_claims/check_claims.py --registry <site>/scripts/lean_claims.json --root <site>
  python3 tools/lean_claims/check_claims.py --self-test [--project <project whose toolchain to use>]
Exit: 0 every claim green | 1 a claim failed | 2 could not evaluate.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

LEAN_TIMEOUT_S = 1800
LAKE_TIMEOUT_S = 600
_FULL_SHA = re.compile(r"[0-9a-f]{40}")
_ERROR_AT = re.compile(r":(\d+):\d+: error")
# A report names the theorem between single quotes, and a Lean name may itself end in primes
# (`foo'`, printed as 'foo''), so the name runs to the LAST quote before " depends" on its line. Until
# 2026-09-13 the name was `[^']+`, and a primed theorem produced no report at all (NO_REPORT), so
# monogate.org could not register `quadratic_lyapunov_sublevel_tight'`.
_DEPENDS = re.compile(r"'([^\n]+?)' depends on axioms: \[(.*?)\]", re.S)
_NONE = re.compile(r"'([^\n]+?)' does not depend on any axioms")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
_LINE_COMMENT = re.compile(r"--[^\n]*")
_IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.+)$", re.M)
_DECLARATION = re.compile(r"(?<![\w.])(?:theorem|lemma|def|abbrev|instance)\s+([^\s(:{\[⦃]+)")
_OLEAN_DIR = (".lake", "build", "lib", "lean")

# Git exports GIT_DIR (and friends) to hooks. Under one, `git -C <another repository>` still reads the
# repository the hook belongs to, so a pinned revision in another repository looks absent. That
# happened to monogate-research's generated-RTL gate on its first push. Every git call here runs with
# the inherited GIT_* variables removed, so `-C` means what it says.
_GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(repo), *args], capture_output=True, env=_GIT_ENV)


def _code(source: str) -> str:
    """Lean source without comments: a commented-out import or theorem is not there."""
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub("", source))


def imports(source: str) -> list[str]:
    return [tok.replace("«", "").replace("»", "") for rest in _IMPORT.findall(_code(source))
            for tok in rest.split() if tok not in ("all", "runtime")]


def declared_names(source: str) -> set[str]:
    """Last name component of every declaration in the file (namespaces make the prefix unreliable)."""
    return {name.replace("«", "").replace("»", "").split(".")[-1] for name in _DECLARATION.findall(_code(source))}


def axiom_reports(output: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {name: [] for name in _NONE.findall(output)}
    for name, axioms in _DEPENDS.findall(output):
        reports[name] = [a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()]
    return reports


def manifest_pins(project: Path) -> dict[str, str]:
    manifest = project / "lake-manifest.json"
    if not manifest.exists():
        return {}
    return {p["name"]: p["rev"] for p in json.loads(manifest.read_text())["packages"] if p.get("rev")}


def environment_problems(env: dict, project: Path) -> list[str]:
    """Why `project` is not the declared environment; [] when it is."""
    wrong = []
    actual = (project / "lean-toolchain").read_text().strip()
    if actual != env["toolchain"]:
        wrong.append(f"{project.name} is on {actual}, the registry declares {env['toolchain']}")
    pins, declared = manifest_pins(project), env.get("packages", {})
    differ = sorted(n for n in pins.keys() | declared.keys() if pins.get(n) != declared.get(n))
    if differ:
        wrong.append(f"lake-manifest.json and the registry's packages disagree on {differ}")
    for name, rev in pins.items():
        head = _git(project / ".lake" / "packages" / name, "rev-parse", "HEAD").stdout.decode().strip()
        if head != rev:
            wrong.append(f"package {name} is checked out at {head[:12] or 'nothing'}, pinned at {rev[:12]}")
    return wrong


def search_path(project: Path) -> tuple[list[Path], Path] | None:
    """LEAN_PATH as `lake env` sets it in `project`, and the toolchain prefix."""
    runs = [subprocess.run(["lake", "env", *cmd], cwd=str(project), env=_GIT_ENV, capture_output=True,
                           text=True, timeout=300) for cmd in (["printenv", "LEAN_PATH"], ["lean", "--print-prefix"])]
    if any(r.returncode for r in runs):
        return None
    return ([Path(p).resolve() for p in runs[0].stdout.strip().split(os.pathsep) if p],
            Path(runs[1].stdout.strip()).resolve())


def import_origin(module: str, search: list[Path], prefix: Path, project: Path) -> str:
    """'core', 'package:<name>', 'unpinned:<dir>' or 'unresolved' -- where `module`'s .olean is loaded from."""
    parts = module.split(".")
    rel = Path(*parts[:-1], f"{parts[-1]}.olean")
    packages = (project / ".lake" / "packages").resolve()
    for d in search:
        if not (d / rel).exists():
            continue
        if d.is_relative_to(prefix):
            return "core"
        if d.is_relative_to(packages):
            return f"package:{d.relative_to(packages).parts[0]}"
        return f"unpinned:{d}"
    return "unresolved"


def local_closure(source: str, env: dict, root: Path, search: list[Path], prefix: Path,
                  project: Path) -> tuple[list[str], list[str]]:
    """(local modules the claimed file reaches, why any of them is not pinned).

    Walks imports transitively. Lean core and pinned packages end the walk. A module built from a local
    source tree must come from a tree the environment declares under `sources`, and its source must be
    byte-identical to that tree's pinned revision -- then its own imports are walked too.
    """
    pinned_packages = set(env.get("packages", {}))
    trees = {(root / d).resolve(): pin for d, pin in env.get("sources", {}).items()}
    toplevels: dict[Path, Path | None] = {}
    modules: list[str] = []
    problems: list[str] = []
    seen: set[str] = set()
    queue = imports(source)
    while queue:
        module = queue.pop(0)
        if module in seen:
            continue
        seen.add(module)
        origin = import_origin(module, search, prefix, project)
        if origin == "core" or origin.removeprefix("package:") in pinned_packages:
            continue
        if not origin.startswith("unpinned:"):
            problems.append(f"{module} comes from {origin}, which no revision pins")
            continue
        olean_dir = Path(origin.removeprefix("unpinned:"))
        tree = Path(*olean_dir.parts[:-4]) if olean_dir.parts[-4:] == _OLEAN_DIR else None
        pin = trees.get(tree) if tree else None
        if pin is None:
            problems.append(f"{module} is built from {tree or olean_dir}, a source tree this environment does "
                            f"not pin (declare it under `sources`)")
            continue
        if not _FULL_SHA.fullmatch(pin.get("revision", "")):
            problems.append(f"the `sources` pin for {tree} is {pin.get('revision')!r}, not a full commit sha")
            continue
        repo = (root / pin["repository"]).resolve()
        if repo not in toplevels:
            top = _git(repo, "rev-parse", "--show-toplevel")
            toplevels[repo] = Path(top.stdout.decode().strip()).resolve() if top.returncode == 0 else None
        if toplevels[repo] is None:
            problems.append(f"{pin['repository']} (the `sources` pin for {tree}) is not a git repository here")
            continue
        parts = module.split(".")
        file = tree.joinpath(*parts[:-1], f"{parts[-1]}.lean")
        if not file.is_file() or not file.resolve().is_relative_to(toplevels[repo]):
            problems.append(f"{module} has no source in {pin['repository']} at {file}")
            continue
        rel = file.resolve().relative_to(toplevels[repo]).as_posix()
        pinned = _git(repo, "show", f"{pin['revision']}:{rel}")
        working = file.read_bytes()
        if pinned.returncode != 0:
            problems.append(f"{module} ({rel}) is not in {pin['repository']} at {pin['revision'][:12]}")
            continue
        if pinned.stdout != working:
            problems.append(f"{module} ({rel}) differs from {pin['repository']} at {pin['revision'][:12]}: "
                            f"the environment would compile against source the pin does not name")
            continue
        modules.append(module)
        queue.extend(imports(working.decode("utf-8", errors="replace")))
    return modules, problems


def stale_build(project: Path, modules: list[str]) -> str | None:
    """Why the environment's build of `modules` is not current; None when it is. Never builds."""
    if not modules:
        return None
    run = subprocess.run(["lake", "build", "--no-build", *(f"+{m}" for m in modules)], cwd=str(project),
                         env=_GIT_ENV, capture_output=True, text=True, timeout=LAKE_TIMEOUT_S)
    if run.returncode == 0:
        return None
    said = [ln.strip() for ln in (run.stdout + run.stderr).splitlines()
            if ln.startswith(("error:", "- ", "Some required"))]
    return f"`lake build --no-build` exited {run.returncode}: {' | '.join(said[:6])[:300]}"


def check_claims(registry: dict, root: Path) -> list[tuple[str, str, str]]:
    """[(code, claim id or file, message)] -- empty when every claim is green."""
    problems: list[tuple[str, str, str]] = []
    if shutil.which("lake") is None:
        return [("UNAVAILABLE", "-", "`lake` is not on PATH")]
    envs = registry.get("environments", {})
    groups: dict[tuple, list[dict]] = defaultdict(list)
    for claim in registry.get("claims", []):
        groups[(claim["repository"], claim["revision"], claim["file"], claim["environment"])].append(claim)
    searched: dict[Path, tuple[list[Path], Path] | None] = {}

    for (repo_rel, revision, file_rel, env_name), claims in groups.items():
        ids = ",".join(c["id"] for c in claims)
        if not _FULL_SHA.fullmatch(revision):
            problems.append(("UNPINNED", ids, f"revision {revision!r} is not a full commit sha, so it can move"))
            continue
        env = envs.get(env_name)
        project = (root / env["project"]).resolve() if env else None
        if project is None or not (project / "lean-toolchain").exists():
            problems.append(("UNAVAILABLE", ids, f"environment {env_name!r} has no lean-toolchain"))
            continue
        wrong = environment_problems(env, project)
        if wrong:
            problems += [("ENVIRONMENT", ids, w) for w in wrong]
            continue
        repo = (root / repo_rel).resolve()
        if _git(repo, "rev-parse", "--git-dir").returncode != 0:
            problems.append(("UNAVAILABLE", ids, f"{repo_rel} is not a git repository here"))
            continue
        shown = _git(repo, "show", f"{revision}:{file_rel}")
        if shown.returncode != 0:
            problems.append(("UNAVAILABLE", ids, f"{file_rel} at {revision[:12]} is not in {repo_rel}; fetch it"))
            continue
        source = shown.stdout.decode("utf-8", errors="replace")

        if project not in searched:
            searched[project] = search_path(project)
        if searched[project] is None:
            problems.append(("UNAVAILABLE", ids, f"`lake env` failed in {project}"))
            continue
        search, prefix = searched[project]
        local, unpinned = local_closure(source, env, root, search, prefix, project)
        if unpinned:
            problems += [("IMPORT", ids, f"{file_rel}: {why}") for why in unpinned]
            continue
        try:
            stale = stale_build(project, local)
        except subprocess.TimeoutExpired:
            problems.append(("UNAVAILABLE", ids, f"`lake build --no-build` timed out after {LAKE_TIMEOUT_S}s"))
            continue
        if stale:
            problems.append(("ENVIRONMENT", ids, f"the build of the {len(local)} local module(s) {file_rel} "
                                                 f"reaches is not current, so it is not the pinned source's -- "
                                                 f"{stale}; run `lake build` in {project}"))
            continue

        # One `#print axioms` per claimed theorem, on known lines after the pinned file, so an error can be
        # attributed: on a theorem's own line it is that theorem's failure, anywhere else the file's.
        theorems = sorted({t for c in claims for t in c["theorems"]})
        first_line = shown.stdout.count(b"\n") + 3
        theorem_at = {first_line + i: t for i, t in enumerate(theorems)}
        with tempfile.TemporaryDirectory(prefix="lean_claims_") as tmp:
            probe = Path(tmp) / "ClaimProbe.lean"
            probe.write_bytes(shown.stdout + b"\n\n" + "".join(f"#print axioms {t}\n" for t in theorems).encode())
            try:
                run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=str(project), env=_GIT_ENV,
                                     capture_output=True, text=True, timeout=LEAN_TIMEOUT_S)
            except subprocess.TimeoutExpired:
                problems.append(("UNAVAILABLE", ids, f"lean timed out after {LEAN_TIMEOUT_S}s on {file_rel}"))
                continue
        output = (run.stdout or "") + "\n" + (run.stderr or "")
        errors = [(int(m.group(1)), line) for line in output.splitlines() for m in [_ERROR_AT.search(line)] if m]
        in_file = [line for n, line in errors if n not in theorem_at]
        if in_file or (run.returncode != 0 and not errors):
            detail = in_file[0] if in_file else output.strip()[-300:]
            problems.append(("COMPILE", ids, f"{file_rel} at {revision[:9]} does not compile: {detail[:240]}"))
            continue
        unreported = {theorem_at[n]: line.split(": error", 1)[-1].strip() for n, line in errors if n in theorem_at}
        reports = axiom_reports(output)
        names = declared_names(source)
        for claim in claims:
            allowed = set(claim["allowed_axioms"]) if "allowed_axioms" in claim else None
            for theorem in claim["theorems"]:
                if theorem.split(".")[-1] not in names:
                    problems.append(("NOT_DECLARED", claim["id"], f"{file_rel} at {revision[:9]} declares no {theorem}"))
                elif theorem in unreported or theorem not in reports:
                    why = unreported.get(theorem, "no report in Lean's output")
                    problems.append(("NO_REPORT", claim["id"], f"no axiom report for {theorem}: {why[:200]}"))
                elif "sorryAx" in reports[theorem]:
                    problems.append(("SORRY", claim["id"], f"{theorem} depends on sorryAx"))
                elif allowed is not None and not set(reports[theorem]) <= allowed:
                    extra = sorted(set(reports[theorem]) - allowed)
                    problems.append(("AXIOM", claim["id"], f"{theorem} depends on {extra}, beyond {sorted(allowed)}"))
    return problems


def check_coverage(registry: dict, root: Path) -> list[tuple[str, str, str]]:
    problems: list[tuple[str, str, str]] = []
    scan = registry["scan"]
    labels = [re.compile(p, re.I) for p in scan["labels"]]
    exts = set(scan["extensions"])
    known: list[tuple[str, str, str]] = (
        [(s["file"], s["line"], c["id"]) for c in registry.get("claims", []) for s in c["sites"]]
        + [(e["file"], e["line"], "exempt") for e in registry.get("exempt", [])])
    for file_rel, line, owner in known:
        path = root / file_rel
        if not path.exists() or line not in path.read_text(encoding="utf-8", errors="replace"):
            problems.append(("STALE_SITE", owner, f"{file_rel} no longer contains {line!r}"))
    for base in scan["paths"]:
        for path in sorted((root / base).rglob("*")):
            if not path.is_file() or path.suffix not in exts or "node_modules" in path.parts:
                continue
            rel = path.relative_to(root).as_posix()
            for n, text in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
                if any(lab.search(text) for lab in labels) and not any(
                        f == rel and line in text for f, line, _ in known):
                    problems.append(("UNREGISTERED", rel, f"line {n} makes a Lean claim with no registry entry: "
                                                          f"{text.strip()[:120]!r}"))
    return problems


def report(problems: list[tuple[str, str, str]], registry: dict) -> int:
    for code, who, msg in problems:
        print(f"  {code:<13} [{who}] {msg}")
    worst = max((2 if c == "UNAVAILABLE" else 1 for c, _, _ in problems), default=0)
    claims = registry.get("claims", [])
    print(f"LEAN CLAIMS: {({0: 'GREEN', 1: 'FAIL', 2: 'UNAVAILABLE'})[worst]}  ({len(claims)} claim(s), "
          f"{sum(len(c['theorems']) for c in claims)} theorem(s), {len(registry.get('exempt', []))} exemption(s))")
    return worst


def _lake_project(path: Path, package: str, lib: str, toolchain: str, requires: str = "") -> None:
    (path / lib).mkdir(parents=True)
    (path / "lean-toolchain").write_text(toolchain + "\n")
    (path / ".gitignore").write_text(".lake/\n")
    (path / "lakefile.lean").write_text(
        f"import Lake\nopen Lake DSL\npackage «{package}»\n{requires}@[default_target] lean_lib «{lib}»\n")
    subprocess.run(["git", "-C", str(path), "init", "-q"], check=True, capture_output=True, env=_GIT_ENV)


def _commit(repo: Path, message: str) -> str:
    for args in (["add", "-A"], ["-c", "user.email=canary@example.invalid", "-c", "user.name=canary",
                                 "-c", "commit.gpgsign=false", "commit", "-q", "-m", message]):
        subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, env=_GIT_ENV)
    return _git(repo, "rev-parse", "HEAD").stdout.decode().strip()


def self_test(project: Path) -> int:
    """Every code but UNAVAILABLE must fire on its canary, and three real theorems -- one with no imports,
    one importing a pinned local module, one importing a pinned path dependency -- must stay green.

    The canaries live in a Lake workspace built here, offline: `canary`, with a path dependency on
    `canarydep`, both on the toolchain of `project`. So the local-import rules are exercised against a
    real .lake build without depending on the state of any real project's build."""
    toolchain = (project / "lean-toolchain").read_text().strip()
    with tempfile.TemporaryDirectory(prefix="lean_claims_selftest_") as tmp:
        root = Path(tmp)
        dep, canary = root / "canarydep", root / "canary"
        _lake_project(dep, "canarydep", "CanaryDep", toolchain)
        (dep / "CanaryDep.lean").write_text("import CanaryDep.Lemma\n")
        (dep / "CanaryDep" / "Lemma.lean").write_text("theorem dep_ok : True := trivial\n")
        _lake_project(canary, "canary", "CanaryLib", toolchain, 'require «canarydep» from "../canarydep"\n')
        (canary / "CanaryLib.lean").write_text("import CanaryLib.Base\nimport CanaryDep.Lemma\n")
        base = canary / "CanaryLib" / "Base.lean"
        base.write_text("theorem base_ok : True := trivial\n")
        for name, text in {
            "Claims.lean": "theorem canary_ok : 1 + 1 = 2 := rfl\n"
                           "theorem canary_sorry : 1 = 2 := by sorry\n"
                           "theorem canary_choice (p : Prop) : p ∨ ¬p := Classical.em p\n"
                           "namespace Canary\ntheorem canary_ns : True := trivial\nend Canary\n"
                           "-- theorem canary_absent : True := trivial\n"
                           "theorem canary_prime' : 1 + 1 = 2 := rfl\n"
                           "theorem canary_choice' (p : Prop) : p ∨ ¬p := Classical.em p\n",
            "Broken.lean": "theorem canary_broken : 1 = 2 := rfl\n",
            "Local.lean": "import CanaryLib.Base\ntheorem local_ok : True := base_ok\n",
            "Dep.lean": "import CanaryDep.Lemma\ntheorem dep_claim : True := dep_ok\n",
        }.items():
            (canary / "CanaryLib" / name).write_text(text)
        dep_rev = _commit(dep, "canarydep")
        rev0 = _commit(canary, "rev0")
        base.write_text("-- a comment, so Base.lean differs between rev0 and rev1\ntheorem base_ok : True := trivial\n")
        rev1 = _commit(canary, "rev1")
        build = subprocess.run(["lake", "build"], cwd=str(canary), env=_GIT_ENV, capture_output=True, text=True,
                               timeout=LAKE_TIMEOUT_S)
        if build.returncode != 0:
            print(f"SELF-TEST UNAVAILABLE: the canary workspace does not build\n{(build.stdout + build.stderr)[-800:]}")
            return 2
        (root / "site").mkdir()
        (root / "site" / "page.md").write_text("Registered: Lean-verified canary.\nUnregistered: Lean-verified stray.\n")

        env = {"project": "canary", "toolchain": toolchain, "packages": manifest_pins(canary),
               "sources": {"canary": {"repository": "canary", "revision": rev1},
                           "canarydep": {"repository": "canarydep", "revision": dep_rev}}}

        def claim(cid: str, theorem: str, file: str = "Claims.lean", environment: str = "env", **extra) -> dict:
            return {"id": cid, "sites": [], "repository": "canary", "revision": rev1, "file": f"CanaryLib/{file}",
                    "environment": environment, "theorems": [theorem], **extra}

        registry = {
            "environments": {
                "env": env,
                "old-toolchain": {**env, "toolchain": "leanprover/lean4:v0.0.0"},
                "extra-package": {**env, "packages": {**env["packages"], "canary": "0" * 40}},
                "dep-unpinned": {**env, "sources": {"canary": env["sources"]["canary"]}},
                "old-pin": {**env, "sources": {**env["sources"], "canary": {"repository": "canary", "revision": rev0}}},
            },
            "scan": {"paths": ["site"], "extensions": [".md"], "labels": ["lean[- ]verified"]},
            "claims": [
                claim("ok", "canary_ok", allowed_axioms=[],
                      sites=[{"file": "site/page.md", "line": "Lean-verified canary"}]),
                claim("sorry", "canary_sorry"),
                claim("choice", "canary_choice", allowed_axioms=["propext"]),
                claim("missing", "canary_absent"),                     # declared only in a comment
                claim("elsewhere", "Nat.add_comm"),                    # has a report, but not this file's
                claim("unqualified", "canary_ns"),                     # declared, but it is Canary.canary_ns
                claim("broken", "canary_broken", file="Broken.lean"),
                claim("unpinned", "canary_ok", revision="HEAD"),       # the same commit today, not tomorrow
                claim("old-toolchain", "canary_ok", environment="old-toolchain"),
                claim("extra-package", "canary_ok", environment="extra-package"),
                claim("local", "local_ok", file="Local.lean"),         # a pinned local import: green
                claim("dep", "dep_claim", file="Dep.lean"),            # a pinned path dependency: green
                claim("prime", "canary_prime'", allowed_axioms=[]),    # a primed name with no axioms: green
                claim("prime-axioms", "canary_choice'",                # a primed name with axioms: green
                      allowed_axioms=["propext", "Classical.choice", "Quot.sound"]),
                claim("dep-unpinned", "dep_claim", file="Dep.lean", environment="dep-unpinned"),
                claim("drift", "local_ok", file="Local.lean", environment="old-pin"),  # Base.lean != rev0's
            ],
            "exempt": [{"file": "site/page.md", "line": "no longer on the page", "reason": "canary"}],
        }
        got = {(c, w) for c, w, _ in check_claims(registry, root) + check_coverage(registry, root)}

        # A source edited and committed after the build: the pin matches the tree, the .olean does not.
        base.write_text("-- edited after the build\ntheorem base_ok : True := trivial\n")
        rev2 = _commit(canary, "rev2")
        after = {**env, "sources": {**env["sources"], "canary": {"repository": "canary", "revision": rev2}}}
        got |= {(c, w) for c, w, _ in check_claims(
            {"environments": {"env": after},
             "claims": [claim("stale-build", "local_ok", file="Local.lean", revision=rev2)]}, root)}

    want = {("SORRY", "sorry"), ("AXIOM", "choice"), ("NOT_DECLARED", "missing"), ("NOT_DECLARED", "elsewhere"),
            ("NO_REPORT", "unqualified"), ("COMPILE", "broken"), ("UNPINNED", "unpinned"),
            ("ENVIRONMENT", "old-toolchain"), ("ENVIRONMENT", "extra-package"),
            ("IMPORT", "dep-unpinned"), ("IMPORT", "drift"), ("ENVIRONMENT", "stale-build"),
            ("STALE_SITE", "exempt"), ("UNREGISTERED", "site/page.md")}
    ok = got == want
    print(f"SELF-TEST {'OK' if ok else 'FAILED'} ({len(want)} canaries fire; canary_ok, a pinned local import, "
          f"a pinned path dependency and two primed names stay green)")
    if not ok:
        print(f"  unexpected: {sorted(got - want)}\n  missing:    {sorted(want - got)}")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--registry", type=Path)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[2],
                    help="for --self-test: the Lean project whose toolchain the canary workspace uses "
                         "(default: this repository)")
    args = ap.parse_args()
    if args.self_test:
        return self_test(args.project.resolve())
    if args.registry is None:
        ap.error("--registry is required")
    registry = json.loads(args.registry.read_text(encoding="utf-8"))
    root = args.root.resolve()
    return report(check_coverage(registry, root) + check_claims(registry, root), registry)


if __name__ == "__main__":
    sys.exit(main())
