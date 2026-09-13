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

WHAT "PINNED" COVERS, AND WHAT IT DOES NOT. A revision is a full 40-hex commit sha; a branch, `HEAD` or
`sha^` can move. The claimed file is read with `git show <revision>:<file>`, never from a working tree.
Its imports are compiled .olean files, so they are only as pinned as the environment: the toolchain
must be the declared one, the registry must declare exactly the package revisions lake-manifest.json
pins, and every package checkout must sit at its pin. Every direct import must then come from Lean
core or one of those packages. An import from the environment's own build, or from a path dependency,
is refused (IMPORT). Its .olean is whatever was built last, not the pinned revision, and this gate does
not rebuild it.

COVERAGE, BOTH DIRECTIONS. The site's sources are scanned for the claim labels. Every occurrence must
be a registered claim site or an exemption that gives its reason, and every registered site must still
appear on the page. A new "Lean-verified" with no registry entry fails, and so does an entry for a
line that has gone.

REGISTRY (JSON; paths are relative to --root):
  environments  {name: {"project": dir holding lean-toolchain, "toolchain": "leanprover/lean4:vX",
                        "packages": {name: revision, ...} -- exactly what lake-manifest.json pins}}
  scan          {"paths": [...], "extensions": [...], "labels": [case-insensitive regex, ...]}
  claims        [{id, statement, sites: [{file, line}], repository, revision, file, environment,
                  theorems: [fully qualified names], allowed_axioms: [...] (optional)}]
  exempt        [{file, line, reason}]

CODES:
  UNPINNED      a claim's revision is not a full commit sha
  ENVIRONMENT   the toolchain, or a package revision, is not the declared one
  IMPORT        the pinned file imports a module from outside Lean core and the pinned packages
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
  python3 tools/lean_claims/check_claims.py --self-test [--project <built Lean project>]
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
_FULL_SHA = re.compile(r"[0-9a-f]{40}")
_ERROR_AT = re.compile(r":(\d+):\d+: error")
_DEPENDS = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.S)
_NONE = re.compile(r"'([^']+)' does not depend on any axioms")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
_LINE_COMMENT = re.compile(r"--[^\n]*")
_IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.+)$", re.M)
_DECLARATION = re.compile(r"(?<![\w.])(?:theorem|lemma|def|abbrev|instance)\s+([^\s(:{\[⦃]+)")

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
        pinned = set(env.get("packages", {}))
        outside = [(m, origin) for m in imports(source)
                   for origin in [import_origin(m, search, prefix, project)]
                   if origin != "core" and origin.removeprefix("package:") not in pinned]
        if outside:
            problems += [("IMPORT", ids, f"{file_rel} imports {m} from {origin}, which no revision pins")
                         for m, origin in outside]
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


def self_test(project: Path) -> int:
    """Every code but UNAVAILABLE must fire on its canary, and a real theorem at a registered site must
    stay green. `project` must be a BUILT Lean project: `lake env` in an unbuilt one would fetch."""
    found = search_path(project)
    if found is None:
        print(f"SELF-TEST UNAVAILABLE: `lake env` failed in {project}")
        return 2
    search, prefix = found
    packages_dir = (project / ".lake" / "packages").resolve()
    local = "CanaryNoSuchModule"                      # unresolved is refused too, if nothing local is built
    for d in search:
        olean = None if d.is_relative_to(prefix) or d.is_relative_to(packages_dir) else next(d.rglob("*.olean"), None)
        if olean is not None:
            local = ".".join(olean.relative_to(d).with_suffix("").parts)
            break

    with tempfile.TemporaryDirectory(prefix="lean_claims_selftest_") as tmp:
        root = Path(tmp)
        repo = root / "canary"
        repo.mkdir()
        (repo / "Canary.lean").write_text(
            "theorem canary_ok : 1 + 1 = 2 := rfl\n"
            "theorem canary_sorry : 1 = 2 := by sorry\n"
            "theorem canary_choice (p : Prop) : p ∨ ¬p := Classical.em p\n"
            "namespace Canary\ntheorem canary_ns : True := trivial\nend Canary\n"
            "-- theorem canary_absent : True := trivial\n")
        (repo / "Broken.lean").write_text("theorem canary_broken : 1 = 2 := rfl\n")
        (repo / "Local.lean").write_text(f"import {local}\ntheorem canary_local : True := trivial\n")
        for args in (["init", "-q"], ["add", "."],
                     ["-c", "user.email=canary@example.invalid", "-c", "user.name=canary",
                      "-c", "commit.gpgsign=false", "commit", "-q", "-m", "canary"]):
            subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, env=_GIT_ENV)
        revision = _git(repo, "rev-parse", "HEAD").stdout.decode().strip()
        (root / "site").mkdir()
        (root / "site" / "page.md").write_text("Registered: Lean-verified canary.\nUnregistered: Lean-verified stray.\n")

        env = {"project": str(project), "toolchain": (project / "lean-toolchain").read_text().strip(),
               "packages": manifest_pins(project)}

        def claim(cid: str, theorem: str, file: str = "Canary.lean", environment: str = "env", **extra) -> dict:
            return {"id": cid, "sites": [], "repository": "canary", "revision": revision, "file": file,
                    "environment": environment, "theorems": [theorem], **extra}

        registry = {
            "environments": {"env": env,
                             "old-toolchain": {**env, "toolchain": "leanprover/lean4:v0.0.0"},
                             "extra-package": {**env, "packages": {**env["packages"], "canary": "0" * 40}}},
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
                claim("local", "canary_local", file="Local.lean"),
                claim("unpinned", "canary_ok", revision="HEAD"),       # the same commit today, not tomorrow
                claim("old-toolchain", "canary_ok", environment="old-toolchain"),
                claim("extra-package", "canary_ok", environment="extra-package"),
            ],
            "exempt": [{"file": "site/page.md", "line": "no longer on the page", "reason": "canary"}],
        }
        got = {(c, w) for c, w, _ in check_claims(registry, root) + check_coverage(registry, root)}
    want = {("SORRY", "sorry"), ("AXIOM", "choice"), ("NOT_DECLARED", "missing"), ("NOT_DECLARED", "elsewhere"),
            ("NO_REPORT", "unqualified"), ("COMPILE", "broken"), ("IMPORT", "local"), ("UNPINNED", "unpinned"),
            ("ENVIRONMENT", "old-toolchain"), ("ENVIRONMENT", "extra-package"),
            ("STALE_SITE", "exempt"), ("UNREGISTERED", "site/page.md")}
    ok = got == want
    print(f"SELF-TEST {'OK' if ok else 'FAILED'} ({len(want)} canaries fire, canary_ok stays green; "
          f"local import canary: {local})")
    if not ok:
        print(f"  unexpected: {sorted(got - want)}\n  missing:    {sorted(want - got)}")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--registry", type=Path)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[2],
                    help="built Lean project for --self-test (default: this repository)")
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
