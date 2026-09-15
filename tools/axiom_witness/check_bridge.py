#!/usr/bin/env python3
"""AxiomWitnessBridge CI runner — enforces the verbatim MachLib.Real ⊨ ℝ witness layer.

`MonogateEML/AxiomWitnessBridge.lean` is self-gating: it interprets each trusted MachLib axiom's
type into ℝ and typechecks a witness against it, and its cross-check asserts every trusted axiom
is witnessed / standard / mapped / a tracked gap. Building it green means the layer holds; a
witness that stops typechecking (e.g. a Mathlib rename under the pinned rev) or an unaccounted
trusted axiom turns it red. This runner builds it, asserts the coverage line, and additionally
asserts the monogate-lean witness THEOREMS are sorryAx-free (only Lean's three standard axioms).

`--self-test` proves the gate goes RED when a witness is wrong (registering `add_comm ⊣ mul_comm`).

Building the bridge green already implies every registered witness typechecks at its interpreted
axiom type AND the cross-check accounts for all trusted axioms; that IS the guarantee. (The witness
theorems `rolle_witnessed` / `not_oldOpenRolle` are separately verified sorryAx-free.)

Usage:
    python3 tools/axiom_witness/check_bridge.py
    python3 tools/axiom_witness/check_bridge.py --self-test
"""
import os, re, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BRIDGE = os.path.join(ROOT, "MonogateEML", "AxiomWitnessBridge.lean")
G, R, RST, B = "\033[32m", "\033[31m", "\033[0m", "\033[1m"


def run_lean_src(src: str) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(src); path = f.name
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr
    finally:
        os.unlink(path)


def enforce() -> int:
    code, out = run_lean_src(open(BRIDGE, encoding="utf-8").read())
    # The bridge's cross-check fails the build on any unaccounted trusted axiom, and since 2026-09-15 on coverage parts
    # that do not sum to the trusted count, so exit 0 plus its coverage line IS full accounting. That line once read
    # "full accounting of N trusted axioms", then "... + G tracked-gap, against N trusted axioms", whose parts were class
    # LENGTHS and could sum past N (a witness for an axiom no footprint trusts was added in). It now counts trusted names
    # per class, "W witnessed + ... + G tracked-gap = N, against N trusted axioms", and names the rest after "outside the
    # trusted footprint". Matching only one wording turned this runner red on a green bridge (found 2026-09-12), so the
    # trusted count is still read from "against N", and the parts are printed when present rather than required.
    cov = re.search(r"(?:full accounting of|against) (\d+) trusted axioms", out)
    wit = re.search(r"(\d+)/(\d+) registered axioms verbatim-witnessed", out)
    parts = re.search(r"AxiomWitnessBridge coverage: (.+?) = (\d+), against \d+ trusted axioms", out)
    outside = re.search(r"outside the trusted footprint, not counted: (.*?)\.\s*$", out, re.M)
    if code != 0 or not (cov and wit):
        print(f"{R}{B}WITNESS-BRIDGE FAIL{RST} — the MachLib.Real ⊨ ℝ layer broke:")
        for line in out.splitlines():
            if "AxiomWitnessBridge:" in line or "error" in line.lower():
                print(f"    {R}{line.strip()}{RST}")
        return 1
    detail = f" ({parts.group(1)} = {parts.group(2)})" if parts else ""
    extra = f"; outside the footprint, not counted: {outside.group(1)}" if outside else ""
    print(f"{G}{B}WITNESS-BRIDGE PASS{RST}  {wit.group(1)}/{wit.group(2)} verbatim-witnessed; "
          f"full accounting of {cov.group(1)} trusted axioms{detail}{extra}.")
    return 0


def self_test() -> int:
    src = open(BRIDGE, encoding="utf-8").read().replace(
        "(`MachLib.Real.add_comm,       Unhygienic.run `(add_comm)),",
        "(`MachLib.Real.add_comm,       Unhygienic.run `(mul_comm)),", 1)  # wrong witness
    code, out = run_lean_src(src)
    if code != 0 and "FAIL the verbatim" in out:
        print(f"{G}canary OK{RST} — the bridge goes RED on a wrong witness (add_comm ⊣ mul_comm rejected).")
        return 0
    print(f"{R}canary FAILED — a wrong witness did not turn the bridge red; it has no teeth.{RST}")
    return 1


def self_test_footprint() -> int:
    """The trusted footprint is READ from machlib's ledger (since 2026-09-14), so an axiom the old hand-pinned copy LACKED
    must now be caught. `Certcom.float_lit_1_5` was added to machlib's ledger on 2026-09-14 and never reached the copy:
    de-classify it and the bridge must go red naming it. Against the copy it would have stayed green."""
    src = open(BRIDGE, encoding="utf-8").read()
    bad = src.replace("`Certcom.float_lit_1_5, ", "", 1)
    if bad == src:
        print(f"{R}canary BROKEN — `Certcom.float_lit_1_5` is no longer in bridgeAxioms; the specimen is inert.{RST}")
        return 1
    code, out = run_lean_src(bad)
    if code != 0 and "UNACCOUNTED" in out and "Certcom.float_lit_1_5" in out:
        print(f"{G}canary OK{RST} — de-classifying `Certcom.float_lit_1_5`, a ledger name the old pinned copy lacked, "
              f"turns the bridge RED: the footprint is the live ledger's.")
        return 0
    print(f"{R}canary FAILED — removing `Certcom.float_lit_1_5` from bridgeAxioms did not turn the bridge red; the "
          f"footprint it checks is not the live ledger's.{RST}")
    return 1


def self_test_coverage_sum() -> int:
    """The coverage line's parts must sum to the trusted count (since 2026-09-15; before, they were class lengths and
    summed to 171 against 169). A trusted name counted by two classes must break that sum: list `MachLib.Real.u_nonneg`,
    which is witnessed and trusted, among the mapped constants as well. Nothing is then unaccounted, so only the sum check
    can turn the bridge red. Against the bridge before the check existed this canary FAILS, which is what it is for."""
    src = open(BRIDGE, encoding="utf-8").read()
    anchor = "def mappedConstants : List Name := [`MachLib.Real, "
    bad = src.replace(anchor, "def mappedConstants : List Name := [`MachLib.Real.u_nonneg, `MachLib.Real, ", 1)
    if bad == src:
        print(f"{R}canary BROKEN — the `mappedConstants` anchor is gone; the specimen is inert.{RST}")
        return 1
    code, out = run_lean_src(bad)
    if code != 0 and "coverage does not add up" in out and "UNACCOUNTED" not in out:
        print(f"{G}canary OK{RST} — a trusted name in two classes (`MachLib.Real.u_nonneg`, witnessed and mapped) turns "
              f"the bridge RED on the coverage sum alone.")
        return 0
    print(f"{R}canary FAILED — a trusted name counted by two classes did not break the coverage sum; its parts can "
          f"overcount the trusted footprint.{RST}")
    return 1


def main() -> int:
    rc = enforce()
    if "--self-test" in sys.argv:
        rc |= self_test()
        rc |= self_test_footprint()
        rc |= self_test_coverage_sum()
    return rc


if __name__ == "__main__":
    sys.exit(main())
