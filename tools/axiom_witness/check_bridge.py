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
    cov = re.search(r"full accounting of (\d+) trusted axioms", out)
    wit = re.search(r"(\d+)/(\d+) registered axioms verbatim-witnessed", out)
    if code != 0 or not (cov and wit):
        print(f"{R}{B}WITNESS-BRIDGE FAIL{RST} — the MachLib.Real ⊨ ℝ layer broke:")
        for line in out.splitlines():
            if "AxiomWitnessBridge:" in line or "error" in line.lower():
                print(f"    {R}{line.strip()}{RST}")
        return 1
    print(f"{G}{B}WITNESS-BRIDGE PASS{RST}  {wit.group(1)}/{wit.group(2)} verbatim-witnessed; "
          f"full accounting of {cov.group(1)} trusted axioms.")
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


def main() -> int:
    rc = enforce()
    if "--self-test" in sys.argv:
        rc |= self_test()
    return rc


if __name__ == "__main__":
    sys.exit(main())
