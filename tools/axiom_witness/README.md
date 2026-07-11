# Axiom trust boundary — CI

Two machine-checked, grep-free gates enforce that the Khovanskii/EML claims rest only on a
**sound, witnessed** axiom base. Both read the Lean *kernel* (`getEnv`, `Lean.collectAxioms`,
type-elaboration), never grep or name paraphrase. Run against a **pinned Mathlib rev**
(`v4.14.0`, in both `lakefile.lean`s).

## The two checks (run both in CI)

1. **Ledger** — machlib. Every axiom enumerated; shipped footprints ⊆ trusted; both-direction diff.
   ```
   cd machlib/foundations && python3 tools/axiom_ledger/check_ledger.py --self-test
   ```
   Fails on: a new/undisclosed axiom (unknown), a snapshot entry whose axiom vanished (rot), a
   shipped headline footprint growing past `trustedFootprint`, or a disclosed axiom going
   load-bearing. Canary proves it goes red on drift.

2. **Witness bridge** — monogate-lean. Every trusted axiom is verbatim-witnessed `MachLib.Real ⊨ ℝ`
   (interpret the axiom's actual type into ℝ, typecheck a witness against it — not name-matching),
   and the cross-check accounts for all 61 trusted axioms (witnessed ∪ standard ∪ mapped ∪ gap).
   ```
   cd monogate-lean && python3 tools/axiom_witness/check_bridge.py --self-test
   ```
   Fails on: a witness that stops typechecking (e.g. a Mathlib rename under the pinned rev) or a
   trusted axiom with no witness/gap entry. Canary proves it goes red on a wrong witness.

## The chain

Ledger: *shipped theorems depend only on the trusted set.*
Bridge: *the trusted set is sound over ℝ, by typecheck.*
Together: "is X witnessed / in the footprint?" is a CI status, not an argument.

## Current state

**252 axioms** pinned; 4 headline footprints ⊆ 61 trusted; all **61 trusted axioms accounted for
with zero tracked gaps** — **57 verbatim-witnessed**, the rest Lean-standard axioms and mapped
type-carriers (Real/HasDerivAt/IsAnalyticOnReals). The last gap,
`analytic_log_pos`, is now witnessed by `MonogateEML.RealModel.analyticOnNhd_real_log_Ioi`
(`Real.log` analytic on `(0,∞)`, derived through `Complex.log` on the slit plane — Mathlib has no
direct real-log analyticity, so this is a genuine derivation; a generalized, PR-ready version lives
in `mathlib-pr/`). The one formerly-unsound axiom, `eml_tree_analytic_on_pos`, has had its dropped
`LogArgPos` side-condition restored and is disclosed-but-sound; the retired open-interval `rolle` is
machine-checked *false* (`RealModel.not_oldOpenRolle`).
