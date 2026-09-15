# Axiom trust boundary

Two machine-checked, grep-free gates check that the Khovanskii/EML claims rest only on a
**sound, witnessed** axiom base. Both read the Lean *kernel* (`getEnv`, `Lean.collectAxioms`,
type-elaboration), never grep or name paraphrase.

**Pins.** Both projects are on **Lean v4.32.2** (`lean-toolchain`). monogate-lean pins **Mathlib v4.32.2**
in its `lakefile.lean` and `lake-manifest.json`. machlib is Mathlib-free.

## The two checks

1. **Ledger** (machlib). Every axiom is enumerated, shipped footprints ⊆ trusted, and the diff runs in both directions.
   ```
   cd machlib/foundations && python3 tools/axiom_ledger/check_ledger.py --self-test
   ```
   - **Fails on:**
     - a new or undisclosed axiom (unknown);
     - a snapshot entry whose axiom vanished (rot);
     - a shipped headline footprint growing past `trustedFootprint`;
     - a disclosed axiom going load-bearing.
   - A canary proves it goes red on drift.
   - **Where it runs:** machlib's `reproduction-walk` workflow (Rung 5, GitHub-hosted x86-64, weekly
     and on push), and by hand.

2. **Witness bridge** (monogate-lean). Every registered trusted axiom is verbatim-witnessed
   `MachLib.Real ⊨ ℝ`: the axiom's actual type is interpreted into ℝ and a witness is typechecked
   against it, with no name-matching. The cross-check accounts for every trusted axiom as witnessed,
   standard, mapped, float-bridge or tracked gap; an unaccounted axiom fails the build.
   ```
   cd monogate-lean && python3 tools/axiom_witness/check_bridge.py --self-test
   ```
   - **Fails on:** a witness that stops typechecking (for example, a Mathlib rename under the pinned
     rev), or a trusted axiom with no witness or gap entry.
   - A canary proves it goes red on a wrong witness.
   - **Where it runs:** monogate-lean has no CI. The bridge runs by hand, and in monogate.org's
     `npm run predeploy` (`check:axiom-bridge`) before every deploy of that site.

## The chain

Ledger: *shipped theorems depend only on the trusted set.*
Bridge: *the trusted set is sound over ℝ, by typecheck.*
Together, "is X witnessed / in the footprint?" is a checked status, not an argument. It holds as of
each check's last run, which is what the next section records.

## Current state (measured 2026-09-14)

- **Ledger** (machlib, the commit that added the literal, libm-finiteness and `u_le_half` axioms): `AxiomLedger OK: 254 axioms pinned; 102 headline footprints ⊆ trusted (167)`.
- **Bridge** (monogate-lean, the commit that witnessed `u_le_half`): `WITNESS-BRIDGE PASS 123/123 verbatim-witnessed; full accounting of 152 trusted axioms`.
  - Coverage: `123 witnessed + 3 standard + 12 mapped + 31 float-bridge + 0 tracked-gap`.
  - The seven axioms added to `bridgeAxioms` that day are float-bridge rows: `float_lit_1_5`, `float_lit_0_4`,
    `float_lit_0_05`, `real_exp_finite`, `real_sinh_finite`, `real_cosh_finite`, `real_log_finite`.
  - The bridge's pinned `trustedFootprint` copy holds 152 names against the ledger's 167: it lacks the seven
    `realOfScientific` / `lit_one_eq` names machlib promoted on 2026-09-11 and the eight added on 2026-09-14. machlib's
    gate 13 reads the live ledger and accounts for all 167, so nothing fails; the copy is stale, not the accounting.
  - Canary OK.

**Notable axioms:**
- **The last tracked gap, `analytic_log_pos`,** is witnessed by
  `MonogateEML.RealModel.analyticOnNhd_real_log_Ioi`: `Real.log` is analytic on `(0,∞)`.
  - It is derived through `Complex.log` on the slit plane. Mathlib has no direct real-log analyticity,
    so this is a genuine derivation.
  - A generalized, PR-ready version lives in `mathlib-pr/`.
- **The formerly-unsound axiom `eml_tree_analytic_on_pos`** carries its restored side condition
  (`EMLLogArgPosOnIoi t`), and the ledger discloses it.
- **The retired open-interval `rolle`** is machine-checked *false* (`MonogateEML.RealModel.not_oldOpenRolle`).

**Superseded figures.** Earlier revisions of this file said 252 axioms pinned, 4 headline
footprints, 61 trusted and 57 witnessed, Mathlib `v4.14.0`, and "run both in CI". None of that held
on 2026-09-12.
