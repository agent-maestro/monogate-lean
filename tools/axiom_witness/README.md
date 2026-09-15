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

- **Ledger** (machlib, the commit that added `u_le_inv_two_pow_52` and `real_abs_eps_eq_zero` and narrowed eight float-bridge
  axioms to finite inputs): `AxiomLedger OK: 256 axioms pinned; 112 headline footprints ⊆ trusted (169)`.
- **Bridge** (monogate-lean, the commit that witnessed `u_le_inv_two_pow_52` and stopped pinning the footprint):
  `WITNESS-BRIDGE PASS 124/124 verbatim-witnessed; full accounting of 169 trusted axioms`.
  - Coverage: `124 witnessed + 3 standard + 12 mapped + 32 float-bridge + 0 tracked-gap`.
  - `real_abs_eps_eq_zero` is a float-bridge row: `real_abs_eps` means something only through `real_abs_rounds`.
  - **The trusted footprint is no longer a copy.** `AxiomWitnessBridge.lean` reads `def trustedFootprint` out of machlib's
    `AxiomLedger.lean` on every build, found from the `MachLib` it imports. The pinned copy it replaces held 152 names
    against the ledger's 167, and its cross-check had passed against the copy. Two controls run in the build (the parser
    on a doctored list; an injected trusted name reported alone), and `check_bridge.py --self-test` carries a second
    canary: de-classifying `Certcom.float_lit_1_5`, a ledger name the old copy lacked, turns the bridge red.
  - Canaries OK.

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
