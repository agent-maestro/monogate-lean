# Mathlib PR: real analyticity of `Real.log`

**Proposed file:** `Mathlib/Analysis/SpecialFunctions/Log/Analytic.lean` (new)
**Verified against:** Mathlib `v4.14.0` (compiles clean, `#print axioms` = `propext, Classical.choice, Quot.sound` only — no `sorry`).

## Summary

Adds the real-variable analyticity of `Real.log`, filling a genuine gap: Mathlib has the *complex*
result (`analyticAt_clog` and the `clog` composition API) and the *differentiability* of real log
(`Real.differentiableAt_log`), but no `AnalyticAt ℝ Real.log`.

Main results:

| Lemma | Statement |
|---|---|
| `Real.analyticAt_log` | `x ≠ 0 → AnalyticAt ℝ Real.log x` |
| `Real.analyticOnNhd_log_Ioi` | `AnalyticOnNhd ℝ Real.log (Ioi 0)` |
| `Real.analyticOnNhd_log_Iio` | `AnalyticOnNhd ℝ Real.log (Iio 0)` |
| `Real.analyticOnNhd_log_compl_zero` | `AnalyticOnNhd ℝ Real.log {0}ᶜ` |
| `AnalyticAt.log` / `AnalyticWithinAt.log` / `AnalyticOnNhd.log` / `AnalyticOn.log` | composition lemmas mirroring `clog` |

## Motivation

`Real.log` is real-analytic away from `0`, a standard fact that was missing. The naming and the
composition-lemma shape are chosen to parallel two things already in Mathlib:

* `Real.differentiableAt_log (hx : x ≠ 0) : DifferentiableAt ℝ log x` — same signature, one
  regularity level up.
* the `clog` block in `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean` — the composition
  lemmas `AnalyticAt.log` etc. are the real analogues of `AnalyticAt.clog` etc.

## Proof

Through the complex logarithm, so no power series has to be summed by hand:

* `Complex.log_ofReal_re : (Complex.log ↑t).re = Real.log t` (all real `t`) rewrites `Real.log` as
  `re ∘ Complex.log ∘ ofReal`.
* On `Ioi 0`, `↑t` is in the slit plane (`Complex.ofReal_mem_slitPlane`), so `Complex.log` is
  ℂ-analytic there (`analyticAt_clog`); `AnalyticAt.restrictScalars` drops it to `ℝ`, and
  `ofRealCLM` / `reCLM` are analytic as continuous linear maps.
* `analyticAt_log` extends to `x < 0` via `Real.log (-t) = Real.log t` (`Real.log_neg_eq_log`),
  composing the positive-side result with negation.

Because `Complex.log_ofReal_re` is a global identity, the `AnalyticAt.congr` steps use an
`Eventually.of_forall`, not a local neighbourhood argument.

## Placement / dependencies

A new leaf file `.../Log/Analytic.lean` importing `Complex/Analytic` and `Complex/Log` is the
lightest option (it does not add a `Complex/Analytic` dependency onto the existing `Log/Deriv.lean`).
It could alternatively live at the end of `Complex/Analytic.lean`, next to the `clog` block.

## Submitter notes

* Set the copyright/`Authors:` line to your real name before opening the PR — Mathlib requires it.
* Consider whether `analyticAt_log` should carry `@[fun_prop]` (the differentiable analogue does; the
  `clog` analytic lemmas do not — left untagged here to match the `clog` block).

## Provenance

Derived while witnessing MachLib's `analytic_log_pos` axiom against Mathlib's `ℝ` (the axiom
trust-boundary work). Unlike the transcendence-degree machinery from the same effort — which current
Mathlib has since independently added, so it was **not** submitted — real-log analyticity remains
absent upstream and passed a fresh gap-check on 2026-07-10.
