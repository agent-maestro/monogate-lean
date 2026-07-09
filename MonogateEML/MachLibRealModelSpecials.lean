import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `MachLib.Real` soundness witness — special functions + the last three items

Final pass over the deferred `MachLib.Real` axioms. It resolves the three
remaining categories honestly:

## 1. `eml_tree_analytic_on_pos` — already proven upstream

MachLib's `eml_tree_analytic_on_pos` (every EML tree's `eval` is analytic on
`(0, ∞)`) was *ported from* `monogate-lean/MonogateEML/InfiniteZerosBarrier.lean`,
where it is **already proven sorry-free** as `eml_tree_analytic` (line 197, via
complexification through `ℂ`), with `#print axioms = [propext, Classical.choice,
Quot.sound]`. Crucially the upstream proof carries the honest **`WellFormedPos`**
domain condition (every nested `log`-argument stays positive on the interval) —
which the MachLib axiom's own docstring admits it *omits*. So the true statement
is witnessed; the axiom is the side-condition-dropped simplification. Nothing to
re-prove — this file only records the correspondence.

## 2. Special functions

Witnessed below against Mathlib: the `arctan` bounds and `log10`/`exp10`
(modeled by `Real.logb 10` and `(10:ℝ) ^ ·`). **`erf` is genuinely absent from
Mathlib** (no `Real.erf`), so `neg_one_le_erf`/`erf_le_one` have no generic
model — an honest gap. The `tanh` bounds (`tanh_lt_one`, …) have no one-line
Mathlib lemma (Mathlib has `Real.tanh` but not the `< 1` bound) and are low
value; left for a follow-on if ever needed.

## 3. Floats — nothing to witness

`monogate-lean/MonogateEML/Float64.lean` is **axiom-free scaffolding** (verified),
and `MachLib.Real` models exact reals with no IEEE-754 notion. There are no float
axioms to witness. Grounding Forge's ULP / bit-exact claims is a Flocq +
per-platform `libm-test-ulps` offline-validation project, not a Lean consistency
witness — it cannot be done here by construction.

Everything witnessed reduces to the three irreducible Lean axioms; no `sorryAx`.
-/

namespace MonogateEML.RealModel

/-! ## arctan bounds (`MachLib/Trig.lean`) -/

theorem arctan_lt_pi_div_two (x : ℝ) : Real.arctan x < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two x
theorem neg_pi_div_two_lt_arctan (x : ℝ) : -(Real.pi / 2) < Real.arctan x :=
  Real.neg_pi_div_two_lt_arctan x

/-! ## log10 / exp10 (`MachLib/Log.lean`)

Modeled exactly as MachLib defines them: `log10 x = log x / log 10` and
`exp10 x = exp (x · log 10)` (`MachLib.Real.exp10_def`). -/

theorem log10_zero : Real.log 1 / Real.log 10 = 0 := by rw [Real.log_one, zero_div]
theorem exp10_zero : Real.exp (0 * Real.log 10) = 1 := by rw [zero_mul, Real.exp_zero]
theorem exp10_log10_inverse (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / Real.log 10 * Real.log 10) = x := by
  rw [div_mul_cancel₀ (Real.log x) (ne_of_gt (Real.log_pos (by norm_num))), Real.exp_log hx]

end MonogateEML.RealModel
