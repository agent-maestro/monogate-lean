/-
Copyright (c) 2026 Monogate Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monogate Research
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Real analyticity of `Real.log`

`Real.log` is real-analytic away from `0`. This is the real-variable analogue of the complex results
in `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean` (`analyticAt_clog`, `AnalyticAt.clog`,
…), and the analytic-strength companion of `Real.differentiableAt_log`.

## Main results

* `Real.analyticAt_log`: `Real.log` is analytic at every `x ≠ 0`.
* `Real.analyticOnNhd_log_Ioi` / `Real.analyticOnNhd_log_Iio` / `Real.analyticOnNhd_log_compl_zero`:
  `Real.log` is analytic on `(0, ∞)`, on `(-∞, 0)`, and on `{0}ᶜ`.
* `AnalyticAt.log`, `AnalyticWithinAt.log`, `AnalyticOnNhd.log`, `AnalyticOn.log`: composition lemmas
  mirroring the `clog` API.

## Implementation notes

The proof factors through the complex logarithm. For every real `t`,
`Real.log t = (Complex.log ↑t).re` (`Complex.log_ofReal_re`), and on the positive reals the
right-hand side is a composition of `ℝ`-analytic maps: `Complex.ofRealCLM` (a continuous ℝ-linear
map), `Complex.log` (ℂ-analytic on the slit plane, `analyticAt_clog`, with scalars restricted to
`ℝ`), and `Complex.reCLM`. For `t > 0`, `↑t` lies in the slit plane
(`Complex.ofReal_mem_slitPlane`), giving analyticity on `(0, ∞)`; the negative reals reduce to the
positive case via `Real.log (-t) = Real.log t` (`Real.log_neg_eq_log`).
-/

open Complex Set

namespace Real

/-- `Real.log` is real-analytic on the positive reals. -/
theorem analyticOnNhd_log_Ioi : AnalyticOnNhd ℝ Real.log (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  -- `t ↦ (Complex.log ↑t).re` is ℝ-analytic at `x` (`re ∘ clog ∘ ofReal`)
  have hcomp : AnalyticAt ℝ (fun t : ℝ => (Complex.log (t : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp
      (((analyticAt_clog (Complex.ofReal_mem_slitPlane.mpr hx0)).restrictScalars).comp
        (Complex.ofRealCLM.analyticAt x))
  -- and it equals `Real.log` everywhere
  exact hcomp.congr (Filter.Eventually.of_forall fun t => Complex.log_ofReal_re t)

/-- `Real.log` is real-analytic at every nonzero point. -/
theorem analyticAt_log {x : ℝ} (hx : x ≠ 0) : AnalyticAt ℝ Real.log x := by
  rcases hx.lt_or_lt with hneg | hpos
  · -- `x < 0`: reduce to the positive case via `Real.log (-t) = Real.log t`
    have h0 : (0 : ℝ) < -x := by linarith
    exact ((analyticOnNhd_log_Ioi _ h0).comp analyticAt_id.neg).congr
      (Filter.Eventually.of_forall fun t => Real.log_neg_eq_log t)
  · exact analyticOnNhd_log_Ioi _ hpos

/-- `Real.log` is real-analytic on the negative reals. -/
theorem analyticOnNhd_log_Iio : AnalyticOnNhd ℝ Real.log (Set.Iio (0 : ℝ)) :=
  fun _ hx => analyticAt_log (ne_of_lt hx)

/-- `Real.log` is real-analytic away from `0`. -/
theorem analyticOnNhd_log_compl_zero : AnalyticOnNhd ℝ Real.log {(0 : ℝ)}ᶜ :=
  fun _ hx => analyticAt_log (by simpa using hx)

end Real

section Composition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {s : Set E}

theorem AnalyticAt.log (fa : AnalyticAt ℝ f x) (h : f x ≠ 0) :
    AnalyticAt ℝ (fun z ↦ Real.log (f z)) x :=
  (Real.analyticAt_log h).comp fa

theorem AnalyticWithinAt.log (fa : AnalyticWithinAt ℝ f s x) (h : f x ≠ 0) :
    AnalyticWithinAt ℝ (fun z ↦ Real.log (f z)) s x :=
  (Real.analyticAt_log h).comp_analyticWithinAt fa

theorem AnalyticOnNhd.log (fs : AnalyticOnNhd ℝ f s) (h : ∀ z ∈ s, f z ≠ 0) :
    AnalyticOnNhd ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (Real.analyticAt_log (h z n)).comp (fs z n)

theorem AnalyticOn.log (fs : AnalyticOn ℝ f s) (h : ∀ z ∈ s, f z ≠ 0) :
    AnalyticOn ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (Real.analyticAt_log (h z n)).analyticWithinAt.comp (fs z n) (Set.mapsTo_univ f s)

end Composition
