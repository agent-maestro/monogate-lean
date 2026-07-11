import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Basic

/-!
# Witness: `Real.log` is real-analytic on `(0, ∞)`

Grounds MachLib's `analytic_log_pos` axiom — `IsAnalyticOnReals Real.log (Ioi 0)` — against
Mathlib's genuine `ℝ`, closing the last `witnessGap` in `AxiomWitnessBridge`.

Mathlib (pinned `v4.14.0`) has **no** direct real-log analyticity lemma (`analyticOnNhd_log` /
`analyticAt_log` are absent, real *and* complex-of-real). It does have ℂ-log analyticity on the
slit plane (`analyticAt_clog`), and that is enough: on the positive reals

  `Real.log t = (Complex.log ↑t).re`   (`Complex.log_ofReal_re`, an identity for all real `t`),

and the right-hand side is a composition of three `ℝ`-analytic maps —

  `ofRealCLM`  (a continuous ℝ-linear map, hence analytic),
  `Complex.log`  (ℂ-analytic on the slit plane `analyticAt_clog`, restricted to ℝ-scalars),
  `reCLM`  (a continuous ℝ-linear map, hence analytic).

For `t > 0`, `↑t` lies in the slit plane (`Complex.ofReal_mem_slitPlane`), so the middle factor is
analytic exactly on `(0, ∞)`. Since the identity holds everywhere, the `congr` to `Real.log` is
global, not merely local.

This is a genuinely Mathlib-missing fact (unlike the transcendence-degree machinery, which current
Mathlib has since absorbed) — a candidate upstream contribution in its own right; see the
accompanying standalone `Mathlib`-style statement.
-/

open Complex Set

namespace MonogateEML.RealModel

/-- `Real.log` is real-analytic on the open ray `(0, ∞)`. Witness for MachLib's `analytic_log_pos`. -/
theorem analyticOnNhd_real_log_Ioi : AnalyticOnNhd ℝ Real.log (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  -- the composite `t ↦ (Complex.log ↑t).re` is ℝ-analytic at x (re ∘ clog ∘ ofReal)
  have hcomp : AnalyticAt ℝ (fun t : ℝ => (Complex.log (t : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp
      (((analyticAt_clog
          (Complex.ofReal_mem_slitPlane.mpr hx0)).restrictScalars).comp
        (Complex.ofRealCLM.analyticAt x))
  -- and it equals `Real.log` everywhere, so `Real.log` is analytic at x
  exact hcomp.congr (Filter.Eventually.of_forall fun t => (Complex.log_ofReal_re t))

end MonogateEML.RealModel
