import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `MachLib.Real` soundness witness — the last Khovanskii-footprint axioms

Batch four. A cross-check of the `#print axioms` footprint of the Khovanskii results against the earlier
soundness batches turned up five axioms not yet witnessed — all in the MIXED exp/log barrier bound
(`eml_eval_boundedZeros_unconditional`); the pure-exponential explicit bound needs none of them. Two are
order/field one-liners; three are reciprocal/log analyticity facts the encoder's `1/x` and `log` nodes rest
on. This grounds four of the five against Mathlib's `ℝ` (`analytic_log_pos` — real-analyticity of `Real.log`
— is the one genuinely deep residual: Mathlib has `analyticAt_rexp` but no `Real.log` analyticity lemma, so
it needs the analytic inverse-function theorem; deferred).

`IsAnalyticOnReals f S` is mirrored by `AnalyticOnNhd ℝ f S`, `Ioi`/`Icc` by `Set.Ioi`/`Set.Icc`. Everything
here reduces to the three irreducible Lean axioms; no `sorryAx`.
-/

namespace MonogateEML.RealModel

open Set

/-! ## Order / field (`MachLib/Forge.lean`, `MachLib/Linarith.lean`) -/

/-- `MachLib.Real.mul_lt_mul_of_pos_right`. -/
theorem mul_lt_mul_of_pos_right {a b c : ℝ} (h : a < b) (hc : 0 < c) : a * c < b * c :=
  _root_.mul_lt_mul_of_pos_right h hc

/-- `MachLib.Real.one_div_pos_of_pos`. -/
theorem one_div_pos_of_pos {b : ℝ} (hb : 0 < b) : 0 < 1 / b := by positivity

/-! ## Reciprocal analyticity + the nonzero-neighbourhood fact -/

/-- `MachLib.analytic_one_div_pos` — `1/x` is analytic on `(0, ∞)` (`analyticAt_inv`). -/
theorem analytic_one_div_pos : AnalyticOnNhd ℝ (fun x : ℝ => 1 / x) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have h : AnalyticAt ℝ (fun x : ℝ => x⁻¹) x := analyticAt_inv (ne_of_gt hx)
  simpa only [one_div] using h

/-- `MachLib.analytic_ne_zero_nbhd` — an analytic (hence continuous) function nonzero at an interior point is
nonzero on an open subinterval of `[a,b]` around it. Continuity from `AnalyticOnNhd.continuousAt`, then the
open set `{G ≠ 0}` yields an `Ioo` neighbourhood clipped into `[a,b]` by `max`/`min`. -/
theorem analytic_ne_zero_nbhd (G : ℝ → ℝ) (a b x : ℝ)
    (hG : AnalyticOnNhd ℝ G (Set.Icc a b)) (hax : a < x) (hxb : x < b) (hGx : G x ≠ 0) :
    ∃ a' b' : ℝ, a ≤ a' ∧ b' ≤ b ∧ a' < x ∧ x < b' ∧ ∀ y, a' < y → y < b' → G y ≠ 0 := by
  have hcont : ContinuousAt G x := (hG x ⟨le_of_lt hax, le_of_lt hxb⟩).continuousAt
  have hmem : {y | G y ≠ 0} ∈ nhds x := hcont.eventually_ne hGx
  obtain ⟨p, q, hxpq, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hmem
  refine ⟨max a p, min b q, le_max_left a p, min_le_left b q,
    max_lt hax hxpq.1, lt_min hxb hxpq.2, fun y hy1 hy2 => ?_⟩
  exact hsub ⟨(le_max_right a p).trans_lt hy1, hy2.trans_le (min_le_right b q)⟩

/-! ## Log analyticity (deferred — needs the analytic inverse-function theorem)

`analytic_log_pos : AnalyticOnNhd ℝ Real.log (Set.Ioi 0)`. `Real.log` is real-analytic on `(0,∞)` (it is the
inverse of the entire `Real.exp`, whose derivative never vanishes), but Mathlib exposes no `Real.log`
analyticity lemma, so this witness would route through the analytic inverse-function theorem. Left for a
focused follow-up; the other four residuals are discharged above. -/

end MonogateEML.RealModel
