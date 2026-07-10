import Mathlib.Analysis.Calculus.MeanValue

/-!
# `MachLib.Real` soundness witness — Rolle's theorem

The final analytic axiom of the Khovanskii/EML foundation: `MachLib.Real.rolle`
(`machlib/foundations/MachLib/Rolle.lean`). Every zero-count bound in that library —
`zero_count_bound_by_deriv`, the iterated-exponential tower, the mixed exp/log EML
barrier bound — bottoms out at this single analytic input, so grounding it against
Mathlib's ℝ closes the analysis loop.

## A faithfulness note on the hypotheses

Mathlib's Rolle (`exists_hasDerivAt_eq_zero`) requires **`ContinuousOn f (Icc a b)`** — continuity on the
CLOSED interval. The `MachLib.Real.rolle` axiom, as currently stated, requires only differentiability on the
OPEN interval `(a,b)` (`∀ c ∈ (a,b), ∃ f', HasDerivAt f f' c`) plus `f a = f b`, with **no** continuity
hypothesis. Under the natural interpretation `Real := ℝ`, `HasDerivAt := Mathlib.HasDerivAt`, the axiom is
therefore **not** a theorem of ℝ as written: take `f x = x` on `(0,1)` with `f 0 = f 1 = 0` (discontinuous at
the endpoints). It is differentiable on `(0,1)` with `f' ≡ 1 ≠ 0`, and `f 0 = f 1`, yet has no interior point
with `f' = 0`. This is exactly why the axiom is absent from the earlier soundness batches — it needs the
continuity hypothesis to be grounded.

The witness below adds that hypothesis (`hcont`) and discharges everything else from Mathlib. Every place the
library *applies* `rolle`, the function is a Pfaffian function (a polynomial evaluated along a coherent chain),
which is differentiable — hence continuous — on all of ℝ, so `ContinuousOn f (Icc a b)` always holds at the
call sites. The honest reading: `rolle` is sound *as used*, and a faithfully-grounded restatement should carry
`ContinuousOn f (Icc a b)` (or a differentiable-on-a-neighborhood hypothesis that implies it). `sorryAx`-free.
-/

namespace MonogateEML.RealModel

open Set

/-- **The witnessed Rolle theorem.** The `MachLib.Real.rolle` statement — verbatim in the ∃-derivative and
`HasDerivAt f 0 c` conclusion shape — with the one hypothesis Mathlib's Rolle needs and the axiom omits:
`ContinuousOn f (Icc a b)`. Discharged from `exists_hasDerivAt_eq_zero`: pick a derivative function by choice
from the pointwise existence, apply Mathlib's Rolle, and transport `f' c = 0` back to `HasDerivAt f 0 c` by
uniqueness of the derivative. -/
theorem rolle_witnessed (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hfab : f a = f b)
    (hdiff : ∀ c : ℝ, a < c → c < b → ∃ f' : ℝ, HasDerivAt f f' c) :
    ∃ c : ℝ, a < c ∧ c < b ∧ HasDerivAt f 0 c := by
  -- Pick a derivative function `F` from the pointwise existence (choice; ℝ is inhabited).
  have hex : ∀ x, x ∈ Ioo a b → ∃ f' : ℝ, HasDerivAt f f' x :=
    fun x hx => hdiff x hx.1 hx.2
  choose! F hF using hex
  -- Mathlib's Rolle on the closed interval.
  obtain ⟨c, hc, hFc⟩ := exists_hasDerivAt_eq_zero hab hcont hfab hF
  refine ⟨c, hc.1, hc.2, ?_⟩
  -- `HasDerivAt f (F c) c` with `F c = 0` gives `HasDerivAt f 0 c`.
  have := hF c hc
  rwa [hFc] at this

end MonogateEML.RealModel
