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

/-- **The witnessed Rolle theorem — grounds `MachLib.Real.rolle_ct` verbatim.** The machlib library now
carries a sound closed-interval Rolle `rolle_ct` (differentiability on `[a,b]`, i.e. `a ≤ c → c ≤ b`); this
theorem is its Mathlib ℝ model, statement-for-statement. Closed-interval differentiability gives continuity on
`[a,b]` (`HasDerivAt.continuousAt`), which is exactly the hypothesis the open-only `rolle` omits and Mathlib's
`exists_hasDerivAt_eq_zero` requires; then pick a derivative function by choice, apply Mathlib's Rolle, and
transport `f' c = 0` back to `HasDerivAt f 0 c` by uniqueness. -/
theorem rolle_witnessed (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfab : f a = f b)
    (hdiff : ∀ c : ℝ, a ≤ c → c ≤ b → ∃ f' : ℝ, HasDerivAt f f' c) :
    ∃ c : ℝ, a < c ∧ c < b ∧ HasDerivAt f 0 c := by
  -- Differentiability on the CLOSED interval gives continuity there (the hypothesis `rolle`
  -- omitted and `rolle_ct` supplies).
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    (hdiff x hx.1 hx.2).choose_spec.continuousAt.continuousWithinAt
  -- Pick a derivative function `F` from the pointwise existence (choice; ℝ is inhabited).
  have hex : ∀ x, x ∈ Ioo a b → ∃ f' : ℝ, HasDerivAt f f' x :=
    fun x hx => hdiff x (le_of_lt hx.1) (le_of_lt hx.2)
  choose! F hF using hex
  -- Mathlib's Rolle on the closed interval.
  obtain ⟨c, hc, hFc⟩ := exists_hasDerivAt_eq_zero hab hcont hfab hF
  refine ⟨c, hc.1, hc.2, ?_⟩
  -- `HasDerivAt f (F c) c` with `F c = 0` gives `HasDerivAt f 0 c`.
  have := hF c hc
  rwa [hFc] at this

/-! ## Tombstone — the retired unsound `rolle` is machine-checked FALSE

`MachLib` once carried an OPEN-interval Rolle (`axiom rolle`, differentiability on `(a,b)`
only, no endpoint continuity) that is **not a theorem of ℝ**; it was replaced by the sound
closed-interval `rolle_ct` (witnessed above) and retired. A `grep "axiom rolle\b"`-style
absence check for the unsound form rots the moment anything is renamed. The tombstone below
is the machine-checked replacement: the old statement's exact shape, proved FALSE over ℝ,
so its unsoundness is a `#check`-able fact that cannot silently drift back. -/

/-- The OLD, unsound open-interval Rolle statement (the retired `MachLib.Real.rolle`):
differentiability on the OPEN `(a,b)` only — no endpoint continuity — plus `f a = f b`,
concluding an interior stationary point. -/
def OldOpenRolle : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → f a = f b →
    (∀ c : ℝ, a < c → c < b → ∃ f', HasDerivAt f f' c) →
    ∃ c : ℝ, a < c ∧ c < b ∧ HasDerivAt f 0 c

/-- **Tombstone.** The old open-interval Rolle is FALSE over ℝ. Counterexample: `f = x` on
`(0,1)` pinned to `0` at both endpoints (discontinuous there), so `f 0 = f 1 = 0` and `f` is
differentiable on the OPEN interval with `f' ≡ 1 ≠ 0` — the exact continuity gap that made
`rolle` unsound and forced the closed-interval `rolle_ct`. Machine-checked, `sorryAx`-free. -/
theorem not_oldOpenRolle : ¬ OldOpenRolle := by
  intro H
  set f : ℝ → ℝ := fun x => if x = 0 ∨ x = 1 then 0 else x with hf
  have hfa : f 0 = 0 := by simp [hf]
  have hfb : f 1 = 0 := by simp [hf]
  have hderiv : ∀ c : ℝ, 0 < c → c < 1 → HasDerivAt f 1 c := by
    intro c hc0 hc1
    have hne : c ≠ 0 ∧ c ≠ 1 := ⟨ne_of_gt hc0, ne_of_lt hc1⟩
    have hopen : IsOpen {x : ℝ | x ≠ 0 ∧ x ≠ 1} := by
      rw [Set.setOf_and]; exact isOpen_ne.inter isOpen_ne
    have hev : f =ᶠ[nhds c] (fun x => x) := by
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ⟨hne.1, hne.2⟩) ?_
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp [hf, hx.1, hx.2]
    exact (hasDerivAt_id c).congr_of_eventuallyEq hev
  obtain ⟨c, hc0, hc1, hc⟩ :=
    H f 0 1 (by norm_num) (by rw [hfa, hfb]) (fun c h0 h1 => ⟨1, hderiv c h0 h1⟩)
  have : (0 : ℝ) = 1 := hc.unique (hderiv c hc0 hc1)
  norm_num at this

end MonogateEML.RealModel
