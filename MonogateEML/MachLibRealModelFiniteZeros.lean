import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Order.Compact

/-!
# `MachLib.Real` soundness witness — the analytic finite-zeros theorem

The one *substantive* deferred axiom from `MachLib/AnalyticFiniteZeros.lean`:
`analytic_finite_zeros_compact` — a real-analytic function on a compact interval
that is not identically zero has finitely many zeros there. Unlike the field /
differentiation / closure axioms (which are one-liners in Mathlib), this needs a
genuine proof from Mathlib's isolated-zeros / identity-theorem machinery. Proving
it against Mathlib's `ℝ` + `AnalyticOnNhd` retires it as an axiom.

Statement mirrors the MachLib axiom verbatim in shape, including the `RealSetFinite`
conclusion (a bound on the length of `Nodup` lists of zeros — MachLib's
Mathlib-free finiteness predicate). Reduces to the three Lean axioms; no `sorryAx`.

Proof: the identity-theorem dichotomy (`eqOn_zero_or_eventually_ne_zero_of_preconnected`)
says `f ≡ 0` on `[a,b]` (excluded by the non-vanishing hypothesis) or the zeros are
`codiscreteWithin [a,b]` — i.e. no point of `[a,b]` is an accumulation point of the
zero set `Z`. Accumulation points of `Z` lie in `closure Z ⊆ [a,b]`, so `Z` has
none anywhere ⇒ `Z` is closed and (sub-space) discrete ⇒ bounded ∩ closed in the
proper space `ℝ` ⇒ finite. A `Nodup` list of `Z`'s elements is then bounded by
`|Z.toFinset|`.
-/

namespace MonogateEML.RealModel

open Filter Topology Set

theorem analytic_finite_zeros_compact (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b))
    (hne : ∃ x : ℝ, a < x ∧ x < b ∧ f x ≠ 0) :
    ∃ n : ℕ, ∀ l : List ℝ, l.Nodup →
      (∀ x ∈ l, (a ≤ x ∧ x ≤ b) ∧ f x = 0) → l.length ≤ n := by
  set Z : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x = 0} with hZdef
  have hZsub : Z ⊆ Set.Icc a b := fun _ hx => hx.1
  -- Step 1: the zero set is finite.
  have hZfin : Z.Finite := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Icc with heq | hcod
    · -- f ≡ 0 on [a,b] contradicts the non-vanishing point in (a,b).
      exfalso
      obtain ⟨x, hxa, hxb, hfx⟩ := hne
      exact hfx (heq ⟨le_of_lt hxa, le_of_lt hxb⟩)
    · -- zeros are codiscrete: no point of [a,b] accumulates them.
      rw [eventually_iff, mem_codiscreteWithin_accPt] at hcod
      have hZeq : Set.Icc a b \ {x | f x ≠ 0} = Z := by
        ext x; simp only [hZdef, mem_diff, mem_setOf_eq, not_not]
      rw [hZeq] at hcod
      -- extend "no accumulation in [a,b]" to "no accumulation anywhere".
      have hall : ∀ x, ¬ AccPt x (𝓟 Z) := by
        intro x hacc
        have hxcl : x ∈ closure Z := mem_closure_iff_clusterPt.mpr hacc.clusterPt
        exact hcod x (closure_minimal hZsub isClosed_Icc hxcl) hacc
      have hdisj : ∀ x, Disjoint (𝓝[≠] x) (𝓟 Z) :=
        fun x => disjoint_iff.mpr (not_neBot.mp (hall x))
      obtain ⟨hZclosed, hZdiscrete⟩ := isClosed_and_discrete_iff.mpr hdisj
      haveI := hZdiscrete
      have hfin := Metric.finite_isBounded_inter_isClosed
        (K := Set.Icc a b) isCompact_Icc.isBounded hZclosed
      rwa [Set.inter_eq_right.mpr hZsub] at hfin
  -- Step 2: a Nodup list of zeros is bounded by |Z.toFinset|.
  refine ⟨hZfin.toFinset.card, fun l hnodup hmem => ?_⟩
  have hsub : l.toFinset ⊆ hZfin.toFinset := by
    intro y hy
    rw [Set.Finite.mem_toFinset]
    have hy' := hmem y (List.mem_toFinset.mp hy)
    exact ⟨Set.mem_Icc.mpr hy'.1, hy'.2⟩
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ hZfin.toFinset.card := Finset.card_le_card hsub

end MonogateEML.RealModel
