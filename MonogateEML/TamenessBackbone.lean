import MachLib.IterExpDepthNBoundUncond
import MachLib.PfaffianGeneralBoundUncond
import MachLib.ExpPolyEffectiveBound
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# The tameness backbone — monogate's finiteness, in o-minimal vocabulary

The o-minimality → *tameness of the string landscape* program (Bakker–Klingler–Tsimerman on
definability of period maps in `ℝ_{an,exp}`; Bakker–Grimm–Schnell–Tsimerman on finiteness of
self-dual flux vacua; Grimm, arXiv:2112.08383 / 2311.09295) rests on **o-minimality of `ℝ_exp`**,
whose finiteness backbone is the Khovanskii/Pfaffian zero-count theorem. Every step of that chain is
pen-and-paper, and Mathlib has none of it (no Pfaffian, no Khovanskii, no o-minimality).

Monogate *does* have the finiteness backbone, machine-checked and axiom-audited:
`MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional` — an iterated-exponential chain of any
depth, not identically zero on `(a,b)`, has finitely many zeros there. But it is phrased in MachLib's
Mathlib-free idiom: *every `Nodup` list of zeros has length `≤ N`* (`MachLib` cannot mention
`Set.Finite`).

This file is the **first piece of that backbone restated in the vocabulary the tameness literature
actually uses** — `Set.Finite` of the zero locus — bridging the two with a single general lemma
(a bounded `Nodup`-list length forces finiteness). It imports the MachLib theorem and Mathlib side by
side (the same co-import the certcom soundness witness uses), so the resulting statement carries
MachLib's audited footprint (`rolle_ct`-based) plus Lean/Mathlib's core.

**Honest scope — the distance to "the landscape is tame" (three named layers):**
1. this is the zero-count *finiteness ingredient*, not o-minimality of `ℝ_exp` itself (Wilkie:
   model-completeness + cell decomposition — not formalized here);
2. the tameness program needs `ℝ_{an,exp}` — the restricted-*analytic* part too — while this is the
   exp/Pfaffian fragment only;
3. landscape finiteness is downstream of *definability of period maps* + o-minimal finiteness, which
   this does not touch.
It is the first machine-checked brick of that edifice, not the edifice.
-/

open MachLib MachLib.IterExpDepthN MachLib.MultiPolyMod
open MachLib.PfaffianChainMod MachLib.PfaffianGeneralReduce
open MachLib.SingleExpKhovanskii MachLib.SingleExpKhovanskii.ExpPoly

namespace MonogateEML.Tameness

/-- **Bounded-`Nodup`-length ⟹ `Set.Finite`.** If some `N` bounds the length of every `Nodup` list
drawn from a set `s`, then `s` is finite. This is the one general lemma that translates MachLib's
Mathlib-free finiteness idiom into Mathlib's `Set.Finite`. -/
theorem finite_of_nodup_length_bound {α : Type*} {s : Set α} {N : ℕ}
    (h : ∀ l : List α, l.Nodup → (∀ x ∈ l, x ∈ s) → l.length ≤ N) : s.Finite := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨t, hts, hcard⟩ := hinf.exists_subset_card_eq (N + 1)
  have hlen := h t.toList t.nodup_toList (fun z hz => hts (Finset.mem_coe.mpr (Finset.mem_toList.mp hz)))
  rw [Finset.length_toList, hcard] at hlen
  omega

/-- **The exp-tower finiteness, in o-minimal vocabulary.** For an iterated-exponential chain of any
depth `m+2` capped by a polynomial `p`, if it is not identically zero on `(a,b)` then its zero set on
`(a,b)` is **`Set.Finite`** — the exact shape the o-minimality/tameness finiteness theorems are stated
in. This is `chainN_khovanskii_bound_unconditional` (an AxiomLedger-pinned, `rolle_ct`-only headline)
routed through `finite_of_nodup_length_bound`. -/
theorem chainN_zero_set_finite (m : ℕ) (p : MultiPoly (m + 2)) (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z ≠ 0) :
    {x : MachLib.Real | a < x ∧ x < b ∧ (chainNFn (m + 2) p).eval x = 0}.Finite := by
  obtain ⟨N, hN⟩ := chainN_khovanskii_bound_unconditional m p a b hab hne
  exact finite_of_nodup_length_bound (N := N) (fun l hnd hmem => hN l hnd hmem)

/-- **General Pfaffian finiteness, in o-minimal vocabulary.** For any positive, coherent, exp-type
Pfaffian chain `c` and any polynomial-in-the-chain `p` not identically zero on `(a,b)`, the zero set
is **`Set.Finite`**. This is `pfaffian_khovanskii_bound_gen_uncond` — Khovanskii's finiteness for the
Pfaffian functions that o-minimality of `ℝ_exp` is built on — routed through the same bridge lemma.
The `IsExpChain` / `IsCoherentOn` / positivity hypotheses are monogate's honest scope: the exp-tower
slice, not fully general Pfaffian. -/
theorem pfaffian_zero_set_finite (a b : MachLib.Real) (hab : a < b)
    (M : ℕ) (c : PfaffianChain (M + 2)) (hexp : IsExpChain c) (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (p : MultiPoly (M + 2))
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    {x : MachLib.Real | a < x ∧ x < b ∧ (pfaffianChainFn c p).eval x = 0}.Finite := by
  obtain ⟨N, hN⟩ := pfaffian_khovanskii_bound_gen_uncond a b hab M c hexp hcoh hpos p hne
  exact finite_of_nodup_length_bound (N := N) (fun l hnd hmem => hN l hnd hmem)

/-! ## The *effective* count, in `Set.ncard` vocabulary

`finite_of_nodup_length_bound` throws the bound away (it yields only `Set.Finite`). Monogate's edge is
**effectiveness** — an explicit *number*. This section carries the bound through to `Set.ncard`, the
exact cardinality shape the tameness/counting literature uses, so the just-proven single-exp effective
bound (`expPoly_effective_bound`, `rolle_ct`-only) reads as an explicit `ncard ≤ …`. -/

/-- **Effective bridge.** The same bounded-`Nodup`-length hypothesis that gives `Set.Finite` gives the
explicit cardinality bound `s.ncard ≤ N`. -/
theorem ncard_le_of_nodup_length_bound {α : Type*} {s : Set α} {N : ℕ}
    (h : ∀ l : List α, l.Nodup → (∀ x ∈ l, x ∈ s) → l.length ≤ N) : s.ncard ≤ N := by
  have hfin : s.Finite := finite_of_nodup_length_bound h
  rw [Set.ncard_eq_toFinset_card s hfin]
  have hlist := h hfin.toFinset.toList hfin.toFinset.nodup_toList
    (fun x hx => (hfin.mem_toFinset).mp (Finset.mem_toList.mp hx))
  rwa [Finset.length_toList] at hlist

/-- **The single-exp effective count, in o-minimal vocabulary.** The real zero set of a non-vanishing
`ExpPoly` on `(a,b)` has `Set.ncard ≤ length + ΣsimplifiedDeg` — the explicit cardinality
`expPoly_effective_bound` gives, now in the `Set.ncard` shape the counting literature uses. This is the
*effective* refinement of a `Set.Finite` statement: not just finite, but bounded by an explicit number.
`rolle_ct`-only. -/
theorem expPoly_zero_set_ncard_le (ep : ExpPoly) (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ x, a < x ∧ x < b ∧ ep.eval x ≠ 0) :
    {x : MachLib.Real | a < x ∧ x < b ∧ ep.eval x = 0}.ncard
      ≤ ep.coeffs.length + sumSimplifiedDegrees ep.coeffs := by
  apply ncard_le_of_nodup_length_bound
  intro l hnd hmem
  exact expPoly_effective_bound ep a b hab hne l hnd (fun z hz => hmem z hz)

/-- **The closed-form effective count, in o-minimal vocabulary.** If every coefficient has degree `≤ D`
and there are `K+1` exponential modes, the real zero set has `Set.ncard ≤ (K+1)·(D+1)` — the explicit
`(modes)·(degree+1)` count the flux counting conjectures want, in Mathlib's cardinality vocabulary. -/
theorem expPoly_zero_set_ncard_le_uniform (ep : ExpPoly) (D : ℕ)
    (hdeg : ∀ p ∈ ep.coeffs, MachLib.PolynomialRootCount.degreeUpper p ≤ D)
    (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ x, a < x ∧ x < b ∧ ep.eval x ≠ 0) :
    {x : MachLib.Real | a < x ∧ x < b ∧ ep.eval x = 0}.ncard ≤ ep.coeffs.length * (D + 1) := by
  apply ncard_le_of_nodup_length_bound
  intro l hnd hmem
  exact expPoly_effective_bound_uniform ep D hdeg a b hab hne l hnd (fun z hz => hmem z hz)

end MonogateEML.Tameness
