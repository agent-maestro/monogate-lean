import Mathlib.RingTheory.AlgebraicIndependent
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Adjoin
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Real.Basic

/-!
# Transcendence-degree exchange (Steinitz for the algebraic matroid)

This builds the theorem Mathlib is **missing** — the transcendence analogue of the linear
Steinitz exchange (`Basis.le_span` : an independent family is bounded by any spanning
family). It is the one lemma that closes `(3a)` (the trans-degree bound `H` that
`MachLibChainAlgDep.algDep_of_bounded_trdeg` consumes), and it is a clean, self-contained
candidate Mathlib contribution in its own right (the pinned Mathlib rev has NO
transcendence-degree file at all — no `Transcendental.lean`, no adjoin-exchange helper, only
the infinite-cardinal `IsTranscendenceBasis.lift_cardinalMk_eq_max_lift`, useless for a
finite bound).

## What is PROVEN here (the crux)

`isAlgebraic_adjoin_singleton_exchange` — the **symmetric one-element exchange**:

    a algebraic over R⟨b⟩,  a transcendental over R  ⟹  b algebraic over R⟨a⟩.

This is the heart of the algebraic-matroid exchange axiom. Proof is the *slick* route,
not the ~150-line bivariate-`MvPolynomial` slog:

  contrapositive + symmetry of algebraic independence. Suppose `b` were transcendental
  over `R⟨a⟩`. With `a` transcendental over `R`, `option_iff` makes `{a, b}`
  algebraically independent; independence is symmetric under the index swap
  `Equiv.swap none (some 0)`, so `{b, a}` is independent too, i.e. `a` is transcendental
  over `R⟨b⟩` — contradicting the hypothesis that `a` is algebraic over `R⟨b⟩`. ∎

Machine-checked, `sorryAx`-free (`#print axioms` = `propext, Classical.choice, Quot.sound`,
the three ambient Mathlib axioms only). Because the statement is generic in the base
`CommRing R`, it *already relativises*: instantiating `R := ↥(adjoin R₀ S)` gives the
exchange over any base set `S` (the form the finite-bound induction consumes), modulo the
`adjoin`-tower rewrite `adjoin R₀ (S ∪ {x}) ≃ adjoin (adjoin R₀ S) {x}`.

## Remaining plan toward the finite bound + (3a)

1. **Relativise** `isAlgebraic_adjoin_singleton_exchange` over a base set `S`.
   **DONE — for free** (`isAlgebraic_adjoin_singleton_exchange_over_adjoin`, below): the
   exchange is generic in the base `CommRing`, so instantiating it at `↥(adjoin R S)`
   carries the base-set form with no `restrictScalars` burden *at the exchange site*.
2. **The finite bound** (target below) by exchange induction on a finite spanning family
   (van der Waerden): maintain "A is algebraic over `R⟨v₀,…,v_{r-1}, w_r,…⟩`"; each new
   `vᵣ`, transcendental over the `v`-part but algebraic over the whole, forces (via the
   exchange) some remaining `w` to be swappable ⇒ `r < k` at each step ⇒ `#v ≤ #w`.

       theorem AlgebraicIndependent.card_le_of_isAlgebraic
           (hv : AlgebraicIndependent R v) (hw : Algebra.IsAlgebraic (adjoin R (range w)) A) :
           #ι ≤ #κ

   Remaining shape (the algebraic content is discharged — `isAlgebraic_adjoin_insert_replace`
   below IS the swap; this is now pure finite bookkeeping): induct on the number of `v`'s
   placed, maintaining a spanning `Finset T` that contains the placed `v`'s. Each step: the
   next `vᵣ` is transcendental over `R⟨placed⟩` (independence) but algebraic over `R⟨T⟩`, so
   a `Nat.find`-style "first index where `vᵣ` turns algebraic" picks a displaceable `t ∈ T`;
   `isAlgebraic_adjoin_insert_replace` swaps `vᵣ` in for `t`, and `Algebra.IsAlgebraic.trans`
   re-establishes that `A` is algebraic over the new `T`. Distinctness of the placed `v`'s
   (independence ⇒ injective) with `card T ≤ q` gives `p ≤ q`.

   **Setting:** state the bound over `[Field F] [Field E]` (Mathlib's whole finite-trdeg /
   transcendence-basis theory lives there — `AlgebraicIndependent.lean:459`, and
   `Algebra.IsAlgebraic.trans` needs the domain structure). The exchange/replace lemmas here
   are general `CommRing` and specialise into the field setting unchanged. The target `H` is
   precisely the hypothesis `algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded`
   (and `MachLibChainAlgDep.algDep_of_bounded_trdeg`) already consume.
3. **(3a) corollary + discharge** `algDep_of_bounded_trdeg`'s `H`, closing
   `chain_algebraic_dependence` (mod step 3b, the analytic-function domain for the exps).

## Status (2026-07-10) — the finite bound is COMPLETE

`card_le_of_isAlgebraic_span` (bottom of file) is **proven and verified `sorryAx`-free**: an
algebraically independent `v : Fin p → E` is bounded by any spanning finset,
`p ≤ T.card` (E algebraic over `F(T)`). The full chain, every step `sorryAx`-free:

  * `isAlgebraic_adjoin_singleton_exchange` (crux, slick contrapositive) → `…_over_adjoin`
    (base-set relativisation, free) → `isAlgebraic_adjoin_insert_replace` (the swap).
  * `exists_displaceable` — the pigeonhole picking which generator each new element displaces.
  * `isAlgebraic_algebraAdjoin_iff_intermediateField` — the **subring ↔ subfield bridge**, the
    one piece Mathlib lacked, built by constructing
    `IsFractionRing ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X)` from scratch
    (`IntermediateField.mem_adjoin_iff` gives the surjectivity field). This is why the respan,
    which needs `Algebra.IsAlgebraic.trans` over *fields*, can consume the exchange's
    *subring*-level output.
  * `respan` — the swapped generating set still spans (single-element join `K⟮t⟯`,
    `Algebra.IsAlgebraic.trans`).
  * `transcendental_last_of_algebraicIndependent` — new element transcendental over the placed
    prefix (`finSuccEquivLast` + `option_iff`).
  * The van der Waerden invariant induction (base fixed at `F`, place each `vᵣ` into a
    same-card spanning `Finset`) + the injectivity count assemble these into the bound.

**Remaining toward `chain_algebraic_dependence`:** the `(3a)` corollary — feed
`card_le_of_isAlgebraic_span` into `MachLibChainAlgDep.algDep_of_bounded_trdeg`'s `H` (a
`Finset`/`Fin` repackaging) — then step `(3b)`, the analytic-function domain for the actual
iterated exponentials. The transcendence-degree machinery itself is now done.
-/

open Algebra

/-- **Transcendence-degree exchange (Steinitz for the algebraic matroid) — PROVEN.**

If `a` is algebraic over `R⟨b⟩` and `a` is transcendental over `R`, then `b` is algebraic
over `R⟨a⟩`. This is the symmetric one-element exchange underlying the algebraic matroid; it
is exactly the transcendence analogue of the linear Steinitz exchange, and Mathlib (this rev)
has no form of it.

Proof: contrapositive. If `b` were transcendental over `R⟨a⟩`, then — `a` being
transcendental over `R` — `AlgebraicIndependent.option_iff` makes the pair `{a, b}`
algebraically independent. Independence is invariant under reindexing (`Equiv.swap`), so the
pair `{b, a}` is independent as well; reading `option_iff` the other way, `a` is then
transcendental over `R⟨b⟩`, contradicting the algebraicity hypothesis `hb`. -/
theorem isAlgebraic_adjoin_singleton_exchange
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {a b : A}
    (hb : IsAlgebraic (Algebra.adjoin R {b}) a)
    (ha : Transcendental R a) :
    IsAlgebraic (Algebra.adjoin R {a}) b := by
  by_contra hcon
  -- `a` alone is independent over `R`.
  have hia : AlgebraicIndependent R ![a] := algebraicIndependent_iff_transcendental.mpr ha
  have hrng : Set.range ![a] = {a} := by
    ext y; constructor
    · rintro ⟨i, rfl⟩; fin_cases i; rfl
    · rintro rfl; exact ⟨0, rfl⟩
  -- extend by `b`: `b` transcendental over `R⟨a⟩` (= ¬ hcon) makes `{a, b}` independent.
  have hpair : AlgebraicIndependent R (fun o : Option (Fin 1) => o.elim b ![a]) := by
    rw [hia.option_iff, hrng]; exact hcon
  -- independence is symmetric: swap the two indices to get `{b, a}` independent.
  have hcomp : (fun o : Option (Fin 1) => o.elim a ![b]) ∘ (Equiv.swap none (some 0))
             = (fun o : Option (Fin 1) => o.elim b ![a]) := by
    funext o
    rcases o with _ | i
    · simp [Function.comp_apply, Equiv.swap_apply_left]
    · rw [Subsingleton.elim i (0 : Fin 1)]
      simp [Function.comp_apply, Equiv.swap_apply_right]
  have hpair' : AlgebraicIndependent R (fun o : Option (Fin 1) => o.elim a ![b]) :=
    (algebraicIndependent_equiv' (Equiv.swap none (some 0)) hcomp).mp hpair
  -- read `option_iff` the other way: `a` transcendental over `R⟨b⟩`.
  have htrb : Transcendental R b := by
    have h := hpair'.transcendental (some 0); simpa using h
  have hib : AlgebraicIndependent R ![b] := algebraicIndependent_iff_transcendental.mpr htrb
  have hrngb : Set.range ![b] = {b} := by
    ext y; constructor
    · rintro ⟨i, rfl⟩; fin_cases i; rfl
    · rintro rfl; exact ⟨0, rfl⟩
  have h0 : Transcendental (Algebra.adjoin R (Set.range ![b])) a := (hib.option_iff a).mp hpair'
  rw [hrngb] at h0
  -- contradiction: `a` is both algebraic (`hb`) and transcendental (`h0`) over `R⟨b⟩`.
  exact h0 hb

/-- **Base-set relativisation of the exchange — FREE.** The exchange over a base *set* `S`
(the form the finite-bound induction consumes): if `a` is algebraic over `R⟨S⟩⟨b⟩` and
transcendental over `R⟨S⟩`, then `b` is algebraic over `R⟨S⟩⟨a⟩`.

Because `isAlgebraic_adjoin_singleton_exchange` is generic in the base `CommRing`, this is
just that lemma instantiated at base ring `K := ↥(Algebra.adjoin R S)` — the subalgebra's
`CommRing`/`Algebra` instances carry it with NO extra proof and NO `restrictScalars` burden
at the exchange site (the tower rewrites `adjoin R (S ∪ {x}) ≃ adjoin (adjoin R S) {x}` are
needed only where the induction threads the growing generating set, not here). Verified
`sorryAx`-free. -/
theorem isAlgebraic_adjoin_singleton_exchange_over_adjoin
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Set A) {a b : A}
    (hb : IsAlgebraic (Algebra.adjoin (Algebra.adjoin R S) {b}) a)
    (ha : Transcendental (Algebra.adjoin R S) a) :
    IsAlgebraic (Algebra.adjoin (Algebra.adjoin R S) {a}) b :=
  isAlgebraic_adjoin_singleton_exchange hb ha

/-- **The `replace` step — the exchange lifted to a generating set.** If `a` is algebraic
over `R⟨insert wq s⟩` but transcendental over `R⟨s⟩`, then the generator `wq` may be
*displaced* by `a`: `wq` is algebraic over `R⟨insert a s⟩`. This is the single swap the
van der Waerden finite-bound induction performs — it exchanges `a` into the spanning set in
place of `wq` without shrinking what the set generates.

It is the base-set exchange (`…_over_adjoin`) wrapped in the `adjoin`-tower bridge
`adjoin R (s ∪ {x}) = (adjoin (adjoin R s) {x}).restrictScalars R`
(`Algebra.adjoin_union_eq_adjoin_adjoin`). The bridge costs nothing at the algebra level:
`IsAlgebraic` is **definitionally invariant** under `Subalgebra.restrictScalars` (same
carrier, same ring structure), so the tower rewrites are pure `▸`-transport with no side
goals. Verified `sorryAx`-free. -/
theorem isAlgebraic_adjoin_insert_replace
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {s : Set A} {wq a : A}
    (hb : IsAlgebraic (Algebra.adjoin R (insert wq s)) a)
    (ha : Transcendental (Algebra.adjoin R s) a) :
    IsAlgebraic (Algebra.adjoin R (insert a s)) wq := by
  have heq : Algebra.adjoin R (insert wq s)
           = (Algebra.adjoin (Algebra.adjoin R s) {wq}).restrictScalars R := by
    rw [Set.insert_eq, Set.union_comm, adjoin_union_eq_adjoin_adjoin]
  -- `IsAlgebraic` is defeq under `restrictScalars`, so the tower form is the same statement.
  have hb'' : IsAlgebraic ((Algebra.adjoin (Algebra.adjoin R s) {wq}).restrictScalars R) a :=
    heq ▸ hb
  have hb' : IsAlgebraic (Algebra.adjoin (Algebra.adjoin R s) {wq}) a := hb''
  have hwq : IsAlgebraic (Algebra.adjoin (Algebra.adjoin R s) {a}) wq :=
    isAlgebraic_adjoin_singleton_exchange_over_adjoin s hb' ha
  have heq2 : Algebra.adjoin R (insert a s)
            = (Algebra.adjoin (Algebra.adjoin R s) {a}).restrictScalars R := by
    rw [Set.insert_eq, Set.union_comm, adjoin_union_eq_adjoin_adjoin]
  have hwq' : IsAlgebraic ((Algebra.adjoin (Algebra.adjoin R s) {a}).restrictScalars R) wq := hwq
  exact heq2.symm ▸ hwq'

/-- `{x | x ∈ c :: l} = insert c {x | x ∈ l}` — the set swept by a list, one cons at a time. -/
theorem setOf_mem_cons {E : Type*} (c : E) (l : List E) :
    {x | x ∈ c :: l} = insert c {x | x ∈ l} := by
  ext x; simp only [Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]

/-- **The pigeonhole for the finite-bound induction — PROVEN.** Walk the generator list `l`.
If `a` is transcendental over `R⟨s⟩` but algebraic over `R⟨s ∪ l⟩`, then somewhere along the
list a generator `t` first turns `a` algebraic: there is a `t ∈ l` and a prefix-grown base
`pre` with `a` still transcendental over `R⟨pre⟩` yet algebraic over `R⟨insert t pre⟩`. That
`t` is exactly the displaceable generator that `isAlgebraic_adjoin_insert_replace` swaps out.

Pure list induction on `l`, branching on `Classical.em (IsAlgebraic (adjoin R (insert c s)) a)`
at each cons; no field or algebra content, so it holds over any `CommRing`. Verified
`sorryAx`-free. -/
theorem exists_displaceable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]
    (a : E) : ∀ (l : List E) (s : Set E),
    Transcendental (Algebra.adjoin R s) a →
    IsAlgebraic (Algebra.adjoin R (s ∪ {x | x ∈ l})) a →
    ∃ (t : E) (pre : Set E), t ∈ l ∧ pre ⊆ s ∪ {x | x ∈ l} ∧
      Transcendental (Algebra.adjoin R pre) a ∧
      IsAlgebraic (Algebra.adjoin R (insert t pre)) a := by
  intro l
  induction l with
  | nil =>
    intro s ha0 halg
    have he : {x : E | x ∈ ([] : List E)} = ∅ := by ext x; simp
    rw [he, Set.union_empty] at halg
    exact absurd halg ha0
  | cons c l' ih =>
    intro s ha0 halg
    by_cases hca : IsAlgebraic (Algebra.adjoin R (insert c s)) a
    · exact ⟨c, s, List.mem_cons_self c l', Set.subset_union_left, ha0, hca⟩
    · have ha0' : Transcendental (Algebra.adjoin R (s ∪ {c})) a := by
        rw [Set.union_comm, Set.singleton_union]; exact hca
      have hset : s ∪ {c} ∪ {x | x ∈ l'} = s ∪ {x | x ∈ c :: l'} := by
        rw [setOf_mem_cons, Set.union_assoc, Set.singleton_union]
      have halg' : IsAlgebraic (Algebra.adjoin R ((s ∪ {c}) ∪ {x | x ∈ l'})) a := by
        rw [hset]; exact halg
      obtain ⟨t, pre, ht, hsub, htr, htalg⟩ := ih (s ∪ {c}) ha0' halg'
      exact ⟨t, pre, List.mem_cons_of_mem c ht, hset ▸ hsub, htr, htalg⟩

/-- **The last element of an independent family is transcendental over the adjoin of the
rest — PROVEN.** For `v : Fin (n+1) → E` algebraically independent over `F`, the final entry
`v (Fin.last n)` is transcendental over `F⟨v₀,…,v_{n-1}⟩`. Reindex the family by
`finSuccEquivLast` (last ↔ none), then `AlgebraicIndependent.option_iff` reads off the
transcendence. Verified `sorryAx`-free. -/
theorem transcendental_last_of_algebraicIndependent
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] {n : ℕ}
    (v : Fin (n + 1) → E) (hv : AlgebraicIndependent F v) :
    Transcendental (Algebra.adjoin F (Set.range (v ∘ Fin.castSucc))) (v (Fin.last n)) := by
  have hpre : AlgebraicIndependent F (v ∘ Fin.castSucc) :=
    hv.comp Fin.castSucc (Fin.castSucc_injective n)
  have hfe : (fun o : Option (Fin n) => o.elim (v (Fin.last n)) (v ∘ Fin.castSucc))
             ∘ finSuccEquivLast = v := by
    funext k
    refine Fin.lastCases ?_ ?_ k
    · simp [finSuccEquivLast_last]
    · intro i; simp [finSuccEquivLast_castSucc]
  have hopt : AlgebraicIndependent F
      (fun o : Option (Fin n) => o.elim (v (Fin.last n)) (v ∘ Fin.castSucc)) :=
    (algebraicIndependent_equiv' finSuccEquivLast hfe).mp hv
  exact (hpre.option_iff (v (Fin.last n))).mp hopt

/-!
## The subring → subfield bridge

The exchange/replace/pigeonhole lemmas above all speak of `Algebra.adjoin F X` — the
*subring* `F[X]`. But the finite-bound respan needs `Algebra.IsAlgebraic.trans`, which
(via `isAlgebraic_iff_isIntegral`) requires **field** bases. The bridge below crosses to
`IntermediateField.adjoin F X` (the *subfield* `F(X)`), where the field-theoretic transitivity
lives. It was the one piece Mathlib lacked: the fact that `F(X)` is the fraction ring of `F[X]`
inside `E`, i.e. the instance `IsFractionRing ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X)`,
built here from `IntermediateField.mem_adjoin_iff` (every subfield element is a quotient of
subring elements).
-/

/-- **The subring → subfield bridge — PROVEN.** `e` is algebraic over the subring `F[X]`
(`Algebra.adjoin F X`) iff it is algebraic over the subfield `F(X)`
(`IntermediateField.adjoin F X`). Both directions at once from `IsFractionRing.isAlgebraic_iff`,
after constructing the missing instance `IsFractionRing ↥(Algebra.adjoin F X) ↥(F(X))`: the
subfield is the fraction ring of the subring inside `E`. The `IsLocalization.surj'` field is
exactly `IntermediateField.mem_adjoin_iff` (`x ∈ F(X) ↔ x = aeval r / aeval s` with
`r,s ∈ F[X]`); `map_units'` is "nonzero in a field is a unit"; `exists_of_eq` is injectivity of
the inclusion. Verified `sorryAx`-free. -/
theorem isAlgebraic_algebraAdjoin_iff_intermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E] (X : Set E) (e : E) :
    IsAlgebraic (Algebra.adjoin F X) e ↔ IsAlgebraic (↥(IntermediateField.adjoin F X)) e := by
  have hmem : ∀ r : MvPolynomial X F,
      MvPolynomial.aeval (Subtype.val : X → E) r ∈ Algebra.adjoin F X := by
    intro r
    have : MvPolynomial.aeval (Subtype.val : X → E) r
        ∈ (MvPolynomial.aeval (Subtype.val : X → E)).range := ⟨r, rfl⟩
    rwa [← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe] at this
  letI algAK : Algebra ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F X)).toRingHom.toAlgebra
  have hmapAK : ∀ a : ↥(Algebra.adjoin F X),
      ((algebraMap ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X) a : _) : E) = (a : E) :=
    fun a => rfl
  haveI tower : IsScalarTower ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X) E :=
    IsScalarTower.of_algebraMap_eq (fun a => (hmapAK a).symm)
  haveI fr : IsFractionRing ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      rw [mem_nonZeroDivisors_iff_ne_zero] at hy
      refine isUnit_iff_ne_zero.mpr (fun h => hy (Subtype.ext ?_))
      have hc := congrArg (fun k : ↥(IntermediateField.adjoin F X) => (k : E)) h
      simpa [hmapAK] using hc
    · intro z
      obtain ⟨r, s, hzrs⟩ := (IntermediateField.mem_adjoin_iff F (z : E)).mp z.2
      by_cases hden : MvPolynomial.aeval (Subtype.val : X → E) s = 0
      · refine ⟨⟨0, 1⟩, Subtype.ext ?_⟩
        rw [hden, div_zero] at hzrs
        simp [show (z : E) = 0 from hzrs]
      · refine ⟨⟨⟨_, hmem r⟩, ⟨⟨_, hmem s⟩,
          mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => hden (congrArg Subtype.val h))⟩⟩,
          Subtype.ext ?_⟩
        have : ((z : E)) * MvPolynomial.aeval (Subtype.val : X → E) s
             = MvPolynomial.aeval (Subtype.val : X → E) r := by
          rw [hzrs, div_mul_cancel₀ _ hden]
        simpa [hmapAK] using this
    · intro x y hxy
      refine ⟨1, ?_⟩
      have hc := congrArg (fun k : ↥(IntermediateField.adjoin F X) => (k : E)) hxy
      simp only [hmapAK] at hc
      simp [Subtype.ext hc]
  exact IsFractionRing.isAlgebraic_iff ↥(Algebra.adjoin F X) ↥(IntermediateField.adjoin F X) E

/-- Bridge for transcendence (negation of `isAlgebraic_algebraAdjoin_iff_intermediateField`):
`a` is transcendental over the subring `F[X]` iff over the subfield `F(X)`. -/
theorem transcendental_algebraAdjoin_iff_intermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E] (X : Set E) (a : E) :
    Transcendental (Algebra.adjoin F X) a ↔ Transcendental (↥(IntermediateField.adjoin F X)) a :=
  not_congr (isAlgebraic_algebraAdjoin_iff_intermediateField X a)

/-- **The respan step — PROVEN.** If `E` is algebraic over `F(insert t S)` and `t` is
algebraic over `F(insert v S)`, then `E` is algebraic over `F(insert v S)`. This is the
"the swapped set still spans" step: after `v` displaces `t`, the new generating set still
makes `E` algebraic. All over `IntermediateField.adjoin` (subfields), where transitivity lives.

Route through the join `B := F(insert v S)⟮t⟯` (a *single*-element extension of the new base
`K := F(insert v S)` by the algebraic `t`): `B` is algebraic over `K` (`isAlgebraic_adjoin`,
`t` integral over the field `K`), and `E` is algebraic over `B` (base-up from
`F(insert t S) ≤ B.restrictScalars F`, via `adjoin_adjoin_left` + element-wise
`IsAlgebraic.tower_top_of_subalgebra_le`), so `Algebra.IsAlgebraic.trans` (`K → B → E`) gives
`E` algebraic over `K`. Verified `sorryAx`-free. -/
theorem respan {F E : Type*} [Field F] [Field E] [Algebra F E] {S : Set E} {v t : E}
    (hspan : Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (insert t S))) E)
    (htalg : IsAlgebraic (↥(IntermediateField.adjoin F (insert v S))) t) :
    Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (insert v S))) E := by
  set K := IntermediateField.adjoin F (insert v S) with hKdef
  have htint : IsIntegral K t := htalg.isIntegral
  have hBK : Algebra.IsAlgebraic K (IntermediateField.adjoin K {t}) :=
    IntermediateField.isAlgebraic_adjoin
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; exact hx ▸ htint)
  have hle : IntermediateField.adjoin F (insert t S)
           ≤ (IntermediateField.adjoin K {t}).restrictScalars F := by
    have hrw : (IntermediateField.adjoin K {t}).restrictScalars F
             = IntermediateField.adjoin F (insert v S ∪ {t}) := by
      rw [hKdef]; exact IntermediateField.adjoin_adjoin_left F (insert v S) {t}
    rw [hrw]
    apply IntermediateField.adjoin.mono
    intro x hx
    rcases hx with rfl | hxS
    · exact Or.inr rfl
    · exact Or.inl (Or.inr hxS)
  have hEB : Algebra.IsAlgebraic (↥(IntermediateField.adjoin K {t})) E := by
    rw [Algebra.isAlgebraic_def]
    intro e
    have h0 : IsAlgebraic (↥(IntermediateField.adjoin F (insert t S))) e := hspan.isAlgebraic e
    have hsle : (IntermediateField.adjoin F (insert t S)).toSubalgebra
              ≤ ((IntermediateField.adjoin K {t}).restrictScalars F).toSubalgebra := hle
    exact h0.tower_top_of_subalgebra_le hsle
  exact Algebra.IsAlgebraic.trans (L := IntermediateField.adjoin K {t})

open Algebra in
/-- **Finite transcendence-degree bound (van der Waerden) — the target.** An algebraically
independent family `v : Fin p → E` is no larger than any spanning finset `T` (E algebraic over
`F(T)`): `p ≤ T.card`. -/
theorem card_le_of_isAlgebraic_span {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (v : Fin p → E) (hv : AlgebraicIndependent F v)
    (T : Finset E) (hT : Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (T : Set E))) E) :
    p ≤ T.card := by
  classical
  -- invariant: after placing the first k of the v's, a same-card spanning finset contains them
  have place : ∀ k : ℕ, k ≤ p → ∃ U : Finset E, U.card = T.card ∧
      Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (U : Set E))) E ∧
      (∀ i : Fin p, (i : ℕ) < k → v i ∈ U) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨T, rfl, hT, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨U, hUcard, hUspan, hUpre⟩ := ih (Nat.le_of_succ_le hk)
      have hk' : k < p := hk
      set vk := v ⟨k, hk'⟩ with hvkdef
      by_cases hmem : vk ∈ U
      · refine ⟨U, hUcard, hUspan, ?_⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hUpre i h
        · have : i = ⟨k, hk'⟩ := Fin.ext h
          rw [this]; exact hmem
      · -- vk ∉ U: displace some non-prefix generator t and swap vk in
        -- prefix family and its range
        have hkle : k + 1 ≤ p := hk
        set w : Fin (k + 1) → E := v ∘ Fin.castLE hkle with hwdef
        have hw : AlgebraicIndependent F w := hv.comp _ (Fin.castLE_injective hkle)
        have hwlast : w (Fin.last k) = vk := by
          simp [hwdef, hvkdef, Fin.castLE, Fin.last]
        -- prefix finset P = {v 0, ..., v (k-1)}
        set P : Finset E := Finset.image (fun i : Fin k => w (Fin.castSucc i)) Finset.univ with hPdef
        have hPrange : (P : Set E) = Set.range (w ∘ Fin.castSucc) := by
          rw [hPdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]; rfl
        have hPU : P ⊆ U := by
          intro x hx
          rw [hPdef, Finset.mem_image] at hx
          obtain ⟨i, _, rfl⟩ := hx
          have : (Fin.castLE hkle (Fin.castSucc i) : ℕ) < k := by
            simp only [Fin.coe_castLE, Fin.coe_castSucc]; exact i.isLt
          exact hUpre _ this
        -- vk transcendental over F[P]
        have htrans : Transcendental (Algebra.adjoin F (P : Set E)) vk := by
          rw [hPrange, ← hwlast]
          exact transcendental_last_of_algebraicIndependent w hw
        -- vk algebraic over F[U]
        have halgU : IsAlgebraic (Algebra.adjoin F (U : Set E)) vk := by
          rw [isAlgebraic_algebraAdjoin_iff_intermediateField]
          exact hUspan.isAlgebraic vk
        -- run the pigeonhole with base P, list U \ P
        have hunion : (P : Set E) ∪ {x | x ∈ (U \ P).toList} = (U : Set E) := by
          ext x
          simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_toList, Finset.mem_sdiff,
            Finset.mem_coe]
          constructor
          · rintro (hxP | ⟨hxU, _⟩)
            · exact hPU hxP
            · exact hxU
          · intro hxU
            by_cases h : x ∈ P
            · exact Or.inl h
            · exact Or.inr ⟨hxU, h⟩
        have halgUnion : IsAlgebraic (Algebra.adjoin F ((P : Set E) ∪ {x | x ∈ (U \ P).toList})) vk := by
          rw [hunion]; exact halgU
        obtain ⟨t, pre, htmem, hpresub, htr, htalg⟩ :=
          exists_displaceable vk (U \ P).toList (P : Set E) htrans halgUnion
        rw [Finset.mem_toList, Finset.mem_sdiff] at htmem
        obtain ⟨htU, htP⟩ := htmem
        -- t ∉ pre (free from transc + algebraic)
        have htnp : t ∉ pre := by
          intro htp
          rw [Set.insert_eq_of_mem htp] at htalg
          exact htr htalg
        -- pre ⊆ U and pre ⊆ U.erase t
        have hpreU : pre ⊆ (U : Set E) := by rw [← hunion]; exact hpresub
        have hpre_erase : pre ⊆ (↑(U.erase t) : Set E) := by
          intro x hx
          rw [Finset.coe_erase, Set.mem_diff]
          exact ⟨hpreU hx, fun hxt => htnp (hxt ▸ hx)⟩
        -- t algebraic over F(insert vk (U.erase t))  [subfield]
        have htalg_if : IsAlgebraic (↥(IntermediateField.adjoin F (insert vk (↑(U.erase t) : Set E)))) t := by
          have h1 : IsAlgebraic (Algebra.adjoin F (insert vk pre)) t :=
            isAlgebraic_adjoin_insert_replace htalg htr
          rw [isAlgebraic_algebraAdjoin_iff_intermediateField] at h1
          refine h1.tower_top_of_subalgebra_le ?_
          apply IntermediateField.adjoin.mono
          apply Set.insert_subset_insert hpre_erase
        -- respan: E algebraic over F(insert vk (U.erase t))
        have hspan' : Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (insert t (↑(U.erase t) : Set E)))) E := by
          have hins : insert t (↑(U.erase t) : Set E) = (↑U : Set E) := by
            rw [← Finset.coe_insert, Finset.insert_erase htU]
          rw [hins]; exact hUspan
        have hUspan' : Algebra.IsAlgebraic (↥(IntermediateField.adjoin F (insert vk (↑(U.erase t) : Set E)))) E :=
          respan hspan' htalg_if
        -- the new finset U' = insert vk (U.erase t)
        refine ⟨insert vk (U.erase t), ?_, ?_, ?_⟩
        · have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨t, htU⟩
          rw [Finset.card_insert_of_not_mem (by simp [hmem]), Finset.card_erase_of_mem htU, ← hUcard]
          omega
        · have : (↑(insert vk (U.erase t)) : Set E) = insert vk (↑(U.erase t) : Set E) := by
            rw [Finset.coe_insert]
          rw [this]; exact hUspan'
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · have hvi : v i ∈ U := hUpre i h
            have hviP : v i ∈ P := by
              rw [hPdef, Finset.mem_image]
              exact ⟨⟨i, h⟩, Finset.mem_univ _, rfl⟩
            have hvit : v i ≠ t := fun he => htP (he ▸ hviP)
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hvit, hvi⟩))
          · have : i = ⟨k, hk'⟩ := Fin.ext h
            rw [this]; exact Finset.mem_insert_self _ _
  -- count
  obtain ⟨U, hUcard, _, hUall⟩ := place p le_rfl
  have hsub : Finset.univ.image v ⊆ U := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hUall i i.2
  calc p = (Finset.univ.image v).card := by
            rw [Finset.card_image_of_injective _ hv.injective, Finset.card_univ, Fintype.card_fin]
    _ ≤ U.card := Finset.card_le_card hsub
    _ = T.card := hUcard

