import Mathlib.RingTheory.AlgebraicIndependent
import Mathlib.RingTheory.Algebraic.Basic
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

1. **Relativise** `isAlgebraic_adjoin_singleton_exchange` over a base set `S` via the
   `adjoin`-tower isomorphism (`Algebra.adjoin_adjoin_...` / `restrictScalars`).
2. **The finite bound** (target below) by exchange induction on a finite spanning family
   (van der Waerden): maintain "A is algebraic over `R⟨v₀,…,v_{r-1}, w_r,…⟩`"; each new
   `vᵣ`, transcendental over the `v`-part but algebraic over the whole, forces (via the
   exchange) some remaining `w` to be swappable ⇒ `r < k` at each step ⇒ `#v ≤ #w`.

       theorem AlgebraicIndependent.card_le_of_isAlgebraic
           (hv : AlgebraicIndependent R v) (hw : Algebra.IsAlgebraic (adjoin R (range w)) A) :
           #ι ≤ #κ

3. **(3a) corollary + discharge** `algDep_of_bounded_trdeg`'s `H`, closing
   `chain_algebraic_dependence` (mod step 3b, the analytic-function domain for the exps).

## Status (2026-07-10)

Step "crux" (the exchange lemma) **PROVEN and verified** below. Steps 1–3 are the
remaining bricks; each commits only when `sorry`-free.
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
