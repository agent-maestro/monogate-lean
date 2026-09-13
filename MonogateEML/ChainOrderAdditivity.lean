-- MonogateEML/ChainOrderAdditivity.lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Chain-Order Additivity (CHA)

**Conjecture (filed 2026-04-27).** For any symbolic expression `f`, the
Pfaffian chain order of `f` equals the sum of chain orders over the
multiset of Pfaffian-not-elementary primitive AST occurrences in `f`:

    chain_order(f) = ∑_{p ∈ PNE(AST(f))} chain_order(p)

where the sum runs with multiplicity.

## Empirical evidence (NOT proof)

Across 23 test cases drawn from
`monogate-research/exploration/yn-log-singularity-2026-04-27/`
and `exploration/9th-tower-prediction-2026-04-27/`, **22 of 23
hit the predicted chain order exactly**. The lone Δ=+3 outlier
(`J₀(x) + Y₀(x)`) is consistent with the rule under
AST-occurrence counting: Y₀ internally contains a J₀ component,
so the explicit `J₀ + Y₀` AST has J₀ occurring twice (once on its
own; once nested inside Y₀ via the recursion
`Y₀ = (2/π)·(ln(x/2) + γ)·J₀(x) + 2/π·Σ ψ-series`), which the
detector counts twice.

## Why this is open

A proof requires the **Khovanskii zero-count theorem on Pfaffian
chains** [Khovanskii 1991; Wilkie 1996], which is not yet in
Mathlib. The same theorem is also required to close
`sin_not_in_eml` and `sin_not_in_real_EML_k` in
`InfiniteZerosBarrier.lean` (the two existing `sorry`s in the
canonical Lean repository). And the same theorem unblocks the
abstract `{T_F, T_Γ, T_W}` minimum-generating-set theorem
(`exploration/tower-independence-2026-04-27/FINDINGS.md`).

**One Mathlib advance — formalising Wilkie's o-minimal-`R_exp`
machinery, or a direct Khovanskii zero-count bound — closes
all three theorems simultaneously.**

## A new agent picking this up should:

  1. Check whether Mathlib's `Mathlib.Analysis.Analytic.IsolatedZeros`
     has gained Pfaffian-chain-tower machinery since this file was
     written (2026-04-27).
  2. If yes: lift the empirical 22/23 hits into Lean theorems
     using the new machinery.
  3. If no: open a Mathlib issue / port Khovanskii's bound from
     [Khovanskii 1991, *Fewnomials*] or formalise Wilkie's
     o-minimal `R_exp` structure [Wilkie 1996,
     *Model completeness results for expansions of the ordered
     field of real numbers by restricted Pfaffian functions and
     the exponential function*].
  4. Once the Mathlib gap is closed, the three theorems below
     should follow within a few hundred lines each.

The PETAL learning loop at `monogate-research/petal/` is designed
exactly for this kind of crowd-sourced attempt: agents can attempt
parts of the proof, log their failed tactics into the
`/api/petal/mistakes` stream, and accumulate documented
failure modes for the next agent.

-/

namespace MonogateChainOrderAdditivity

/-- Pfaffian-not-elementary primitive — abstract index over the
8 confirmed towers + 2 candidate towers. The chain order is the
height in the iterated defining-ODE tower. -/
inductive PNEPrimitive : Type
  | T_erf       -- chain 2 (DLMF 7)
  | T_Si        -- chain 3 (DLMF 6)
  | T_J         -- chain 3 (DLMF 10) — the FM-synthesis tower
  | T_Ai        -- chain 3 (DLMF 9)  — cubic-phase outlier
  | T_Gamma     -- chain 2 (DLMF 5)
  | T_W         -- chain 2 (DLMF 4)
  | T_K         -- chain 3 (DLMF 19)
  | T_F         -- chain 2-4 (DLMF 16) — hypergeometric supertower
  | T_Lerch     -- chain 4 — CANDIDATE (DLMF 25)
  | T_Mathieu   -- chain 4 — CANDIDATE (DLMF 28)
  deriving DecidableEq, Repr

namespace PNEPrimitive

/-- The chain order of a Pfaffian-not-elementary primitive.
Values from `monogate-research/exploration/E201_extended_atlas/independence_table.json`. -/
def chainOrder : PNEPrimitive → ℕ
  | T_erf     => 2
  | T_Si      => 3
  | T_J       => 3
  | T_Ai      => 3
  | T_Gamma   => 2
  | T_W       => 2
  | T_K       => 3
  | T_F       => 3      -- nominal; actual varies 2-4 with parameters
  | T_Lerch   => 4
  | T_Mathieu => 4

end PNEPrimitive

/-- A symbolic-expression abstraction sufficient to state the
conjecture. Concretely we only need a way to extract the multiset of
PNE primitives appearing in the expression's AST, with multiplicity. -/
opaque SymbolicExpr : Type

/-- Multiset of PNE primitive occurrences in the AST of an expression,
counted with multiplicity. The detector at
`eml_cost.analyze(expr).pfaffian_r` computes this in practice;
formalising the SymPy AST traversal is a separate engineering task. -/
opaque PNE_primitives_in_AST : SymbolicExpr → Multiset PNEPrimitive

/-- The Pfaffian chain order of an expression. In practice computed
by `eml_cost.analyze(expr).pfaffian_r`; the formal definition would
recurse over the iterated antiderivative tower. -/
opaque chainOrder : SymbolicExpr → ℕ

/-- **Chain-Order Additivity (CHA) — open.**

For any symbolic expression `f`, the Pfaffian chain order of `f`
equals the sum (with multiplicity) of chain orders of its
PNE-primitive AST occurrences.

### Mathematical content

Chain order of a Pfaffian function is the length of its defining
Pfaffian chain. CHA states that this length is recoverable by a
purely syntactic walk of the AST: count each occurrence of a
non-elementary primitive with the chain order of its defining
ODE, sum the multiset.

### Why it matters

If proven, CHA gives a linear-time algorithm for the Pfaffian
chain order from the AST — currently the best known method
requires solving the chain ODEs symbolically. CHA also sharpens
Khovanskii's zero-count bound from a global statement about a
Pfaffian function to a constructive bound from the AST shape.

### Empirical support

22/23 hits across `exploration/yn-log-singularity-2026-04-27`
and `exploration/9th-tower-prediction-2026-04-27`. The single
`Δ = +3` outlier `J₀ + Y₀` is recovered once `Y₀`'s internal
`J₀` occurrence is counted; see paper Section 4.

### Mathlib infrastructure needed

* The Khovanskii zero-count theorem on Pfaffian chains
  (`Mathlib.Analysis.PfaffianChains`, not yet in Mathlib).
* o-minimal structure theory for `ℝ_exp`, `ℝ_an`, `ℝ_an,exp`
  (Wilkie 1996; not yet in Mathlib — see Mathlib issue tracker
  for o-minimal RFC).
* Composition lemmas for Pfaffian functions analogous to
  `AnalyticOnNhd.comp`. -/
theorem chain_order_additivity (f : SymbolicExpr) :
    chainOrder f =
      ((PNE_primitives_in_AST f).map PNEPrimitive.chainOrder).sum := by
  sorry  -- Open: requires Khovanskii zero-count + o-minimal Pfaffian
         -- composition. See docstring for empirical motivation.

/-- **Corollary 1: tower-base equals chain order — open.**

For any single-primitive expression `f` whose AST contains exactly
one PNE-primitive node `p`, the empirical "tower base" assigned in
the C-207 dataset equals the chain order of `p`'s defining ODE.

  Empirical support: 17/18 of PNE rows in `combined_dataset.csv`.
  The lone Y_n outlier is recovered via `chain_order_additivity`
  once Y_n is recognised as a hidden T_J ⊕ T_Γ AST occurrence.

### Why this is sorry'd

This corollary is a direct consequence of `chain_order_additivity`
specialized to the single-primitive case: rewriting the multiset
sum on a singleton reduces to the chain order of the primitive.
But `chain_order_additivity` itself is sorry'd (open conjecture,
needs Khovanskii / o-minimal infrastructure).

A theorem downstream of a sorry is not proved. Marking this
corollary as sorry too keeps the dependency honest — once CHA is
closed, this corollary collapses to the original two-line proof
(`rw [chain_order_additivity, hf]; simp [Multiset.map_singleton,
Multiset.sum_singleton]`). -/
theorem tower_base_eq_chain_order
    (f : SymbolicExpr) (p : PNEPrimitive)
    (hf : PNE_primitives_in_AST f = {p}) :
    chainOrder f = PNEPrimitive.chainOrder p := by
  sorry  -- Conditionally provable from chain_order_additivity (sorry).
         -- See docstring for the two-line proof that closes once CHA does.

/-- **Corollary 2: minimum generating set in the abstract — open.**

Under unrestricted parameter substitution (DLMF identities),
`T_erf`, `T_Si`, `T_J`, `T_Ai`, `T_K` all reduce to restricted
parameter values of the hypergeometric supertower `T_F`.
`T_Γ` and `T_W` are NOT reducible to any other tower. Hence
`{T_F, T_Γ, T_W}` is a minimum generating set for the
Pfaffian-not-elementary closure (in the abstract sense; in the
F16 EML grammar all 8 are operationally needed since the grammar
lacks parameter-substitution primitives).

### Why it matters

The abstract minimum generating set tells us how *fundamental*
each Pfaffian primitive is. If only three primitives generate
the rest, an EML compiler can target a smaller backend ISA;
if more, every additional tower needs its own runtime.

### Empirical support

`exploration/tower-independence-2026-04-27/pairwise_results.json`
reports 5 SUBSUMES + 1 PARTIAL + 22 INDEPENDENT pairs across all
${8 \choose 2} = 28$ unordered tower pairs.

### Mathlib infrastructure needed

* A formal model of the hypergeometric function `_pFq` with
  parameter substitution and DLMF identity rewrites. Mathlib
  has `Real.Gamma`, `Real.Beta`, and the basic `_2F_1`, but the
  parametric DLMF rewrites are not yet in scope.
* The current statement is a placeholder (`∃ params, True`)
  pending a proper definition of "tower reducibility under
  parameter substitution". The right type is something like
  `∃ subst : ℝ → ℝ, AnalyticOn ℝ subst univ ∧ p = T_F.specialize subst`. -/
theorem three_tower_min_generating_set :
    ∀ p : PNEPrimitive,
      (p = .T_erf ∨ p = .T_Si ∨ p = .T_J ∨ p = .T_Ai ∨ p = .T_K) →
        ∃ params : ℕ, True  -- placeholder; replace with reducibility to T_F
        := by
  sorry  -- Open: needs formal _pFq + DLMF parameter-substitution
         -- machinery. See docstring for the proper statement shape.

end MonogateChainOrderAdditivity
