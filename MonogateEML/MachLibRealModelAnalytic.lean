import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `MachLib.Real` soundness witness — power + differentiation axioms

Batch two of the Scope-B soundness witness (see `MachLibRealModel.lean` for the
field/order/literal core). This file discharges:

* the **power axioms** (`MachLib/Basic.lean` `realPow_*`) against `Real.rpow`, and
* the **differentiation axioms** (`MachLib/Differentiation.lean`: the opaque
  `HasDerivAt` predicate and its full rule set) against Mathlib's `HasDerivAt`.

The differentiation layer is the calculus foundation the log-Khovanskii work
rests on, so witnessing it in Mathlib closes the loop on "is that foundation
sound?" for the derivative reasoning. As before, everything reduces to the three
irreducible Lean axioms — no `sorryAx`.

**Follow-on (not here):** the analyticity layer (`IsAnalyticOnReals` + closures
in `MachLib/AnalyticFiniteZeros.lean`) against Mathlib's `AnalyticOn` — the base
closures are provable, but `analytic_finite_zeros_compact` needs Mathlib's
identity-theorem machinery and `eml_tree_analytic_on_pos` is EML-specific (not a
generic analysis fact); the exp/log/trig *value* axioms in `MachLib/Exp,Log,Trig`;
the generic decimal-order axioms; and the separate, harder float axis (Flocq).
-/

namespace MonogateEML.RealModel

/-! ## Power axioms → `Real.rpow` (`MachLib.Real.realPow_*`) -/

theorem realPow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := Real.rpow_zero x
theorem realPow_one  (x : ℝ) : x ^ (1 : ℝ) = x := Real.rpow_one x
theorem realPow_pos  {x y : ℝ} (hx : 0 < x) : 0 < x ^ y := Real.rpow_pos_of_pos hx y
theorem realPow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := Real.rpow_nonneg hx y

/-! ## Differentiation axioms → Mathlib `HasDerivAt`

`DifferentiationModel` bundles the opaque `HasDerivAt` predicate of
`MachLib/Differentiation.lean` and its rule set (name in the comment) into an
interface; `mathlibModel` exhibits Mathlib's `HasDerivAt` as a model, so the
predicate and every rule are Mathlib theorems, not axioms. -/

structure DifferentiationModel where
  R : Type
  zero : R
  one : R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R
  neg : R → R
  exp : R → R
  log : R → R
  sin : R → R
  cos : R → R
  lt : R → R → Prop
  /-- `D f f' x` : `f` has derivative `f'` at `x`. -/
  D : (R → R) → R → R → Prop
  unique     : ∀ (f : R → R) (a b x), D f a x → D f b x → a = b            -- HasDerivAt_unique
  const_rule : ∀ (c x), D (fun _ => c) zero x                              -- HasDerivAt_const
  id_rule    : ∀ x, D (fun x => x) one x                                   -- HasDerivAt_id
  exp_rule   : ∀ x, D exp (exp x) x                                        -- HasDerivAt_exp
  log_rule   : ∀ x, lt zero x → D log (div one x) x                        -- HasDerivAt_log_pos
  sin_rule   : ∀ x, D sin (cos x) x                                        -- HasDerivAt_sin
  cos_rule   : ∀ x, D cos (neg (sin x)) x                                  -- HasDerivAt_cos
  add_rule   : ∀ (f g : R → R) a b x, D f a x → D g b x →
                 D (fun y => add (f y) (g y)) (add a b) x                  -- HasDerivAt_add
  sub_rule   : ∀ (f g : R → R) a b x, D f a x → D g b x →
                 D (fun y => sub (f y) (g y)) (sub a b) x                  -- HasDerivAt_sub
  mul_rule   : ∀ (f g : R → R) a b x, D f a x → D g b x →
                 D (fun y => mul (f y) (g y)) (add (mul a (g x)) (mul (f x) b)) x  -- HasDerivAt_mul
  comp_rule  : ∀ (f g : R → R) a b x, D g a x → D f b (g x) →
                 D (fun y => f (g y)) (mul b a) x                          -- HasDerivAt_comp
  inv_rule   : ∀ (f : R → R) a x, f x ≠ zero → D f a x →
                 D (fun y => div one (f y)) (div (neg a) (mul (f x) (f x))) x  -- HasDerivAt_inv
  neg_rule   : ∀ (f : R → R) a x, D f a x → D (fun y => neg (f y)) (neg a) x    -- HasDerivAt_neg
  of_eq      : ∀ (f g : R → R) a x, (∀ y, f y = g y) → D f a x → D g a x   -- HasDerivAt_of_eq

/-- **The witness.** Mathlib's `ℝ` with `HasDerivAt` satisfies every
differentiation axiom of `MachLib.Real`. Existence of the term proves that layer
consistent relative to Mathlib. -/
noncomputable def mathlibModel : DifferentiationModel where
  R    := ℝ
  zero := 0
  one  := 1
  add  := (· + ·)
  sub  := (· - ·)
  mul  := (· * ·)
  div  := (· / ·)
  neg  := (- ·)
  exp  := Real.exp
  log  := Real.log
  sin  := Real.sin
  cos  := Real.cos
  lt   := (· < ·)
  D    := HasDerivAt
  unique     := fun _ _ _ _ h₁ h₂ => h₁.unique h₂
  const_rule := fun c x => hasDerivAt_const x c
  id_rule    := fun x => hasDerivAt_id x
  exp_rule   := fun x => Real.hasDerivAt_exp x
  log_rule   := fun x hx => by
                  show HasDerivAt Real.log (1 / x) x
                  rw [one_div]; exact Real.hasDerivAt_log (ne_of_gt hx)
  sin_rule   := fun x => Real.hasDerivAt_sin x
  cos_rule   := fun x => Real.hasDerivAt_cos x
  add_rule   := fun _ _ _ _ _ hf hg => hf.add hg
  sub_rule   := fun _ _ _ _ _ hf hg => hf.sub hg
  mul_rule   := fun _ _ _ _ _ hf hg => hf.mul hg
  comp_rule  := fun _ _ _ _ x hg hf => hf.comp x hg
  inv_rule   := fun f a x hfx hf => by
                  have hsq : f x * f x = f x ^ 2 := by ring
                  simp only [one_div, hsq]
                  exact hf.inv hfx
  neg_rule   := fun _ _ _ hf => hf.neg
  of_eq      := fun f g a x heq hf => by rw [show f = g from funext heq] at hf; exact hf

end MonogateEML.RealModel
