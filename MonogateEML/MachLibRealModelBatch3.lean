import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# `MachLib.Real` soundness witness — batch 3 (exp/trig values, Archimedean, analyticity)

Third batch of the Scope-B consistency witness (see `MachLibRealModel.lean` and
`MachLibRealModelAnalytic.lean`). Discharges, against Mathlib's `ℝ`:

* **exp value axioms** (`MachLib/Exp.lean`) → `Real.exp_*`;
* **core trig identities** (`MachLib/Trig.lean`) → `Real.sin_*` / `Real.cos_*` / `Real.pi_*`;
* **Archimedean** (`MachLib/Basic.lean` `natCast*` / `archimedean`) → `Nat.cast_*` / `exists_nat_gt`;
* **analyticity closures** (`MachLib/AnalyticFiniteZeros.lean`) → Mathlib `AnalyticOnNhd`.

Everything reduces to the three irreducible Lean axioms — no `sorryAx`.

## Not witnessed here, and why

* **`analytic_finite_zeros_compact`** (analytic + non-vanishing ⇒ finitely many
  zeros) needs Mathlib's identity-theorem / isolated-zeros machinery — a real
  proof, deferred; **`eml_tree_analytic_on_pos`** is EML-specific (a fact about
  `EMLTree.eval`, not a generic analysis lemma) so it has no generic model.
* **Supremum/completeness** (`sup_exists`), the **generic decimal-order** axioms,
  and the **exotic specials** (`erf`, `tanh` bounds, `arctan` bounds, `log10`/
  `exp10`, `tan_half_pos`) — mechanical-but-tedious or, for `erf`, absent from
  Mathlib; left for a follow-on.
* **Floats.** There is *nothing to witness*: `MachLib.Real` models exact reals
  (no IEEE-754), and `monogate-lean/MonogateEML/Float64.lean` is deliberately
  **axiom-free scaffolding** — concrete per-platform ULP axioms require offline
  libm validation (`libm-test-ulps`), so float grounding (Flocq) is a separate
  offline-validation project, not a soundness-witness one.
-/

namespace MonogateEML.RealModel

/-! ## exp value axioms → `Real.exp_*` (`MachLib/Exp.lean`) -/

theorem exp_zero : Real.exp 0 = 1 := Real.exp_zero
theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := Real.exp_add x y
theorem exp_pos (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
theorem exp_lt {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr h
theorem exp_surj (y : ℝ) (hy : 0 < y) : ∃ x : ℝ, Real.exp x = y :=
  ⟨Real.log y, Real.exp_log hy⟩
theorem exp_gt_one_plus_self (x : ℝ) (hx : 0 < x) : 1 + x < Real.exp x := by
  rw [add_comm]; exact Real.add_one_lt_exp (ne_of_gt hx)
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  rw [add_comm]; exact Real.add_one_le_exp x

/-! ## core trig identities → `Real.sin_*` / `Real.cos_*` (`MachLib/Trig.lean`) -/

theorem sin_zero : Real.sin 0 = 0 := Real.sin_zero
theorem cos_zero : Real.cos 0 = 1 := Real.cos_zero
theorem sin_pi : Real.sin Real.pi = 0 := Real.sin_pi
theorem cos_pi : Real.cos Real.pi = -1 := Real.cos_pi
theorem pi_pos : 0 < Real.pi := Real.pi_pos
theorem pythagorean (x : ℝ) : Real.sin x * Real.sin x + Real.cos x * Real.cos x = 1 := by
  rw [← Real.sin_sq_add_cos_sq x]; ring
theorem sin_neg (x : ℝ) : Real.sin (-x) = -(Real.sin x) := Real.sin_neg x
theorem cos_neg (x : ℝ) : Real.cos (-x) = Real.cos x := Real.cos_neg x
theorem sin_add (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := Real.sin_add x y
theorem cos_add (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := Real.cos_add x y

/-! ## Archimedean → `Nat.cast_*` / `exists_nat_gt` (`MachLib/Basic.lean`) -/

theorem natCast_zero : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
theorem natCast_succ (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
theorem archimedean (x : ℝ) : ∃ n : ℕ, x < (n : ℝ) := exists_nat_gt x

/-! ## analyticity closures → Mathlib `AnalyticOnNhd` (`MachLib/AnalyticFiniteZeros.lean`)

`AnalyticModel` bundles the opaque `IsAnalyticOnReals` predicate and its closure
axioms; `mathlibModel` models it with `AnalyticOnNhd ℝ f {x | S x}` (a `RealSet`
`S : R → Prop` becomes the set `{x | S x}`). Covers const/id/exp/add/sub/mul and
composition (the domain-mapping side condition becomes Mathlib's `Set.MapsTo`). -/

structure AnalyticModel where
  R : Type
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  exp : R → R
  Analytic : (R → R) → (R → Prop) → Prop
  const_rule : ∀ (c : R) (S), Analytic (fun _ => c) S                     -- analytic_const
  id_rule    : ∀ S, Analytic (fun x => x) S                               -- analytic_id
  exp_rule   : ∀ S, Analytic exp S                                        -- analytic_exp
  add_rule   : ∀ (f g : R → R) S, Analytic f S → Analytic g S →
                 Analytic (fun x => add (f x) (g x)) S                    -- analytic_add
  sub_rule   : ∀ (f g : R → R) S, Analytic f S → Analytic g S →
                 Analytic (fun x => sub (f x) (g x)) S                    -- analytic_sub
  mul_rule   : ∀ (f g : R → R) S, Analytic f S → Analytic g S →
                 Analytic (fun x => mul (f x) (g x)) S                    -- analytic_mul
  comp_rule  : ∀ (f g : R → R) S T, Analytic g S → (∀ x, S x → T (g x)) →
                 Analytic f T → Analytic (fun x => f (g x)) S             -- analytic_comp

/-- **The witness.** Mathlib's `ℝ` with `AnalyticOnNhd` satisfies the analyticity
closure axioms of `MachLib.Real`. -/
noncomputable def mathlibAnalyticModel : AnalyticModel where
  R := ℝ
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  exp := Real.exp
  Analytic := fun f S => AnalyticOnNhd ℝ f {x | S x}
  const_rule := fun c S => analyticOnNhd_const
  id_rule    := fun S => analyticOnNhd_id
  exp_rule   := fun S => analyticOnNhd_rexp.mono (Set.subset_univ _)
  add_rule   := fun _ _ _ hf hg => hf.add hg
  sub_rule   := fun _ _ _ hf hg => hf.sub hg
  mul_rule   := fun _ _ _ hf hg => hf.mul hg
  comp_rule  := fun _ _ _ _ hg hmaps hf => hf.comp hg (fun x hx => hmaps x hx)

end MonogateEML.RealModel
