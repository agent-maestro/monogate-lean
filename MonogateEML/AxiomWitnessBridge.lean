import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Compact
import MachLib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import MonogateEML.MachLibRealModelRolle
import MonogateEML.MachLibRealModelLog
import MonogateEML.MachLibRealModelHyperbolic

/-!
# Axiom-witness bridge — verbatim, kernel-checked `MachLib.Real ⊨ ℝ`

The AxiomLedger (machlib) pins that shipped footprints stay ⊆ a `trustedFootprint` set — but
"trusted" was, until now, an *asserted* claim that those axioms are witnessed. This file makes
that claim **mechanical and verbatim**: for each registered MachLib axiom it *interprets* the
axiom's actual `Expr` type into Mathlib's vocabulary (`MachLib.Real ↦ ℝ`, its `Add`/`Mul`/`LT`
instances ↦ ℝ's, `exp ↦ Real.exp`, `HasDerivAt ↦` Mathlib's `HasDerivAt`, …) and then checks that
a registered witness term **elaborates at that interpreted type** — the muse's
`example : ⟦axiom⟧ := witness`, done automatically.

Why this and not name-matching: a name table (`rolle_ct ↦ rolle_witnessed`) would have marked the
old *unsound* open-interval `rolle` "witnessed" forever. Here the check is on the *type*: the
witness must inhabit the exact interpreted statement. Teeth-verified — a wrong witness
(`rolle_ct ⊣ Real.exp_pos`, `add_comm ⊣ mul_comm`) is rejected. If a witness stops typechecking
under the pinned Mathlib rev, this file goes red.

Building this file IS the check: `logError` on any registered axiom whose witness fails to
verbatim-inhabit its interpreted type.
-/

-- The registry is a long list literal; the default elaborator recursion depth is not
-- enough for it once the trig/sqrt block is included.
set_option maxRecDepth 100000

/-- **Half of the last remaining gap**, discharged and named so the next agent does not have to
rediscover that it is a separate obligation.

`analytic_finite_zeros_compact` concludes `RealSetFinite`, which is NOT `Set.Finite`: MachLib
defines it as a bound on the length of every `Nodup` list drawn from the set
(`AnalyticFiniteZeros.lean:70`). So witnessing that axiom needs the analysis (zeros of a
not-identically-zero analytic function on a compact are finite) AND this conversion. Only the
former is still open; feed its `Set.Finite` to this lemma and the witness closes. -/
theorem realSetFinite_of_finite {S : Set ℝ} (hS : S.Finite) :
    ∃ n : ℕ, ∀ l : List ℝ, l.Nodup → (∀ x ∈ l, x ∈ S) → l.length ≤ n := by
  classical
  refine ⟨hS.toFinset.card, fun l hnd hmem => ?_⟩
  have hsub : l.toFinset ⊆ hS.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simpa using hmem x hx
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ hS.toFinset.card := Finset.card_le_card hsub

open Lean Meta Elab Command Term

namespace AxiomWitnessBridge

/-- Interpretation map: each MachLib constant appearing in a registered axiom's type ↦ the
Mathlib term it denotes over `ℝ`. Instances are `inferInstance`; functions are η-expanded so the
substituted application β-reduces to the Mathlib call. -/
def interpEntries : List (Name × TSyntax `term) := [
  (`MachLib.Real,               Unhygienic.run `(ℝ)),
  (`MachLib.Real.instAdd,       Unhygienic.run `((inferInstance : Add ℝ))),
  (`MachLib.Real.instMul,       Unhygienic.run `((inferInstance : Mul ℝ))),
  (`MachLib.Real.instSub,       Unhygienic.run `((inferInstance : Sub ℝ))),
  (`MachLib.Real.instNeg,       Unhygienic.run `((inferInstance : Neg ℝ))),
  (`MachLib.Real.instDiv,       Unhygienic.run `((inferInstance : Div ℝ))),
  (`MachLib.Real.instLT,        Unhygienic.run `((inferInstance : LT ℝ))),
  (`MachLib.Real.instLE,        Unhygienic.run `((inferInstance : LE ℝ))),
  (`MachLib.Real.instOfNatZero, Unhygienic.run `((inferInstance : OfNat ℝ 0))),
  (`MachLib.Real.instOfNatOne,  Unhygienic.run `((inferInstance : OfNat ℝ 1))),
  -- raw operations (appear directly in some axiom types)
  (`MachLib.Real.addR,          Unhygienic.run `((fun a b : ℝ => a + b))),
  (`MachLib.Real.mulR,          Unhygienic.run `((fun a b : ℝ => a * b))),
  (`MachLib.Real.subR,          Unhygienic.run `((fun a b : ℝ => a - b))),
  (`MachLib.Real.divR,          Unhygienic.run `((fun a b : ℝ => a / b))),
  (`MachLib.Real.negR,          Unhygienic.run `((Neg.neg : ℝ → ℝ))),
  (`MachLib.Real.zeroR,         Unhygienic.run `((0 : ℝ))),
  (`MachLib.Real.oneR,          Unhygienic.run `((1 : ℝ))),
  (`MachLib.Real.ltR,           Unhygienic.run `((fun a b : ℝ => a < b))),
  (`MachLib.Real.leR,           Unhygienic.run `((fun a b : ℝ => a ≤ b))),
  (`MachLib.Real.natCast,       Unhygienic.run `((Nat.cast : ℕ → ℝ))),
  (`MachLib.Real.exp,           Unhygienic.run `(Real.exp)),
  (`MachLib.Real.log,           Unhygienic.run `(Real.log)),
  (`MachLib.Real.sinh,          Unhygienic.run `(Real.sinh)),
  (`MachLib.Real.cosh,          Unhygienic.run `(Real.cosh)),
  (`MachLib.Real.tanh,          Unhygienic.run `(Real.tanh)),
  (`MachLib.Real.u,             Unhygienic.run `((0 : ℝ))),
  -- Trig / sqrt / pi block. MachLib's `sqrt` and Mathlib's `Real.sqrt` are BOTH totalised to 0
  -- on negatives, so the interpretation is exact rather than merely agreeing on the domain.
  (`MachLib.Real.sin,           Unhygienic.run `(Real.sin)),
  (`MachLib.Real.cos,           Unhygienic.run `(Real.cos)),
  (`MachLib.Real.tan,           Unhygienic.run `(Real.tan)),
  (`MachLib.Real.pi,            Unhygienic.run `(Real.pi)),
  (`MachLib.Real.sqrt,          Unhygienic.run `(Real.sqrt)),
  (`MachLib.Real.atan,          Unhygienic.run `(Real.arctan)),
  (`MachLib.Real.arcsin,        Unhygienic.run `(Real.arcsin)),
  (`MachLib.Real.arccos,        Unhygienic.run `(Real.arccos)),
  (`MachLib.Real.log10,         Unhygienic.run `(Real.logb 10)),
  -- `abs` and `BoundedAbove` are MachLib `def`s, not axioms, but they appear inside axiom TYPES
  -- (`|x| < 1` hypotheses, the sup axiom's bound), so they must be interpreted before those
  -- axioms can be witnessed at all. Four of the nine gaps were blocked on exactly this.
  (`MachLib.Real.abs,           Unhygienic.run `((fun x : ℝ => |x|))),
  (`MachLib.Real.BoundedAbove,  Unhygienic.run `((fun p : ℝ → Prop => ∃ M : ℝ, ∀ x : ℝ, p x → x ≤ M))),
  -- MachLib's `ContinuousAt` is its OWN transparent epsilon-delta def, not Mathlib's filter one.
  (`MachLib.Real.ContinuousAt,  Unhygienic.run `((fun (f : ℝ → ℝ) (x : ℝ) =>
     ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |f y - f x| < ε))),
  (`MachLib.Real.HasDerivAt,    Unhygienic.run `(fun (f : ℝ → ℝ) (f' x : ℝ) => HasDerivAt f f' x)),
  (`MachLib.RealSet,            Unhygienic.run `((Set ℝ))),
  (`MachLib.Ioi,                Unhygienic.run `((fun a : ℝ => Set.Ioi a))),
  (`MachLib.Icc,                Unhygienic.run `((fun a b : ℝ => Set.Icc a b))),
  (`MachLib.Ioo,                Unhygienic.run `((fun a b : ℝ => Set.Ioo a b))),
  -- `RealSetFinite` is a Nodup-list-length bound, NOT `Set.Finite` (AnalyticFiniteZeros.lean:70).
  (`MachLib.RealSetFinite,      Unhygienic.run `((fun s : Set ℝ =>
     ∃ n : ℕ, ∀ l : List ℝ, l.Nodup → (∀ x ∈ l, x ∈ s) → l.length ≤ n))),
  (`MachLib.IsAnalyticOnReals,  Unhygienic.run `((fun (f : ℝ → ℝ) (S : Set ℝ) => AnalyticOnNhd ℝ f S))) ]

/-- Witness registry: MachLib axiom ↦ a Mathlib term claimed to inhabit its interpreted type.
The claim is CHECKED (not trusted): a wrong entry fails the gate. -/
def witnessRegistry : List (Name × TSyntax `term) := [
  -- raw operations (interpreted type is just the ℝ operation's type)
  (`MachLib.Real.addR,           Unhygienic.run `((fun a b : ℝ => a + b))),
  (`MachLib.Real.mulR,           Unhygienic.run `((fun a b : ℝ => a * b))),
  (`MachLib.Real.subR,           Unhygienic.run `((fun a b : ℝ => a - b))),
  (`MachLib.Real.divR,           Unhygienic.run `((fun a b : ℝ => a / b))),
  (`MachLib.Real.negR,           Unhygienic.run `((Neg.neg : ℝ → ℝ))),
  (`MachLib.Real.zeroR,          Unhygienic.run `((0 : ℝ))),
  (`MachLib.Real.oneR,           Unhygienic.run `((1 : ℝ))),
  (`MachLib.Real.ltR,            Unhygienic.run `((fun a b : ℝ => a < b))),
  (`MachLib.Real.leR,            Unhygienic.run `((fun a b : ℝ => a ≤ b))),
  (`MachLib.Real.natCast,        Unhygienic.run `((Nat.cast : ℕ → ℝ))),
  -- field / order laws
  (`MachLib.Real.add_comm,       Unhygienic.run `(add_comm)),
  (`MachLib.Real.add_assoc,      Unhygienic.run `(add_assoc)),
  (`MachLib.Real.add_zero,       Unhygienic.run `(add_zero)),
  (`MachLib.Real.add_neg,        Unhygienic.run `(fun a => add_neg_cancel a)),
  -- Mathlib v4.32 FLIPPED the sense of `add_lt_add_left`: it now yields `a + c < b + c`
  -- (adding on the right), while MachLib's axiom adds on the left. Caught by this bridge.
  (`MachLib.Real.add_lt_add_left, Unhygienic.run `(fun {a b} h c => by gcongr)),
  (`MachLib.Real.mul_comm,       Unhygienic.run `(mul_comm)),
  (`MachLib.Real.mul_assoc,      Unhygienic.run `(mul_assoc)),
  (`MachLib.Real.mul_one_ax,     Unhygienic.run `(mul_one)),
  (`MachLib.Real.mul_distrib,    Unhygienic.run `(mul_add)),
  (`MachLib.Real.mul_pos,        Unhygienic.run `(fun {a b} => mul_pos)),
  (`MachLib.Real.lt_irrefl_ax,   Unhygienic.run `(lt_irrefl)),
  (`MachLib.Real.lt_trans_ax,    Unhygienic.run `(fun {a b c} => lt_trans)),
  (`MachLib.Real.le_iff_lt_or_eq, Unhygienic.run `(fun {a b} => le_iff_lt_or_eq)),
  (`MachLib.Real.zero_lt_one_ax, Unhygienic.run `(zero_lt_one)),
  (`MachLib.Real.zero_ne_one_ax, Unhygienic.run `(zero_ne_one)),
  (`MachLib.Real.lt_total,       Unhygienic.run `(lt_trichotomy)),
  (`MachLib.Real.mul_inv,        Unhygienic.run `(fun a ha => mul_one_div_cancel ha)),
  (`MachLib.Real.sub_def,        Unhygienic.run `(sub_eq_add_neg)),
  (`MachLib.Real.div_def,        Unhygienic.run `(fun a b _ => div_eq_mul_one_div a b)),
  (`MachLib.Real.natCast_zero,   Unhygienic.run `(Nat.cast_zero)),
  (`MachLib.Real.one_div_pos_of_pos, Unhygienic.run `(fun {a} => one_div_pos.mpr)),
  -- exp
  (`MachLib.Real.exp,            Unhygienic.run `(Real.exp)),
  (`MachLib.Real.exp_pos,        Unhygienic.run `(Real.exp_pos)),
  (`MachLib.Real.exp_add,        Unhygienic.run `(Real.exp_add)),
  (`MachLib.Real.exp_zero,       Unhygienic.run `(Real.exp_zero)),
  -- derivatives
  (`MachLib.Real.HasDerivAt_exp,   Unhygienic.run `(fun x => Real.hasDerivAt_exp x)),
  (`MachLib.Real.HasDerivAt_const, Unhygienic.run `(fun (c x : ℝ) => hasDerivAt_const x c)),
  (`MachLib.Real.HasDerivAt_id,    Unhygienic.run `(fun x => hasDerivAt_id x)),
  (`MachLib.Real.HasDerivAt_add,   Unhygienic.run `(fun {f g f' g' x} hf hg => HasDerivAt.add hf hg)),
  (`MachLib.Real.HasDerivAt_sub,   Unhygienic.run `(fun {f g f' g' x} hf hg => HasDerivAt.sub hf hg)),
  (`MachLib.Real.HasDerivAt_mul,   Unhygienic.run `(fun {f g f' g' x} hf hg => HasDerivAt.mul hf hg)),
  (`MachLib.Real.HasDerivAt_unique, Unhygienic.run `(fun {f f₀ f₁ x} h₀ h₁ => HasDerivAt.unique h₀ h₁)),
  (`MachLib.Real.rolle_ct,       Unhygienic.run `(MonogateEML.RealModel.rolle_witnessed)),
  -- remaining derivatives + casts
  (`MachLib.Real.natCast_succ,   Unhygienic.run `(fun n => by push_cast; ring)),
  (`MachLib.Real.exp_surj,       Unhygienic.run `(fun y hy => ⟨Real.log y, Real.exp_log hy⟩)),
  (`MachLib.Real.HasDerivAt_log_pos, Unhygienic.run `(fun x hx => by simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx))),
  (`MachLib.Real.HasDerivAt_comp, Unhygienic.run `(fun f g a b x hg hf => HasDerivAt.comp x hf hg)),
  -- analytic batch
  (`MachLib.analytic_id,         Unhygienic.run `(fun S => analyticOnNhd_id)),
  (`MachLib.analytic_const,      Unhygienic.run `(fun c S => analyticOnNhd_const)),
  (`MachLib.analytic_add,        Unhygienic.run `(fun f g S hf hg => hf.add hg)),
  (`MachLib.analytic_sub,        Unhygienic.run `(fun f g S hf hg => hf.sub hg)),
  (`MachLib.analytic_mul,        Unhygienic.run `(fun f g S hf hg => hf.mul hg)),
  (`MachLib.analytic_exp,        Unhygienic.run `(fun S => analyticOnNhd_rexp.mono (Set.subset_univ S))),
  (`MachLib.analytic_comp,       Unhygienic.run `(fun f g S T hg hmaps hf => hf.comp hg hmaps)),
  (`MachLib.analytic_one_div_pos, Unhygienic.run `(by simp only [one_div]; exact analyticOnNhd_inv.mono (fun x hx => ne_of_gt hx))),
  (`MachLib.analytic_log_pos,    Unhygienic.run `(MonogateEML.RealModel.analyticOnNhd_real_log_Ioi)),
  -- `Pi.inv_def` is needed since v4.32: Mathlib states this for the FUNCTION `c⁻¹`, and
  -- without it simp leaves `f⁻¹` against MachLib's `fun y => 1 / f y` (plus an instance diamond).
  (`MachLib.Real.HasDerivAt_inv, Unhygienic.run `(fun f a x hfx hf => by simpa [one_div, sq, Pi.inv_def] using hf.inv hfx)),
  -- hyperbolic batch (MachLibRealModelHyperbolic.lean)
  (`MachLib.Real.sinh,           Unhygienic.run `(Real.sinh)),
  (`MachLib.Real.cosh,           Unhygienic.run `(Real.cosh)),
  (`MachLib.Real.tanh,           Unhygienic.run `(Real.tanh)),
  (`MachLib.Real.cosh_pos,       Unhygienic.run `(Real.cosh_pos)),
  (`MachLib.Real.cosh_ge_one,    Unhygienic.run `(Real.one_le_cosh)),
  (`MachLib.Real.sinh_eq,        Unhygienic.run `(fun x => by rw [Real.sinh_eq]; norm_num)),
  (`MachLib.Real.cosh_eq,        Unhygienic.run `(fun x => by rw [Real.cosh_eq]; norm_num)),
  (`MachLib.Real.tanh_eq_sinh_div_cosh, Unhygienic.run `(fun x => Real.tanh_eq_sinh_div_cosh x)),
  (`MachLib.Real.tanh_zero,      Unhygienic.run `(Real.tanh_zero)),
  (`MachLib.Real.tanh_lt_one,    Unhygienic.run `(fun x => by
    rw [Real.tanh_eq_sinh_div_cosh x, div_lt_one (Real.cosh_pos x)]; exact Real.sinh_lt_cosh x)),
  (`MachLib.Real.tanh_neg,       Unhygienic.run `(fun x => Real.tanh_neg x)),
  -- remaining certcom-footprint items: negation/congruence derivative rules, one more order
  -- law, and the abstract unit-roundoff constant `u` (only constrained by `u_nonneg`, so any
  -- nonnegative real witnesses it — `0` is the simplest choice)
  (`MachLib.Real.HasDerivAt_neg,   Unhygienic.run `(fun f a x hf => hf.neg)),
  (`MachLib.Real.HasDerivAt_of_eq, Unhygienic.run `(fun f g a x heq hf => by
    rw [show f = g from funext heq] at hf; exact hf)),
  (`MachLib.Real.mul_lt_mul_of_pos_right, Unhygienic.run `(fun {a b c} h hc => mul_lt_mul_of_pos_right h hc)),
  (`MachLib.Real.one_div_nonneg_of_pos, Unhygienic.run `(fun {b} hb => le_of_lt (one_div_pos.mpr hb))),
  (`MachLib.Real.u,              Unhygienic.run `((0 : ℝ))),
  -- ── trig / pi / sqrt tranche (added 2026-09-02) ───────────────────────────────
  (`MachLib.Real.sin_zero,       Unhygienic.run `(Real.sin_zero)),
  (`MachLib.Real.cos_zero,       Unhygienic.run `(Real.cos_zero)),
  (`MachLib.Real.sin_pi,         Unhygienic.run `(Real.sin_pi)),
  (`MachLib.Real.cos_pi,         Unhygienic.run `(Real.cos_pi)),
  (`MachLib.Real.sin_neg,        Unhygienic.run `(Real.sin_neg)),
  (`MachLib.Real.cos_neg,        Unhygienic.run `(Real.cos_neg)),
  (`MachLib.Real.sin_add,        Unhygienic.run `(Real.sin_add)),
  (`MachLib.Real.cos_add,        Unhygienic.run `(Real.cos_add)),
  (`MachLib.Real.pi_pos,         Unhygienic.run `(Real.pi_pos)),
  (`MachLib.Real.atan_zero,      Unhygienic.run `(Real.arctan_zero)),
  (`MachLib.Real.sqrt_nonneg,    Unhygienic.run `(Real.sqrt_nonneg)),
  (`MachLib.Real.HasDerivAt_sin, Unhygienic.run `(Real.hasDerivAt_sin)),
  (`MachLib.Real.HasDerivAt_cos, Unhygienic.run `(Real.hasDerivAt_cos)),
  -- MachLib writes `1 + 1` where Mathlib writes `2`, and `x * x` where Mathlib writes `x ^ 2`;
  -- these witnesses close exactly that gap and nothing else.
  (`MachLib.Real.pi_gt_one,      Unhygienic.run `(by linarith [Real.pi_gt_three])),
  (`MachLib.Real.sin_pi_div_two, Unhygienic.run `(by norm_num [Real.sin_pi_div_two])),
  (`MachLib.Real.cos_pi_div_two, Unhygienic.run `(by norm_num [Real.cos_pi_div_two])),
  (`MachLib.Real.pythagorean,    Unhygienic.run `(fun x => by simpa [sq] using Real.sin_sq_add_cos_sq x)),
  (`MachLib.Real.sin_periodic,   Unhygienic.run `(fun x => by norm_num [Real.sin_add_two_pi])),
  (`MachLib.Real.HasDerivAt_atan, Unhygienic.run `(fun x => by simpa [sq] using Real.hasDerivAt_arctan x)),
  (`MachLib.Real.sqrt_sq_nonneg, Unhygienic.run `(fun x hx => Real.mul_self_sqrt hx)),
  (`MachLib.Real.tan_def,        Unhygienic.run `(fun x _ => Real.tan_eq_sin_div_cos x)),
  (`MachLib.Real.sin_one_pos,    Unhygienic.run `(Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three]))),
  (`MachLib.Real.sin_pos_of_pos_lt_pi_div_two,
     Unhygienic.run `(fun x h0 hp => Real.sin_pos_of_pos_of_lt_pi h0 (by nlinarith [Real.pi_pos]))),
  (`MachLib.Real.archimedean,    Unhygienic.run `(fun x => exists_nat_gt x)),
  (`MachLib.Real.div_zero,       Unhygienic.run `(div_zero)),
  (`MachLib.Real.exp_lt,         Unhygienic.run `(fun h => Real.exp_lt_exp.mpr h)),
  (`MachLib.Real.one_add_le_exp, Unhygienic.run `(fun x => by simpa [add_comm] using Real.add_one_le_exp x)),
  (`MachLib.Real.exp_gt_one_plus_self,
     Unhygienic.run `(fun x hx => by simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt hx))),
  (`MachLib.Real.neg_one_lt_tanh, Unhygienic.run `(Real.neg_one_lt_tanh)),
  (`MachLib.Real.sqrt_le_of_le_sq,
     Unhygienic.run `(fun {z y} hz h => by
        rw [show z = Real.sqrt (z * z) from (Real.sqrt_mul_self hz).symm]; exact Real.sqrt_le_sqrt h)),
  (`MachLib.Real.le_sqrt_of_sq_le,
     Unhygienic.run `(fun {z y} hz h => by
        rw [show z = Real.sqrt (z * z) from (Real.sqrt_mul_self hz).symm]; exact Real.sqrt_le_sqrt h)),
  -- ── gap closures, second pass (2026-09-02) ────────────────────────────────────
  (`MachLib.Real.HasDerivAt_arcsin, Unhygienic.run `(fun x hx => by
     obtain ⟨h1, h2⟩ := abs_lt.mp hx
     simpa [sq] using Real.hasDerivAt_arcsin (ne_of_gt h1) (ne_of_lt h2))),
  (`MachLib.Real.HasDerivAt_arccos, Unhygienic.run `(fun x hx => by
     obtain ⟨h1, h2⟩ := abs_lt.mp hx
     simpa [sq] using Real.hasDerivAt_arccos (ne_of_gt h1) (ne_of_lt h2))),
  (`MachLib.Real.log10_def, Unhygienic.run `(fun x hx => by
     rw [show ((10:ℕ):ℝ) = (10:ℝ) by norm_num, Real.logb,
         div_mul_cancel₀ _ (by norm_num : Real.log (10:ℝ) ≠ 0)]
     exact Real.exp_log hx)),
  (`MachLib.Real.sup_exists, Unhygienic.run `(fun p hne hbd => by
     obtain ⟨M, hM⟩ := hbd
     obtain ⟨w, hw⟩ := hne
     obtain ⟨t, ht⟩ := Real.exists_isLUB (s := {x | p x}) ⟨w, hw⟩ ⟨M, fun y hy => hM y hy⟩
     exact ⟨t, fun x hx => ht.1 hx, fun s' hs' => ht.2 hs'⟩)),
  -- ── epsilon-delta tranche: all three were blocked on MachLib's own `abs` / `ContinuousAt`
  -- defs being uninterpreted, NOT on the analysis. `HasDerivAt` is fully opaque in MachLib, so
  -- these are the axioms that tie it to a real derivative -- worth witnessing precisely because
  -- an opaque predicate is where a misstatement would never surface from inside the corpus.
  (`MachLib.Real.hasDerivAt_continuousAt, Unhygienic.run `(fun {f f' x} h ε hε => by
     obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.mp h.continuousAt ε hε
     exact ⟨δ, hδ, fun y hy => by
       simpa [Real.dist_eq] using H (by simpa [Real.dist_eq] using hy)⟩)),
  (`MachLib.Real.HasDerivAt_congr, Unhygienic.run `(fun f g a x h hf => by
     obtain ⟨δ, hδ, H⟩ := h
     have heq : f =ᶠ[nhds x] g := by
       have : ∀ᶠ y in nhds x, f y = g y := by
         rw [Metric.eventually_nhds_iff]
         exact ⟨δ, hδ, fun {y} hy => H y (by simpa [Real.dist_eq] using hy)⟩
       exact this
     exact heq.hasDerivAt_iff.mp hf)),
  -- NOTE: `rw [hasDerivAt_iff_isLittleO]` works standalone but NOT here — after the
  -- interpretation substitution the goal is a beta-redex that `rw` will not see through.
  -- Going through `.mpr` is term-directed and tolerates it.
  (`MachLib.Real.HasDerivAt_of_eps_delta, Unhygienic.run `(fun {f f' x} h => by
     refine hasDerivAt_iff_isLittleO.mpr (Asymptotics.isLittleO_iff.mpr ?_)
     intro c hc
     obtain ⟨δ, hδ, H⟩ := h c hc
     rw [Metric.eventually_nhds_iff]
     refine ⟨δ, hδ, fun {y} hy => ?_⟩
     have hy' : |y - x| < δ := by simpa [Real.dist_eq] using hy
     simpa [Real.norm_eq_abs, mul_comm f' (y - x)] using H y hy')),
  -- Confirms the gap reason rewritten in f60d3090: this axiom NEVER uses analyticity. The
  -- witness takes `AnalyticAt -> ContinuousAt` and then works entirely from continuity, which
  -- is why it is far cheaper than the `analytic_finite_zeros_compact` it was once filed under.
  (`MachLib.analytic_ne_zero_nbhd, Unhygienic.run `(fun G a b x hG hax hxb hGx => by
     have hxmem : x ∈ Set.Icc a b := ⟨le_of_lt hax, le_of_lt hxb⟩
     have hcont : ContinuousAt G x := (hG x hxmem).continuousAt
     have hne : ∀ᶠ y in nhds x, G y ≠ 0 := hcont.eventually_ne hGx
     rw [Metric.eventually_nhds_iff] at hne
     obtain ⟨δ, hδ, H⟩ := hne
     refine ⟨max a (x - δ/2), min b (x + δ/2), le_max_left _ _, min_le_left _ _,
             max_lt hax (by linarith), lt_min hxb (by linarith), fun y h1 h2 => ?_⟩
     have hl : x - δ/2 < y := lt_of_le_of_lt (le_max_right _ _) h1
     have hr : y < x + δ/2 := lt_of_lt_of_le h2 (min_le_right _ _)
     exact H (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith))),
  -- THE LAST GAP. My own gap reason over-estimated this: it said a connected OPEN superset of
  -- `Icc a b` had to be built from the pointwise `AnalyticAt` neighbourhoods. Not so --
  -- `eqOn_zero_of_preconnected_of_frequently_eq_zero` wants only `IsPreconnected U`, and
  -- `Set.Icc a b` is preconnected, so the identity theorem applies to it directly. The whole
  -- construction I had budgeted for was unnecessary and the proof is ten lines.
  (`MachLib.analytic_finite_zeros_compact, Unhygienic.run `(fun f a b hab hf hne => by
     obtain ⟨x₀, hx₀mem, hx₀ne⟩ := hne
     have hZfin : {x : ℝ | x ∈ Set.Icc a b ∧ f x = 0}.Finite := by
       by_contra hinf
       obtain ⟨z₀, hz₀K, hacc⟩ :=
         Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc (fun x hx => hx.1)
       have hfreq : ∃ᶠ y in nhdsWithin z₀ {z₀}ᶜ, f y = 0 := by
         rw [accPt_iff_frequently_nhdsNE] at hacc
         exact hacc.mono (fun y hy => hy.2)
       exact hx₀ne ((hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
         isPreconnected_Icc hz₀K hfreq) (Set.Ioo_subset_Icc_self hx₀mem))
     exact realSetFinite_of_finite hZfin)),
  (`MachLib.Real.u_nonneg,       Unhygienic.run `(le_refl (0 : ℝ))) ]

def mkMap : TermElabM (List (Name × Expr)) :=
  interpEntries.mapM (fun (n, s) => do return (n, ← elabTerm s none))

/-- Replace every mapped MachLib const in `e` by its Mathlib image (β-reduction is handled by the
elaborator's defeq during the witness check). -/
def interpret (m : List (Name × Expr)) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n _ => m.lookup n
    | _ => none

/-- Verbatim check: does `witnessStx` elaborate at the INTERPRETED type of `axName`?
`withoutErrToSorry` turns a mismatch into a thrown error (caught → `false`); the sorry/mvar guard
rejects partial elaborations. -/
def checkWitnessed (m : List (Name × Expr)) (axName : Name) (witnessStx : TSyntax `term) : TermElabM Bool := do
  let some ci := (← getEnv).find? axName | return false
  let iType := interpret m ci.type
  try
    let e ← Term.withoutErrToSorry (elabTermEnsuringType witnessStx iType)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasSorry || e.hasExprMVar then return false
    return true
  catch _ => return false

run_cmd Command.liftTermElabM do
  let m ← mkMap
  let mut witnessed : Array Name := #[]
  let mut failed : Array Name := #[]
  for (ax, w) in witnessRegistry do
    if ← checkWitnessed m ax w then witnessed := witnessed.push ax
    else failed := failed.push ax
  unless failed.isEmpty do
    logError m!"AxiomWitnessBridge: {failed.size} registered axiom(s) FAIL the verbatim witness \
      typecheck (witness does not inhabit the interpreted axiom type): {failed.toList}"
  logInfo m!"AxiomWitnessBridge: {witnessed.size}/{witnessRegistry.length} registered axioms \
    verbatim-witnessed (kernel-checked `MachLib.Real ⊨ ℝ`)."

/-! ## Ledger cross-check — trusted = witnessed ∪ standard ∪ mapped ∪ (tracked gap)

Closes the loop with `AxiomLedger`: every axiom the ledger pins as `trustedFootprint` must be
accounted for here — verbatim-witnessed above, a Lean standard axiom, an interpretation-map
constant (carrier/predicate, not a proposition), or an explicitly tracked gap with a reason.
Anything trusted-but-unaccounted FAILS; a stale gap entry FAILS. So "trusted" (ledger) and
"witnessed" (this file) can no longer silently diverge. -/

/-- The ledger's trusted footprint (machlib `AxiomLedger.trustedFootprint`, pinned snapshot). -/
def trustedFootprint : List Name := [`Certcom.floatOfR, `Certcom.realToR, `Certcom.real_abs_eps, `Certcom.real_abs_rounds, `Certcom.real_acos_rounds, `Certcom.real_asin_rounds, `Certcom.real_atan_eps, `Certcom.real_atan_rounds, `Certcom.real_cos_eps, `Certcom.real_cos_rounds, `Certcom.real_cosh_rounds, `Certcom.real_exp_rounds, `Certcom.real_fpbridge, `Certcom.real_log10_rounds, `Certcom.real_log_rounds, `Certcom.real_round_bounds, `Certcom.real_sin_eps, `Certcom.real_sin_rounds, `Certcom.real_sinh_rounds, `Certcom.real_sqrt_rounds, `Certcom.real_tan_rounds, `Certcom.real_tanh_rounds, `Classical.choice, `MachLib.IsAnalyticOnReals, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_arccos, `MachLib.Real.HasDerivAt_arcsin, `MachLib.Real.HasDerivAt_atan, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_congr, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_cos, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_neg, `MachLib.Real.HasDerivAt_of_eps_delta, `MachLib.Real.HasDerivAt_of_eq, `MachLib.Real.HasDerivAt_sin, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.arccos, `MachLib.Real.archimedean, `MachLib.Real.arcsin, `MachLib.Real.atan, `MachLib.Real.atan_zero, `MachLib.Real.cos, `MachLib.Real.cos_add, `MachLib.Real.cos_neg, `MachLib.Real.cos_pi, `MachLib.Real.cos_pi_div_two, `MachLib.Real.cos_zero, `MachLib.Real.cosh, `MachLib.Real.cosh_eq, `MachLib.Real.cosh_ge_one, `MachLib.Real.cosh_pos, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.div_zero, `MachLib.Real.exp, `MachLib.Real.exp_add, `MachLib.Real.exp_gt_one_plus_self, `MachLib.Real.exp_lt, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.exp_zero, `MachLib.Real.hasDerivAt_continuousAt, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.le_sqrt_of_sq_le, `MachLib.Real.log10, `MachLib.Real.log10_def, `MachLib.Real.ltR, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_lt_mul_of_pos_right, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.neg_one_lt_tanh, `MachLib.Real.oneR, `MachLib.Real.one_add_le_exp, `MachLib.Real.one_div_nonneg_of_pos, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.pi, `MachLib.Real.pi_gt_one, `MachLib.Real.pi_pos, `MachLib.Real.pythagorean, `MachLib.Real.rolle_ct, `MachLib.Real.sin, `MachLib.Real.sin_add, `MachLib.Real.sin_neg, `MachLib.Real.sin_one_pos, `MachLib.Real.sin_periodic, `MachLib.Real.sin_pi, `MachLib.Real.sin_pi_div_two, `MachLib.Real.sin_pos_of_pos_lt_pi_div_two, `MachLib.Real.sin_zero, `MachLib.Real.sinh, `MachLib.Real.sinh_eq, `MachLib.Real.sqrt, `MachLib.Real.sqrt_le_of_le_sq, `MachLib.Real.sqrt_nonneg, `MachLib.Real.sqrt_sq_nonneg, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.sup_exists, `MachLib.Real.tan, `MachLib.Real.tan_def, `MachLib.Real.tanh, `MachLib.Real.tanh_eq_sinh_div_cosh, `MachLib.Real.tanh_lt_one, `MachLib.Real.u, `MachLib.Real.u_nonneg, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_finite_zeros_compact, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_ne_zero_nbhd, `MachLib.analytic_one_div_pos, `MachLib.analytic_sub, `Quot.sound, `propext]

/-- Standard Lean axioms — sound by construction, not witnessed here. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Carrier/predicate constants — interpretation-map entries (`Real ↦ ℝ`, `HasDerivAt` /
`IsAnalyticOnReals ↦` Mathlib's), not propositions to witness. -/
def mappedConstants : List Name := [`MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.IsAnalyticOnReals,
  -- function symbols: interpreted in `interpEntries`, not propositions to witness
  `MachLib.Real.sin, `MachLib.Real.cos, `MachLib.Real.tan, `MachLib.Real.pi, `MachLib.Real.sqrt,
  `MachLib.Real.atan, `MachLib.Real.arcsin, `MachLib.Real.arccos, `MachLib.Real.log10]

/-- **Float-bridge axioms — a different kind of trust, and Mathlib's `ℝ` cannot discharge them.**

Everything else in `trustedFootprint` is a statement *about `ℝ`*, so a Mathlib term either inhabits
it or the axiom is misstated. These are not. They relate `Certcom`'s concrete floating-point
evaluation to `ℝ` — that a machine `exp` rounds to within `eps` of `Real.exp`, that `floatOfR`
round-trips, and so on. No amount of Mathlib witnesses them, because Mathlib has no IEEE-754
semantics: they are claims about an implementation, validated by MEASUREMENT (the certifier's
harness and the hardware anchors), not by a model.

Listing them here rather than in `witnessGap` keeps the two kinds of trust apart. "Zero unmodeled
axioms" is a claim about the mathematical footprint; these 22 are the empirical footprint, and a
reader of the manifest should see that boundary rather than have it averaged away. -/
def bridgeAxioms : List Name := [`Certcom.floatOfR, `Certcom.realToR, `Certcom.real_abs_eps, `Certcom.real_abs_rounds, `Certcom.real_acos_rounds, `Certcom.real_asin_rounds, `Certcom.real_atan_eps, `Certcom.real_atan_rounds, `Certcom.real_cos_eps, `Certcom.real_cos_rounds, `Certcom.real_cosh_rounds, `Certcom.real_exp_rounds, `Certcom.real_fpbridge, `Certcom.real_log10_rounds, `Certcom.real_log_rounds, `Certcom.real_round_bounds, `Certcom.real_sin_eps, `Certcom.real_sin_rounds, `Certcom.real_sinh_rounds, `Certcom.real_sqrt_rounds, `Certcom.real_tan_rounds, `Certcom.real_tanh_rounds]

/-- Known-unwitnessed trusted axioms + machine-readable reason. CI-visible; shrinks as witnesses
are added. Trusted-but-unaccounted (not here, not registered, not standard/mapped) FAILS. -/
def witnessGap : List (Name × String) := []







run_cmd Command.liftTermElabM do
  let registered := witnessRegistry.map Prod.fst
  let accounted := registered ++ standardAxioms ++ mappedConstants ++ bridgeAxioms ++ witnessGap.map Prod.fst
  let unaccounted := trustedFootprint.filter (fun a => !(accounted.contains a))
  unless unaccounted.isEmpty do
    logError m!"AxiomWitnessBridge: {unaccounted.length} trusted axiom(s) UNACCOUNTED \
(not witnessed, not standard/mapped, not a tracked gap): {unaccounted}"
  let staleGap := (witnessGap.map Prod.fst).filter (fun a => !(trustedFootprint.contains a))
  unless staleGap.isEmpty do
    logError m!"AxiomWitnessBridge: stale witnessGap entr(y/ies) no longer trusted: {staleGap}"
  logInfo m!"AxiomWitnessBridge coverage: {registered.length} witnessed + {standardAxioms.length} \
standard + {mappedConstants.length} mapped + {bridgeAxioms.length} float-bridge + \
{witnessGap.length} tracked-gap, against {trustedFootprint.length} trusted axioms."

end AxiomWitnessBridge
