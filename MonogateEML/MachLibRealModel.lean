import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `MachLib.Real` soundness witness — Mathlib's `ℝ` is a model of the axiom base

`MachLib` (the fast, Mathlib-free proof library) rests on an opaque `Real`
type and ~40 axioms in `MachLib/Basic.lean`. Being Mathlib-free was a
deliberate build-speed choice, but it leaves the honest question open:
*could those axioms secretly be inconsistent?*

This file discharges that for the **mechanical field / order / literal core**:
it bundles those axioms — verbatim in shape — into an `OrderedFieldModel`
interface, then exhibits a single term `mathlibModel : OrderedFieldModel`
whose carrier is Mathlib's `ℝ` and whose every law is a Mathlib theorem.
Because the structure *requires* every field, the witness is complete for the
core by construction — no axiom can be silently skipped — and the existence of
the term is a machine-checked proof that the core is consistent relative to
Mathlib's `ℝ` (hence to ZFC).

Net effect for the covered axioms: the trusted base shrinks from those domain
axioms to the three irreducible Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — the base CompCert-class work also stands on.

**Covered here** (mirrors `MachLib.Real` in `MachLib/Basic.lean`): the field
laws (`add_comm`, `add_assoc`, `add_zero`, `add_neg`, `sub_def`, `mul_comm`,
`mul_assoc`, `mul_one_ax`, `mul_distrib`, `zero_ne_one_ax`, `div_def`,
`mul_inv`, `div_zero`), the order laws (`lt_irrefl_ax`, `lt_trans_ax`,
`lt_total`, `le_iff_lt_or_eq`, `add_lt_add_left`, `mul_pos`, `zero_lt_one_ax`),
and the concrete decimal-literal axioms (`realOfScientific_{one,two,three}_dot_zero`).

**Follow-on (not yet witnessed here):** the generic literal-order axioms
(`realOfScientific_pos` / `_le_of_nat` / `_lt_of_nat`), the power axioms
(`realPow_*` → `Real.rpow`), the Archimedean/completeness axioms
(`natCast`, `archimedean`, supremum), and the analytic axioms in
`MachLib/Differentiation.lean` + `MachLib/AnalyticFiniteZeros.lean`
(`exp`, `log`, `HasDerivAt_*` → Mathlib's `Real.exp`/`log`/`HasDerivAt`).
-/

namespace MonogateEML.RealModel

/-- The mechanical field/order/literal core of `MachLib.Real`, as an interface.
Each field mirrors an axiom of `MachLib/Basic.lean` (name in the comment); a
term of this type is a *model* of that axiom set. Operations are named as bare
functions (not notation) so the laws state exactly what `MachLib` asserts,
independent of any typeclass. -/
structure OrderedFieldModel where
  R    : Type
  zero : R
  one  : R
  add  : R → R → R
  neg  : R → R
  sub  : R → R → R
  mul  : R → R → R
  div  : R → R → R
  lt   : R → R → Prop
  le   : R → R → Prop
  -- field axioms (MachLib.Real.*)
  add_comm     : ∀ a b, add a b = add b a                                 -- add_comm
  add_assoc    : ∀ a b c, add (add a b) c = add a (add b c)               -- add_assoc
  add_zero     : ∀ a, add a zero = a                                      -- add_zero
  add_neg      : ∀ a, add a (neg a) = zero                                -- add_neg
  sub_def      : ∀ a b, sub a b = add a (neg b)                           -- sub_def
  mul_comm     : ∀ a b, mul a b = mul b a                                 -- mul_comm
  mul_assoc    : ∀ a b c, mul (mul a b) c = mul a (mul b c)               -- mul_assoc
  mul_one      : ∀ a, mul a one = a                                       -- mul_one_ax
  mul_distrib  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)       -- mul_distrib
  zero_ne_one  : zero ≠ one                                               -- zero_ne_one_ax
  div_def      : ∀ a b, b ≠ zero → div a b = mul a (div one b)            -- div_def
  mul_inv      : ∀ a, a ≠ zero → mul a (div one a) = one                  -- mul_inv
  div_zero     : ∀ a, div a zero = zero                                   -- div_zero
  -- order axioms (MachLib.Real.*)
  lt_irrefl        : ∀ a, ¬ lt a a                                        -- lt_irrefl_ax
  lt_trans         : ∀ {a b c}, lt a b → lt b c → lt a c                  -- lt_trans_ax
  lt_total         : ∀ a b, lt a b ∨ a = b ∨ lt b a                       -- lt_total
  le_iff_lt_or_eq  : ∀ a b, le a b ↔ lt a b ∨ a = b                       -- le_iff_lt_or_eq
  add_lt_add_left  : ∀ {a b}, lt a b → ∀ c, lt (add c a) (add c b)        -- add_lt_add_left
  mul_pos          : ∀ {a b}, lt zero a → lt zero b → lt zero (mul a b)   -- mul_pos
  zero_lt_one      : lt zero one                                          -- zero_lt_one_ax

/-- **The witness.** Mathlib's `ℝ` satisfies every field/order axiom of
`MachLib.Real`. Its existence is a machine-checked consistency proof for that
core: all laws below are Mathlib theorems, so the axiom base cannot be
contradictory (it has a model). -/
noncomputable def mathlibModel : OrderedFieldModel where
  R    := ℝ
  zero := 0
  one  := 1
  add  := (· + ·)
  neg  := (- ·)
  sub  := (· - ·)
  mul  := (· * ·)
  div  := (· / ·)
  lt   := (· < ·)
  le   := (· ≤ ·)
  add_comm     := fun a b => by ring
  add_assoc    := fun a b c => by ring
  add_zero     := fun a => by ring
  add_neg      := fun a => by ring
  sub_def      := fun a b => by ring
  mul_comm     := fun a b => by ring
  mul_assoc    := fun a b c => by ring
  mul_one      := fun a => by ring
  mul_distrib  := fun a b c => by ring
  zero_ne_one  := zero_ne_one
  div_def      := fun a b _ => by simp only [div_eq_mul_inv, one_mul]
  mul_inv      := fun a ha => by simp only [one_div]; exact mul_inv_cancel₀ ha
  div_zero     := fun a => div_zero a
  lt_irrefl        := fun a => lt_irrefl a
  lt_trans         := fun h₁ h₂ => lt_trans h₁ h₂
  lt_total         := fun a b => lt_trichotomy a b
  le_iff_lt_or_eq  := fun a b => le_iff_lt_or_eq
  add_lt_add_left  := fun h c => add_lt_add_left h c
  mul_pos          := fun ha hb => mul_pos ha hb
  zero_lt_one      := zero_lt_one

/-! ## Concrete decimal-literal axioms

`MachLib`'s decimal literals desugar through `realOfScientific`; in the model
they desugar through `ℝ`'s own `OfScientific.ofScientific m s e = m · 10^{±e}`.
These three integer-valued literals are exactly the axioms
`realOfScientific_{one,two,three}_dot_zero`, proven here as `ℝ` theorems. -/

theorem realOfScientific_one_dot_zero :
    (OfScientific.ofScientific 10 true 1 : ℝ) = 1 := by norm_num

theorem realOfScientific_two_dot_zero :
    (OfScientific.ofScientific 20 true 1 : ℝ) = 1 + 1 := by norm_num

theorem realOfScientific_three_dot_zero :
    (OfScientific.ofScientific 30 true 1 : ℝ) = 1 + 1 + 1 := by norm_num

end MonogateEML.RealModel
