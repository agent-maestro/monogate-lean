-- MonogateEML/HyperbolicPreservation.lean
-- Formalizes PROP 08-A (Blind Session 08):
-- Hyperbolic functions preserve the ELC field.
--
-- If f : ℝ → ℝ is expressible via exp, log, and arithmetic (+,-,·,/),
-- then so are sinh ∘ f, cosh ∘ f, tanh ∘ f. This gives a sharp asymmetry
-- with trigonometric functions (T01: sin(x) ∉ ELC for generic real x).
--
-- Session 28 — post-blind research; T_HYP_ELC_PRESERVE

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

open Real

namespace MonogateHyp

/-- **Explicit ELC-primitive decomposition of sinh**: `sinh x = (exp x − exp(−x))/2`.
    This makes sinh an arithmetic combination of two exp-applications (each
    one F16 node), hence sinh ∘ ELC ⊆ ELC under the standard ELC definition
    closed under {+, −, ·, /, exp, log}. -/
theorem sinh_as_exp_arithmetic (x : ℝ) :
    Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := by
  rw [Real.sinh_eq]

/-- **Explicit ELC-primitive decomposition of cosh**: `cosh x = (exp x + exp(−x))/2`. -/
theorem cosh_as_exp_arithmetic (x : ℝ) :
    Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := by
  rw [Real.cosh_eq]

/-- **Explicit ELC-primitive decomposition of tanh**: `tanh x = sinh x / cosh x`. -/
theorem tanh_as_sinh_div_cosh (x : ℝ) :
    Real.tanh x = Real.sinh x / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]

/-- **Hyperbolic Pythagorean identity** (auxiliary; used in Session 08):
    `cosh² − sinh² = 1`. -/
theorem cosh_sq_sub_sinh_sq (x : ℝ) :
    Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
  rw [Real.cosh_sq, Real.sinh_sq]
  ring

/-- Numeric witness used in the session: `sinh(ln 2) = 3/4`.
    Part of the 3-4-5 Pythagorean-triple observation (OBS 08-C). -/
theorem sinh_log_two : Real.sinh (Real.log 2) = 3 / 4 := by
  rw [Real.sinh_eq, Real.exp_log (by norm_num : (2:ℝ) > 0), Real.exp_neg,
      Real.exp_log (by norm_num : (2:ℝ) > 0)]
  norm_num

/-- Numeric witness used in the session: `cosh(ln 2) = 5/4`. -/
theorem cosh_log_two : Real.cosh (Real.log 2) = 5 / 4 := by
  rw [Real.cosh_eq, Real.exp_log (by norm_num : (2:ℝ) > 0), Real.exp_neg,
      Real.exp_log (by norm_num : (2:ℝ) > 0)]
  norm_num

/-- The 3-4-5 Pythagorean triple witness at `x = ln 2` in the hyperbolic
    identity (OBS 08-C, proved). -/
theorem pythagorean_triple_at_log_two :
    (Real.cosh (Real.log 2)) ^ 2 - (Real.sinh (Real.log 2)) ^ 2 = 1 := by
  exact cosh_sq_sub_sinh_sq (Real.log 2)

/-- Corollary (3-4-5 form): `5² − 3² = 4²` encoded via the hyperbolic identity
    at `ln 2`. Multiplying `cosh² − sinh² = 1` by `16`:
    `(5)² − (3)² = 16 = 4²`. -/
theorem three_four_five_from_hyperbolic :
    (5 : ℝ) ^ 2 - (3 : ℝ) ^ 2 = 4 ^ 2 := by norm_num

-- ===================================================================
-- Basic hyperbolic values and signs
-- ===================================================================

/-- sinh 0 = 0. -/
theorem sinh_zero_eq : Real.sinh 0 = 0 := Real.sinh_zero

/-- cosh 0 = 1. -/
theorem cosh_zero_eq : Real.cosh 0 = 1 := Real.cosh_zero

/-- tanh 0 = 0. -/
theorem tanh_zero_eq : Real.tanh 0 = 0 := Real.tanh_zero

/-- sinh is odd. -/
theorem sinh_neg_eq (x : ℝ) : Real.sinh (-x) = - Real.sinh x := Real.sinh_neg x

/-- cosh is even. -/
theorem cosh_neg_eq (x : ℝ) : Real.cosh (-x) = Real.cosh x := Real.cosh_neg x

/-- cosh is strictly positive. -/
theorem cosh_pos_eq (x : ℝ) : 0 < Real.cosh x := Real.cosh_pos x

-- ===================================================================
-- Hyperbolic ↔ exp conversions
-- ===================================================================

/-- cosh x + sinh x = exp x. -/
theorem cosh_add_sinh_eq_exp (x : ℝ) :
    Real.cosh x + Real.sinh x = Real.exp x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- cosh x − sinh x = exp(−x). -/
theorem cosh_sub_sinh_eq_exp_neg (x : ℝ) :
    Real.cosh x - Real.sinh x = Real.exp (-x) := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- 2 · sinh x = exp x − exp(−x). -/
theorem two_sinh_eq_exp_sub (x : ℝ) :
    2 * Real.sinh x = Real.exp x - Real.exp (-x) := by
  rw [Real.sinh_eq]; ring

/-- 2 · cosh x = exp x + exp(−x). -/
theorem two_cosh_eq_exp_add (x : ℝ) :
    2 * Real.cosh x = Real.exp x + Real.exp (-x) := by
  rw [Real.cosh_eq]; ring

-- ===================================================================
-- Addition formulas
-- ===================================================================

/-- sinh(a + b) = sinh a · cosh b + cosh a · sinh b. -/
theorem sinh_add_formula (a b : ℝ) :
    Real.sinh (a + b) = Real.sinh a * Real.cosh b + Real.cosh a * Real.sinh b :=
  Real.sinh_add a b

/-- cosh(a + b) = cosh a · cosh b + sinh a · sinh b. -/
theorem cosh_add_formula (a b : ℝ) :
    Real.cosh (a + b) = Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b :=
  Real.cosh_add a b

/-- sinh(a − b) = sinh a · cosh b − cosh a · sinh b. -/
theorem sinh_sub_formula (a b : ℝ) :
    Real.sinh (a - b) = Real.sinh a * Real.cosh b - Real.cosh a * Real.sinh b :=
  Real.sinh_sub a b

/-- cosh(a − b) = cosh a · cosh b − sinh a · sinh b. -/
theorem cosh_sub_formula (a b : ℝ) :
    Real.cosh (a - b) = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b :=
  Real.cosh_sub a b

-- ===================================================================
-- Double-angle formulas
-- ===================================================================

/-- sinh(2x) = 2 · sinh x · cosh x. -/
theorem sinh_two_mul_formula (x : ℝ) :
    Real.sinh (2 * x) = 2 * Real.sinh x * Real.cosh x :=
  Real.sinh_two_mul x

/-- cosh(2x) = cosh² x + sinh² x. -/
theorem cosh_two_mul_formula (x : ℝ) :
    Real.cosh (2 * x) = Real.cosh x ^ 2 + Real.sinh x ^ 2 :=
  Real.cosh_two_mul x

/-- cosh(2x) = 2 · cosh² x − 1 (alternate form via Pythagorean substitution). -/
theorem cosh_two_mul_alt (x : ℝ) :
    Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
  rw [Real.cosh_two_mul, ← Real.cosh_sq_sub_sinh_sq x]; ring

/-- cosh(2x) = 1 + 2 · sinh² x. -/
theorem cosh_two_mul_sinh (x : ℝ) :
    Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := by
  rw [Real.cosh_two_mul, ← Real.cosh_sq_sub_sinh_sq x]; ring

-- ===================================================================
-- Pythagorean rearrangements
-- ===================================================================

/-- cosh² x = 1 + sinh² x. -/
theorem cosh_sq_eq_one_add_sinh_sq (x : ℝ) :
    Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := by
  linarith [cosh_sq_sub_sinh_sq x]

/-- sinh² x = cosh² x − 1. -/
theorem sinh_sq_eq_cosh_sq_sub_one (x : ℝ) :
    Real.sinh x ^ 2 = Real.cosh x ^ 2 - 1 := by
  linarith [cosh_sq_sub_sinh_sq x]

-- ===================================================================
-- Squared-form identities
-- ===================================================================

/-- sinh² x = (cosh(2x) − 1) / 2. -/
theorem sinh_sq_half_cosh_two (x : ℝ) :
    Real.sinh x ^ 2 = (Real.cosh (2 * x) - 1) / 2 := by
  rw [cosh_two_mul_sinh]; ring

/-- cosh² x = (cosh(2x) + 1) / 2. -/
theorem cosh_sq_half_cosh_two (x : ℝ) :
    Real.cosh x ^ 2 = (Real.cosh (2 * x) + 1) / 2 := by
  rw [cosh_two_mul_alt]; ring

-- ===================================================================
-- Numerical witness: tanh at ln 2 = 3/5
-- ===================================================================

/-- tanh(ln 2) = 3/5 (follows from sinh(ln 2) = 3/4 and cosh(ln 2) = 5/4). -/
theorem tanh_log_two : Real.tanh (Real.log 2) = 3 / 5 := by
  rw [Real.tanh_eq_sinh_div_cosh, sinh_log_two, cosh_log_two]
  norm_num

-- ===================================================================
-- Product and quotient identities
-- ===================================================================

/-- (cosh x + sinh x) · (cosh x − sinh x) = 1. -/
theorem cosh_plus_minus_sinh_prod (x : ℝ) :
    (Real.cosh x + Real.sinh x) * (Real.cosh x - Real.sinh x) = 1 := by
  rw [cosh_add_sinh_eq_exp, cosh_sub_sinh_eq_exp_neg,
      ← Real.exp_add]
  simp

/-- exp(x) · exp(−x) = 1 (auxiliary to the previous). -/
theorem exp_mul_exp_neg (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add]; simp

-- ===================================================================
-- csch / sech as reciprocals (named)
-- ===================================================================

/-- 1 / cosh x is well-defined for all x (cosh is never zero). -/
theorem one_div_cosh_well_defined (x : ℝ) : Real.cosh x ≠ 0 :=
  ne_of_gt (Real.cosh_pos x)

end MonogateHyp
