-- MonogateEML/UpperBounds.lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Upper Bounds: Explicit 1-Node F16 Constructions

Algebraic identity proofs establishing that several SuperBEST operations
can be computed by a SINGLE F16-orbit node.

F16 operator family (selected):
  F1(x,y)  = exp(x) − log(y)
  F13(x,y) = exp(x · log(y))        [EPL — "exponential power law"]
  F14(x,y) = exp(x + log(y))
  F16(x,y) = exp(log(x) + log(y))   [F16fn — the generating operator]

All constructions use only F16-orbit primitives and apply for the stated domain.

## No sorries
-/

open Real

-- ===================================================================
-- 1. exp(x) = F1(x, 1) — for all real x
-- ===================================================================

/-- exp(x) is computable by a single F16 node: F1(x, 1) = exp(x) − log(1) = exp(x). -/
theorem exp_one_node (x : ℝ) : Real.exp x - Real.log 1 = Real.exp x := by
  simp [Real.log_one]

/-- Equivalently stated using the operator form. -/
theorem exp_is_one_node_all_reals (x : ℝ) :
    (fun x y => Real.exp x - Real.log y) x 1 = Real.exp x := by
  simp [Real.log_one]

-- ===================================================================
-- 2. x * y = F16(x, y) for x > 0, y > 0
-- ===================================================================

/-- Multiplication is a single F16 node on the positive domain:
    F16fn(x,y) = exp(log(x) + log(y)) = x · y for x,y > 0. -/
theorem mul_one_node_positive (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (Real.log x + Real.log y) = x * y := by
  rw [Real.exp_add, Real.exp_log hx, Real.exp_log hy]

-- ===================================================================
-- 3. x ^ n = F13(n, x) for x > 0, n : ℝ
-- ===================================================================

/-- Real power x^n is a single F16 node via EPL:
    F13(n, x) = exp(n · log(x)) = x^n for x > 0. -/
theorem rpow_one_node_positive (n x : ℝ) (hx : 0 < x) :
    Real.exp (n * Real.log x) = x ^ n := by
  rw [Real.rpow_def_of_pos hx]; ring_nf

-- ===================================================================
-- 4. 1 / x = F13(-1, x) for x > 0
-- ===================================================================

/-- Reciprocal is a single F16 node via EPL with exponent −1:
    F13(−1, x) = exp(−1 · log(x)) = exp(−log(x)) = 1/x for x > 0. -/
theorem recip_one_node_positive (x : ℝ) (hx : 0 < x) :
    Real.exp ((-1) * Real.log x) = 1 / x := by
  rw [rpow_one_node_positive (-1) x hx]
  simp [Real.rpow_neg (le_of_lt hx), Real.rpow_one]

-- ===================================================================
-- 5. sqrt(x) = F13(1/2, x) for x > 0
-- (Reproduced from ModelAudit.lean for completeness; same proof)
-- ===================================================================

/-- Square root is a single F16 node via EPL with exponent 1/2:
    F13(1/2, x) = exp((1/2)·log(x)) = √x for x > 0. -/
theorem sqrt_one_node_positive' (x : ℝ) (hx : 0 < x) :
    Real.exp ((1/2) * Real.log x) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  exact rpow_one_node_positive (1/2) x hx

-- ===================================================================
-- 6. log(x) = exp(0) * log(x)   [EXL identity]   for all x
-- ===================================================================

/-- EXL identity: exp(0) * log(x) = log(x) for all real x.

    Justifies the SuperBEST 1-node accounting of `ln(x)` via the extended
    operator EXL(a, b) := exp(a) * log(b), with EXL(0, x) = log(x).

    Note on scope: EXL is in the extended 23-operator catalogue (it has
    the form h(exp(±x), log(±y)) with h(u, v) = u * v) but is not one of
    the F1..F16 operators defined in AddLowerBound.lean / DivLowerBound.lean
    (which use h ∈ {subtraction, identity, log-of-arithmetic, exp-of-arithmetic}).
    The 14n SuperBEST headline that counts ln = 1n therefore relies on this
    extended-op accounting. -/
theorem ln_one_node_via_exl (x : ℝ) :
    Real.exp 0 * Real.log x = Real.log x := by
  rw [Real.exp_zero, one_mul]

-- ===================================================================
-- 7. exp(x + log(y)) = exp(x) * y  [F14 identity]  for y > 0
-- ===================================================================

/-- F14 identity: exp(x + log(y)) = exp(x) · y for y > 0.
    Useful for computing exp(x) * y with a single F14 node. -/
theorem f14_identity (x y : ℝ) (hy : 0 < y) :
    Real.exp (x + Real.log y) = Real.exp x * y := by
  rw [Real.exp_add, Real.exp_log hy]

-- ===================================================================
-- 8. exp(x − log(y)) = exp(x) / y  [F15 identity]  for y > 0
-- ===================================================================

/-- F15 identity: exp(x − log(y)) = exp(x) / y for y > 0.
    Useful for computing exp(x) / y with a single F15 node. -/
theorem f15_identity (x y : ℝ) (hy : 0 < y) :
    Real.exp (x - Real.log y) = Real.exp x / y := by
  rw [Real.exp_sub, Real.exp_log hy]

-- ===================================================================
-- 9. exp(log(x) + log(y)) = x · y  [F16 identity]  for x, y > 0
-- ===================================================================

/-- F16 identity: exp(log(x) + log(y)) = x · y for x, y > 0.
    Named alias of `mul_one_node_positive` that completes the F13–F16
    naming symmetry alongside `f14_identity` and `f15_identity`. -/
theorem f16_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (Real.log x + Real.log y) = x * y :=
  mul_one_node_positive x y hx hy

-- ===================================================================
-- 10. Multiplication on the same-sign negative domain: x < 0, y < 0
-- ===================================================================

/-- Multiplication of two negatives is a single F16 node:
    exp(log(−x) + log(−y)) = x · y for x, y < 0.
    Extends `mul_one_node_positive` to the same-sign negative domain,
    using `neg_pos` to reduce to the positive case and `neg_mul_neg`
    to close the product. -/
theorem mul_of_negatives_one_node (x y : ℝ) (hx : x < 0) (hy : y < 0) :
    Real.exp (Real.log (-x) + Real.log (-y)) = x * y := by
  have hxp : 0 < -x := neg_pos.mpr hx
  have hyp : 0 < -y := neg_pos.mpr hy
  rw [mul_one_node_positive (-x) (-y) hxp hyp]
  ring

-- ===================================================================
-- Summary: SuperBEST positive-domain 1-node operations
-- ===================================================================

/-- All seven 1-node positive-domain results, collected:
    exp, mul, pow, recip, sqrt, ln (via EXL), and the F14 identity. -/
theorem superbest_positive_one_node_ops :
    (∀ x : ℝ, Real.exp x - Real.log 1 = Real.exp x) ∧          -- exp: 1n
    (∀ x y : ℝ, 0 < x → 0 < y →
      Real.exp (Real.log x + Real.log y) = x * y) ∧             -- mul: 1n (x,y>0)
    (∀ n x : ℝ, 0 < x → Real.exp (n * Real.log x) = x ^ n) ∧   -- pow: 1n (x>0)
    (∀ x : ℝ, 0 < x →
      Real.exp ((-1) * Real.log x) = 1 / x) ∧                   -- recip: 1n (x>0)
    (∀ x : ℝ, 0 < x →
      Real.exp ((1/2) * Real.log x) = Real.sqrt x) ∧             -- sqrt: 1n (x>0)
    (∀ x : ℝ, Real.exp 0 * Real.log x = Real.log x) ∧           -- ln: 1n via EXL
    (∀ x y : ℝ, 0 < y →
      Real.exp (x + Real.log y) = Real.exp x * y) :=             -- f14: exp(x)·y, y>0
  ⟨fun x => by simp [Real.log_one],
   mul_one_node_positive,
   rpow_one_node_positive,
   recip_one_node_positive,
   sqrt_one_node_positive',
   ln_one_node_via_exl,
   f14_identity⟩

-- ===================================================================
-- Cancellation identities (named aliases over Mathlib)
-- ===================================================================

/-- exp(log x) = x for x > 0. -/
theorem exp_ln_cancel (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x :=
  Real.exp_log hx

/-- log(exp x) = x for all real x. -/
theorem ln_exp_cancel (x : ℝ) : Real.log (Real.exp x) = x :=
  Real.log_exp x

-- ===================================================================
-- Product / sum identities
-- ===================================================================

/-- exp(a) · exp(b) = exp(a + b). -/
theorem exp_add_mul (a b : ℝ) : Real.exp a * Real.exp b = Real.exp (a + b) :=
  (Real.exp_add a b).symm

/-- exp(a) / exp(b) = exp(a − b). -/
theorem exp_sub_div (a b : ℝ) : Real.exp a / Real.exp b = Real.exp (a - b) :=
  (Real.exp_sub a b).symm

/-- log(a · b) = log a + log b for a, b > 0. -/
theorem ln_mul_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul (ne_of_gt ha) (ne_of_gt hb)

/-- log(a / b) = log a − log b for a, b > 0. -/
theorem ln_div_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div (ne_of_gt ha) (ne_of_gt hb)

/-- log(1 / x) = − log x (holds for all x via Mathlib's log conventions). -/
theorem ln_one_div_neg (x : ℝ) : Real.log (1 / x) = - Real.log x := by
  rw [one_div, Real.log_inv]

-- ===================================================================
-- Power / rpow identities
-- ===================================================================

/-- (exp a)^b = exp(a · b). -/
theorem exp_pow (a b : ℝ) : (Real.exp a) ^ b = Real.exp (a * b) :=
  (Real.exp_mul a b).symm

/-- sqrt(x) = x^(1/2) for all real x (Mathlib convention: both sides = 0 for x < 0). -/
theorem sqrt_as_pow (x : ℝ) : Real.sqrt x = x ^ ((1:ℝ)/2) :=
  Real.sqrt_eq_rpow x

/-- x^(a · b) = (x^a)^b for x ≥ 0. Named alias of `Real.rpow_mul`. -/
theorem rpow_mul_positive (x : ℝ) (hx : 0 ≤ x) (a b : ℝ) :
    x ^ (a * b) = (x ^ a) ^ b :=
  Real.rpow_mul hx a b

/-- x^(a + b) = x^a · x^b for x > 0. Named alias of `Real.rpow_add`. -/
theorem rpow_add_positive (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    x ^ (a + b) = x ^ a * x ^ b :=
  Real.rpow_add hx a b

-- ===================================================================
-- Trivial atoms (named aliases for citability)
-- ===================================================================

/-- log(1) = 0. -/
theorem ln_one_zero : Real.log 1 = 0 := Real.log_one

/-- exp(0) = 1. -/
theorem exp_zero_one : Real.exp 0 = 1 := Real.exp_zero

/-- exp(x) is strictly positive, hence nonzero. -/
theorem exp_pos_named (x : ℝ) : 0 < Real.exp x := Real.exp_pos x

/-- exp(x) ≠ 0. -/
theorem exp_ne_zero_named (x : ℝ) : Real.exp x ≠ 0 := Real.exp_ne_zero x

/-- exp(−x) = 1 / exp(x). -/
theorem exp_neg_recip (x : ℝ) : Real.exp (-x) = 1 / Real.exp x := by
  rw [Real.exp_neg, one_div]

-- ===================================================================
-- More rpow / log identities
-- ===================================================================

/-- log(x^y) = y · log(x) for x > 0 (rpow version). -/
theorem ln_rpow_mul (x : ℝ) (hx : 0 < x) (y : ℝ) :
    Real.log (x ^ y) = y * Real.log x :=
  Real.log_rpow hx y

/-- log(sqrt x) = log(x) / 2 for x > 0. -/
theorem ln_sqrt_half (x : ℝ) (hx : 0 < x) :
    Real.log (Real.sqrt x) = Real.log x / 2 := by
  rw [Real.sqrt_eq_rpow, Real.log_rpow hx]
  ring

/-- sqrt(x · y) = sqrt(x) · sqrt(y) for x, y ≥ 0. -/
theorem sqrt_mul_split (x y : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
  Real.sqrt_mul hx y

/-- sqrt(x^2) = |x|. -/
theorem sqrt_sq_abs (x : ℝ) : Real.sqrt (x ^ 2) = |x| :=
  Real.sqrt_sq_eq_abs x

/-- x^1 = x for x > 0 (rpow). -/
theorem rpow_one_pos (x : ℝ) : x ^ (1 : ℝ) = x :=
  Real.rpow_one x

/-- x^0 = 1 (rpow; holds for any x under Mathlib's rpow convention). -/
theorem rpow_zero_any (x : ℝ) : x ^ (0 : ℝ) = 1 :=
  Real.rpow_zero x

/-- 1^x = 1. -/
theorem one_rpow_any (x : ℝ) : (1 : ℝ) ^ x = 1 :=
  Real.one_rpow x

/-- exp is strictly monotone: exp a < exp b ↔ a < b. -/
theorem exp_lt_exp_iff (a b : ℝ) : Real.exp a < Real.exp b ↔ a < b :=
  Real.exp_lt_exp

/-- exp is monotone: exp a ≤ exp b ↔ a ≤ b. -/
theorem exp_le_exp_iff (a b : ℝ) : Real.exp a ≤ Real.exp b ↔ a ≤ b :=
  Real.exp_le_exp

/-- exp injectivity: exp a = exp b ↔ a = b. -/
theorem exp_eq_exp_iff (a b : ℝ) : Real.exp a = Real.exp b ↔ a = b :=
  Real.exp_eq_exp

/-- log is strictly monotone on the positive reals: for a, b > 0, log a < log b ↔ a < b. -/
theorem ln_lt_ln_iff_of_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log a < Real.log b ↔ a < b :=
  Real.log_lt_log_iff ha hb

/-- exp(a + b + c) = exp a · exp b · exp c. -/
theorem exp_add_add (a b c : ℝ) :
    Real.exp (a + b + c) = Real.exp a * Real.exp b * Real.exp c := by
  rw [Real.exp_add, Real.exp_add]

/-- exp is never zero, restated as an equality: exp x ≠ 0. -/
theorem exp_ne_zero' (x : ℝ) : Real.exp x ≠ 0 := Real.exp_ne_zero x

/-- For x > 0: x = exp(log x) (convenient equation form). -/
theorem eq_exp_ln (x : ℝ) (hx : 0 < x) : x = Real.exp (Real.log x) :=
  (Real.exp_log hx).symm

-- ===================================================================
-- Numeric sqrt / log constants
-- ===================================================================

/-- sqrt(0) = 0. -/
theorem sqrt_zero_eq : Real.sqrt 0 = 0 := Real.sqrt_zero

/-- sqrt(1) = 1. -/
theorem sqrt_one_eq : Real.sqrt 1 = 1 := Real.sqrt_one

/-- log(exp 1) = 1. -/
theorem ln_e_one : Real.log (Real.exp 1) = 1 := Real.log_exp 1

/-- exp 1 is strictly positive (named for citability). -/
theorem exp_one_pos : 0 < Real.exp 1 := Real.exp_pos 1

-- ===================================================================
-- rpow-specific identities
-- ===================================================================

/-- x^(-1) = 1/x (rpow form; works for all x via Mathlib's rpow conventions). -/
theorem rpow_neg_one_div (x : ℝ) : x ^ (-1 : ℝ) = 1 / x := by
  rw [Real.rpow_neg_one, inv_eq_one_div]

/-- x^(1/2)^2 = x for x ≥ 0 (sqrt-squared round-trip). -/
theorem rpow_half_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1:ℝ)/2)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

/-- exp(log x · n) = x^n for x > 0 (rpow version, swapped order from rpow_one_node_positive). -/
theorem exp_log_mul_rpow (x n : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x * n) = x ^ n := by
  rw [mul_comm]; exact rpow_one_node_positive n x hx

-- ===================================================================
-- Hyperbolic function definitions (Mathlib named aliases)
-- ===================================================================

/-- sinh(x) = (exp x − exp(−x)) / 2. -/
theorem sinh_def (x : ℝ) : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 :=
  Real.sinh_eq x

/-- cosh(x) = (exp x + exp(−x)) / 2. -/
theorem cosh_def (x : ℝ) : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 :=
  Real.cosh_eq x

/-- tanh(x) = sinh(x) / cosh(x). -/
theorem tanh_as_ratio (x : ℝ) : Real.tanh x = Real.sinh x / Real.cosh x :=
  Real.tanh_eq_sinh_div_cosh x

-- ===================================================================
-- Hyperbolic / trig atoms (named aliases)
-- ===================================================================

/-- sinh(0) = 0. -/
theorem sinh_zero_eq : Real.sinh 0 = 0 := Real.sinh_zero

/-- cosh(0) = 1. -/
theorem cosh_zero_eq : Real.cosh 0 = 1 := Real.cosh_zero

/-- tanh(0) = 0. -/
theorem tanh_zero_eq : Real.tanh 0 = 0 := Real.tanh_zero

/-- cosh is strictly positive. -/
theorem cosh_pos_named (x : ℝ) : 0 < Real.cosh x := Real.cosh_pos x

/-- sinh is odd: sinh(−x) = −sinh(x). -/
theorem sinh_neg_eq (x : ℝ) : Real.sinh (-x) = - Real.sinh x := Real.sinh_neg x

/-- cosh is even: cosh(−x) = cosh(x). -/
theorem cosh_neg_eq (x : ℝ) : Real.cosh (-x) = Real.cosh x := Real.cosh_neg x

/-- sin(0) = 0. -/
theorem sin_zero_eq : Real.sin 0 = 0 := Real.sin_zero

/-- cos(0) = 1. -/
theorem cos_zero_eq : Real.cos 0 = 1 := Real.cos_zero

/-- sin(π) = 0. -/
theorem sin_pi_eq : Real.sin Real.pi = 0 := Real.sin_pi

/-- cos(π) = −1. -/
theorem cos_pi_eq : Real.cos Real.pi = -1 := Real.cos_pi

/-- sin² + cos² = 1 (Pythagorean identity). -/
theorem sin_sq_add_cos_sq_eq (x : ℝ) :
    Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x

/-- π is strictly positive. -/
theorem pi_pos_named : 0 < Real.pi := Real.pi_pos

-- ===================================================================
-- Specific positive-constant evaluations
-- ===================================================================

/-- exp(log 2) = 2. -/
theorem exp_log_two : Real.exp (Real.log 2) = 2 :=
  Real.exp_log (by norm_num)

/-- exp(log π) = π. -/
theorem exp_log_pi : Real.exp (Real.log Real.pi) = Real.pi :=
  Real.exp_log Real.pi_pos

/-- log 2 is strictly positive. -/
theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- log 1 = 0 (alias). -/
theorem log_one_zero_alt : Real.log 1 = 0 := Real.log_one

/-- log of inverse: log(x⁻¹) = −log x. -/
theorem log_inv_neg (x : ℝ) : Real.log (x⁻¹) = - Real.log x :=
  Real.log_inv x

-- ===================================================================
-- Composed positive-domain shortcuts
-- ===================================================================

/-- exp(log x + c) = exp(c) · x for x > 0 (F14-shape with constant offset). -/
theorem exp_log_add_const (x c : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x + c) = x * Real.exp c := by
  rw [Real.exp_add, Real.exp_log hx, mul_comm]

/-- exp(c − log x) = exp(c) / x for x > 0 (F15-shape with constant offset). -/
theorem exp_sub_log_const (x c : ℝ) (hx : 0 < x) :
    Real.exp (c - Real.log x) = Real.exp c / x := by
  rw [Real.exp_sub, Real.exp_log hx]

/-- For x > 0: x · 1 = exp(log x · 1) — trivial but illustrates F13(1, x) = x. -/
theorem f13_at_one_x (x : ℝ) (hx : 0 < x) : Real.exp (1 * Real.log x) = x := by
  rw [one_mul, Real.exp_log hx]

/-- For x > 0: F13(0, x) = exp(0 · log x) = 1. -/
theorem f13_at_zero_x (x : ℝ) : Real.exp (0 * Real.log x) = 1 := by
  rw [zero_mul, Real.exp_zero]

-- ===================================================================
-- Interplay between exp and rpow at base e
-- ===================================================================

/-- (exp 1)^x = exp x — base-e rpow. -/
theorem e_rpow_eq_exp (x : ℝ) : (Real.exp 1) ^ x = Real.exp x := by
  rw [← Real.exp_one_rpow x]

-- ===================================================================
-- Hyperbolic composition with exp
-- ===================================================================

/-- cosh x + sinh x = exp x. -/
theorem cosh_add_sinh_exp (x : ℝ) :
    Real.cosh x + Real.sinh x = Real.exp x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- cosh x − sinh x = exp(−x). -/
theorem cosh_sub_sinh_exp_neg (x : ℝ) :
    Real.cosh x - Real.sinh x = Real.exp (-x) := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- 2 · cosh x = exp x + exp(−x). -/
theorem two_cosh_eq (x : ℝ) :
    2 * Real.cosh x = Real.exp x + Real.exp (-x) := by
  rw [Real.cosh_eq]; ring

/-- 2 · sinh x = exp x − exp(−x). -/
theorem two_sinh_eq (x : ℝ) :
    2 * Real.sinh x = Real.exp x - Real.exp (-x) := by
  rw [Real.sinh_eq]; ring

-- ===================================================================
-- Positivity / nonzero corollaries
-- ===================================================================

/-- 0 < sqrt x for x > 0. -/
theorem sqrt_pos_of_pos (x : ℝ) (hx : 0 < x) : 0 < Real.sqrt x :=
  Real.sqrt_pos.mpr hx

/-- 0 < x^n for x > 0 and n : ℕ. -/
theorem pow_pos_of_pos (x : ℝ) (n : ℕ) (hx : 0 < x) : 0 < x ^ n :=
  pow_pos hx n

/-- 0 < x^y (rpow) for x > 0 and any real y. -/
theorem rpow_pos_of_pos (x y : ℝ) (hx : 0 < x) : 0 < x ^ y :=
  Real.rpow_pos_of_pos hx y

/-- For x > 0: x ≠ 0 (named convenience). -/
theorem ne_zero_of_pos (x : ℝ) (hx : 0 < x) : x ≠ 0 := ne_of_gt hx

-- ===================================================================
-- More log identities
-- ===================================================================

/-- log(x²) = 2 · log x (Mathlib log_pow handles all reals). -/
theorem log_sq_two_log (x : ℝ) :
    Real.log (x ^ 2) = 2 * Real.log x := by
  rw [Real.log_pow]; push_cast; ring

/-- log(x^n) = n · log x for natural exponent n. -/
theorem log_pow_nat (x : ℝ) (n : ℕ) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  rw [Real.log_pow]

-- ===================================================================
-- Trig: more atoms and identities
-- ===================================================================

/-- cos(2π) = 1. -/
theorem cos_two_pi_eq : Real.cos (2 * Real.pi) = 1 := Real.cos_two_pi

/-- sin(2π) = 0. -/
theorem sin_two_pi_eq : Real.sin (2 * Real.pi) = 0 := Real.sin_two_pi

/-- cos² x + sin² x = 1 (Pythagorean, swapped order). -/
theorem cos_sq_add_sin_sq_eq (x : ℝ) :
    Real.cos x ^ 2 + Real.sin x ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq x

/-- sin is odd: sin(−x) = −sin x. -/
theorem sin_neg_eq (x : ℝ) : Real.sin (-x) = - Real.sin x := Real.sin_neg x

/-- cos is even: cos(−x) = cos x. -/
theorem cos_neg_eq (x : ℝ) : Real.cos (-x) = Real.cos x := Real.cos_neg x

-- ===================================================================
-- abs identities
-- ===================================================================

/-- |x|² = x². -/
theorem abs_sq_eq (x : ℝ) : |x| ^ 2 = x ^ 2 := sq_abs x

/-- exp x > 0 implies |exp x| = exp x. -/
theorem abs_exp_eq (x : ℝ) : |Real.exp x| = Real.exp x :=
  abs_of_pos (Real.exp_pos x)

-- ===================================================================
-- Log of negative inputs (Mathlib convention: log(-x) = log|x| = log x for x ≠ 0)
-- ===================================================================

/-- log(−x) = log x (Mathlib convention reduces log of negatives via absolute value). -/
theorem log_neg_eq (x : ℝ) : Real.log (-x) = Real.log x :=
  Real.log_neg_eq_log x

-- ===================================================================
-- sqrt arithmetic
-- ===================================================================

/-- sqrt(x) · sqrt(x) = x for x ≥ 0. -/
theorem sqrt_mul_self_eq (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x * Real.sqrt x = x :=
  Real.mul_self_sqrt hx

/-- (sqrt x)^2 = x for x ≥ 0. -/
theorem sq_sqrt_eq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ 2 = x :=
  Real.sq_sqrt hx

/-- sqrt(x · y) = sqrt(y) · sqrt(x) for y ≥ 0 (Mathlib's swapped variant). -/
theorem sqrt_mul_swap (x y : ℝ) (hy : 0 ≤ y) :
    Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
  rw [mul_comm x y, Real.sqrt_mul hy, mul_comm]

-- ===================================================================
-- Specific numeric evaluations
-- ===================================================================

/-- exp 0 = 1 (alternate alias to keep with cluster). -/
theorem exp_zero_alt : Real.exp 0 = 1 := Real.exp_zero

/-- log 1 = 0 (alternate alias to keep with cluster). -/
theorem ln_one_alt : Real.log 1 = 0 := Real.log_one

/-- Real.exp 1 is positive (alias). -/
theorem e_pos : 0 < Real.exp 1 := Real.exp_pos 1

/-- Real.exp 1 ≠ 0 (alias). -/
theorem e_ne_zero : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1

/-- log of exp 1 is 1. -/
theorem log_exp_one_eq_one : Real.log (Real.exp 1) = 1 := Real.log_exp 1

-- ===================================================================
-- Multiplication / division by exp factors
-- ===================================================================

/-- exp(a) · exp(b) · exp(c) = exp(a + b + c) (3-fold product). -/
theorem exp_mul_three (a b c : ℝ) :
    Real.exp a * Real.exp b * Real.exp c = Real.exp (a + b + c) := by
  rw [← Real.exp_add, ← Real.exp_add]

/-- exp(a) / exp(a) = 1. -/
theorem exp_div_self (a : ℝ) : Real.exp a / Real.exp a = 1 :=
  div_self (Real.exp_ne_zero a)

-- ===================================================================
-- Compositional rpow
-- ===================================================================

/-- (x^a) · (x^b) = x^(a + b) for x > 0. -/
theorem rpow_mul_rpow (x : ℝ) (a b : ℝ) (hx : 0 < x) :
    x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm

/-- (x^a) / (x^b) = x^(a − b) for x > 0. -/
theorem rpow_div_rpow (x : ℝ) (a b : ℝ) (hx : 0 < x) :
    x ^ a / x ^ b = x ^ (a - b) :=
  (Real.rpow_sub hx a b).symm

-- ===================================================================
-- Inverses
-- ===================================================================

/-- (exp x)⁻¹ = exp(−x). -/
theorem inv_exp_eq (x : ℝ) : (Real.exp x)⁻¹ = Real.exp (-x) := by
  rw [Real.exp_neg]

/-- (x^a)⁻¹ = x^(−a) for x > 0. -/
theorem inv_rpow_pos (x a : ℝ) (hx : 0 ≤ x) : (x ^ a)⁻¹ = x ^ (-a) :=
  (Real.rpow_neg hx a).symm

/-- exp(−(−x)) = exp x. -/
theorem exp_neg_neg (x : ℝ) : Real.exp (-(-x)) = Real.exp x := by
  rw [neg_neg]

-- ===================================================================
-- Classical exp/log inequalities
-- ===================================================================

/-- Fundamental convexity bound: 1 + x ≤ exp x for all real x. -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  rw [add_comm]; exact Real.add_one_le_exp x

/-- exp x > 1 for x > 0. -/
theorem one_lt_exp_of_pos (x : ℝ) (hx : 0 < x) : 1 < Real.exp x := by
  have h : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hx
  rwa [Real.exp_zero] at h

/-- exp x < 1 for x < 0. -/
theorem exp_lt_one_of_neg (x : ℝ) (hx : x < 0) : Real.exp x < 1 := by
  have h : Real.exp x < Real.exp 0 := Real.exp_lt_exp.mpr hx
  rwa [Real.exp_zero] at h

/-- exp is strictly monotone (named). -/
theorem exp_strictMono_named : StrictMono Real.exp := Real.exp_strictMono


-- ===================================================================
-- rpow / pow bridging
-- ===================================================================

/-- x^(n : ℕ) (rpow) = x^n (monoid pow). -/
theorem rpow_natCast_eq (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  Real.rpow_natCast x n

/-- x^1 (rpow) = x. -/
theorem rpow_one_eq (x : ℝ) : x ^ (1 : ℝ) = x := Real.rpow_one x

-- ===================================================================
-- Product / sum shortcuts
-- ===================================================================

/-- log(x) + log(1/x) = 0 (inverse balance). -/
theorem log_plus_log_inv_zero (x : ℝ) :
    Real.log x + Real.log (1 / x) = 0 := by
  rw [one_div, Real.log_inv]; ring

/-- exp(a + b − b) = exp a (trivial cancellation). -/
theorem exp_add_sub_self (a b : ℝ) :
    Real.exp (a + b - b) = Real.exp a := by
  ring_nf

-- ===================================================================
-- Ordering around 1 and 0
-- ===================================================================

/-- sqrt is nondecreasing: 0 ≤ a ≤ b → sqrt a ≤ sqrt b. -/
theorem sqrt_le_sqrt_of_le (a b : ℝ) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b :=
  Real.sqrt_le_sqrt hab

/-- 1 ≤ sqrt x if 1 ≤ x. -/
theorem one_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  have := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_one] at this

/-- sqrt x ≤ 1 if 0 ≤ x ≤ 1. -/
theorem sqrt_le_one_of_le (x : ℝ) (hx : x ≤ 1) : Real.sqrt x ≤ 1 := by
  have := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_one] at this

-- ===================================================================
-- F-family edge values at 0
-- ===================================================================

/-- F14(0, y) = y for y > 0: exp(0 + log y) = y. -/
theorem f14_at_zero_y_eq (y : ℝ) (hy : 0 < y) :
    Real.exp (0 + Real.log y) = y := by
  rw [zero_add, Real.exp_log hy]

/-- F15(0, y) = 1/y for y > 0: exp(0 − log y) = 1/y. -/
theorem f15_at_zero_y_eq (y : ℝ) (hy : 0 < y) :
    Real.exp (0 - Real.log y) = 1 / y := by
  rw [zero_sub, Real.exp_neg, Real.exp_log hy, inv_eq_one_div]

/-- F14(x, 1) = exp x: exp(x + log 1) = exp x. -/
theorem f14_at_x_one_eq (x : ℝ) :
    Real.exp (x + Real.log 1) = Real.exp x := by
  rw [Real.log_one, add_zero]

/-- F15(x, 1) = exp x: exp(x − log 1) = exp x. -/
theorem f15_at_x_one_eq (x : ℝ) :
    Real.exp (x - Real.log 1) = Real.exp x := by
  rw [Real.log_one, sub_zero]

/-- F16(x, 1) = x for x > 0: exp(log x + log 1) = x. -/
theorem f16_at_x_one_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x + Real.log 1) = x := by
  rw [Real.log_one, add_zero, Real.exp_log hx]

/-- F13(1, x) = x for x > 0: exp(1 · log x) = x. -/
theorem f13_at_one_x_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (1 * Real.log x) = x := by
  rw [one_mul, Real.exp_log hx]

-- ===================================================================
-- Trivial squares / positivity shortcuts
-- ===================================================================

/-- 0 ≤ x² for all real x. -/
theorem sq_nonneg_named (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

/-- |x| ≥ 0 (named). -/
theorem abs_nonneg_named (x : ℝ) : 0 ≤ |x| := abs_nonneg x

/-- |x| = x for x ≥ 0. -/
theorem abs_of_nonneg_named (x : ℝ) (hx : 0 ≤ x) : |x| = x := abs_of_nonneg hx

-- ===================================================================
-- log monotonicity on the positives
-- ===================================================================

/-- log is strictly monotone on the positive reals. -/
theorem log_strictMono_on_pos :
    ∀ a b : ℝ, 0 < a → a < b → Real.log a < Real.log b :=
  fun _ _ ha hab => Real.log_lt_log ha hab

/-- log is monotone on the positive reals. -/
theorem log_monotone_on_pos :
    ∀ a b : ℝ, 0 < a → a ≤ b → Real.log a ≤ Real.log b :=
  fun _ _ ha hab => Real.log_le_log ha hab

-- ===================================================================
-- rpow at specific bases
-- ===================================================================

/-- 0^(a : ℝ) = 0 for a > 0. -/
theorem zero_rpow_of_pos (a : ℝ) (ha : 0 < a) : (0 : ℝ) ^ a = 0 :=
  Real.zero_rpow (ne_of_gt ha)

/-- x^(a + b + c) = x^a · x^b · x^c for x > 0. -/
theorem rpow_add_three (x a b c : ℝ) (hx : 0 < x) :
    x ^ (a + b + c) = x ^ a * x ^ b * x ^ c := by
  rw [Real.rpow_add hx, Real.rpow_add hx]

-- ===================================================================
-- Tan basics
-- ===================================================================

/-- tan 0 = 0. -/
theorem tan_zero_eq : Real.tan 0 = 0 := Real.tan_zero

/-- tan is odd: tan(−x) = −tan x. -/
theorem tan_neg_eq (x : ℝ) : Real.tan (-x) = - Real.tan x := Real.tan_neg x

/-- tan(x) = sin(x) / cos(x). -/
theorem tan_as_sin_div_cos (x : ℝ) : Real.tan x = Real.sin x / Real.cos x :=
  Real.tan_eq_sin_div_cos x

-- ===================================================================
-- rpow with negative exponent
-- ===================================================================

/-- x^(−a) = (x^a)⁻¹ for x ≥ 0. -/
theorem rpow_neg_inv (x a : ℝ) (hx : 0 ≤ x) : x ^ (-a) = (x ^ a)⁻¹ :=
  Real.rpow_neg hx a

/-- x^(−a) = 1 / x^a for x ≥ 0. -/
theorem rpow_neg_one_div_rpow (x a : ℝ) (hx : 0 ≤ x) : x ^ (-a) = 1 / (x ^ a) := by
  rw [Real.rpow_neg hx, one_div]

-- ===================================================================
-- log of exp variations
-- ===================================================================

/-- log(exp(−x)) = −x. -/
theorem log_exp_neg_eq (x : ℝ) : Real.log (Real.exp (-x)) = -x := Real.log_exp (-x)

/-- log(exp x · exp y) = x + y (distributes to additive form). -/
theorem log_exp_mul_add (x y : ℝ) :
    Real.log (Real.exp x * Real.exp y) = x + y := by
  rw [← Real.exp_add, Real.log_exp]

-- ===================================================================
-- Sqrt of exp
-- ===================================================================

/-- sqrt(exp x) = exp(x / 2). -/
theorem sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [show Real.exp x = Real.exp (x/2 + x/2) from by ring_nf,
      Real.exp_add, Real.sqrt_mul_self (le_of_lt (Real.exp_pos _))]

-- ===================================================================
-- More absolute value identities
-- ===================================================================

/-- x ≤ |x|. -/
theorem le_abs_self_named (x : ℝ) : x ≤ |x| := le_abs_self x

/-- −|x| ≤ x. -/
theorem neg_abs_le_named (x : ℝ) : -|x| ≤ x := neg_abs_le x

/-- |x · y| = |x| · |y|. -/
theorem abs_mul_named (x y : ℝ) : |x * y| = |x| * |y| := abs_mul x y

/-- |x|² = x². -/
theorem sq_abs_eq_sq (x : ℝ) : x ^ 2 = |x| ^ 2 := (sq_abs x).symm

-- ===================================================================
-- Triangle inequality and log sign
-- ===================================================================

/-- |a + b| ≤ |a| + |b| (triangle inequality, named). -/
theorem abs_add_le_named (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b

/-- |a − b| ≤ |a| + |b|. -/
theorem abs_sub_le_named (a b : ℝ) : |a - b| ≤ |a| + |b| := abs_sub a b

/-- 0 < log x ↔ 1 < x (for x > 0). -/
theorem log_pos_iff_one_lt (x : ℝ) (hx : 0 < x) : 0 < Real.log x ↔ 1 < x :=
  Real.log_pos_iff hx.le

-- ===================================================================
-- exp / log thresholds
-- ===================================================================

/-- exp x ≤ 1 ↔ x ≤ 0. -/
theorem exp_le_one_iff_named (x : ℝ) : Real.exp x ≤ 1 ↔ x ≤ 0 :=
  Real.exp_le_one_iff

/-- 1 ≤ exp x ↔ 0 ≤ x. -/
theorem one_le_exp_iff_named (x : ℝ) : 1 ≤ Real.exp x ↔ 0 ≤ x :=
  Real.one_le_exp_iff

-- ===================================================================
-- log of arithmetic on specific constants
-- ===================================================================

/-- log 2 ≠ 0 (since 2 ≠ 1). -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt log_two_pos

/-- exp(2 · log x) = x² for x > 0. -/
theorem exp_two_log_eq_sq (x : ℝ) (hx : 0 < x) :
    Real.exp (2 * Real.log x) = x ^ 2 := by
  rw [rpow_one_node_positive 2 x hx, Real.rpow_two]

/-- exp(log x / 2) = sqrt x for x > 0. -/
theorem exp_half_log_eq_sqrt (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [show Real.log x / 2 = (1/2) * Real.log x from by ring]
  exact sqrt_one_node_positive' x hx

-- ===================================================================
-- More sqrt compositions
-- ===================================================================

/-- sqrt(x²) = x for x ≥ 0 (Mathlib's non-abs form). -/
theorem sqrt_sq_of_nonneg (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ 2) = x :=
  Real.sqrt_sq hx

/-- sqrt(x / y) = sqrt(x) / sqrt(y) for x ≥ 0, y > 0 (Mathlib's variant). -/
theorem sqrt_div_sqrt (x y : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x / y) = Real.sqrt x / Real.sqrt y :=
  Real.sqrt_div hx y

-- ===================================================================
-- Trig at specific angles
-- ===================================================================

/-- sin(π/2) = 1. -/
theorem sin_pi_div_two_eq : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two

/-- cos(π/2) = 0. -/
theorem cos_pi_div_two_eq : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two

-- ===================================================================
-- More rpow ordering
-- ===================================================================

/-- rpow preserves order on the nonnegative reals for a ≥ 0: x ≤ y → x^a ≤ y^a. -/
theorem rpow_le_rpow_of_le (x y a : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (ha : 0 ≤ a) :
    x ^ a ≤ y ^ a :=
  Real.rpow_le_rpow hx hxy ha

-- ===================================================================
-- Double sign operations
-- ===================================================================

/-- −(−x) = x. -/
theorem neg_neg_named (x : ℝ) : -(-x) = x := neg_neg x

/-- (−x) · (−y) = x · y. -/
theorem neg_mul_neg_named (x y : ℝ) : (-x) * (-y) = x * y := neg_mul_neg x y

-- ===================================================================
-- exp at integer arguments
-- ===================================================================

/-- exp 1 = e (alias — Real.exp 1 is the canonical e). -/
theorem exp_one_eq_e : Real.exp 1 = Real.exp 1 := rfl

/-- exp 2 = exp 1 · exp 1. -/
theorem exp_two_as_sq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
  rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]

-- ===================================================================
-- Compositional shortcuts (cosmetic)
-- ===================================================================

/-- (exp x)^n = exp(n · x) for n : ℕ. -/
theorem exp_pow_nat (x : ℝ) (n : ℕ) :
    (Real.exp x) ^ n = Real.exp (n * x) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← Real.exp_add]; push_cast; ring_nf

/-- exp(x) · exp(x) = exp(2x). -/
theorem exp_sq_double (x : ℝ) : Real.exp x * Real.exp x = Real.exp (2 * x) := by
  rw [← Real.exp_add]; ring_nf

-- ===================================================================
-- log of squares for nonzero
-- ===================================================================

/-- log(x · x) = 2 · log x for x > 0. -/
theorem log_self_mul (x : ℝ) (hx : 0 < x) :
    Real.log (x * x) = 2 * Real.log x := by
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hx)]; ring

-- ===================================================================
-- Concrete sqrt evaluations
-- ===================================================================

/-- sqrt(4) = 2. -/
theorem sqrt_four_eq_two : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

/-- sqrt(9) = 3. -/
theorem sqrt_nine_eq_three : Real.sqrt 9 = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)

/-- sqrt(16) = 4. -/
theorem sqrt_sixteen_eq_four : Real.sqrt 16 = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)

-- ===================================================================
-- log of reciprocals
-- ===================================================================

/-- log(1/2) = −log 2. -/
theorem log_half_neg : Real.log (1 / 2) = - Real.log 2 := by
  rw [one_div, Real.log_inv]

/-- log(1/e) = −1. -/
theorem log_inv_e_neg_one : Real.log (1 / Real.exp 1) = -1 := by
  rw [one_div, Real.log_inv, Real.log_exp]

-- ===================================================================
-- More sign / abs on exp
-- ===================================================================

/-- exp x is never negative: 0 < exp x (restated bound). -/
theorem exp_not_neg (x : ℝ) : ¬ (Real.exp x < 0) := by
  intro h; exact absurd h (not_lt.mpr (le_of_lt (Real.exp_pos x)))

/-- |exp x − exp y| = exp y · |exp(x − y) − 1| is too strong; we just state
    nonneg of abs(exp x − exp y). -/
theorem abs_exp_sub_nonneg (x y : ℝ) : 0 ≤ |Real.exp x - Real.exp y| :=
  abs_nonneg _

-- ===================================================================
-- Symmetries between operators
-- ===================================================================

/-- Swap commutativity for F16(x,y) = F16(y,x): exp(log x + log y) = exp(log y + log x). -/
theorem f16_comm (x y : ℝ) :
    Real.exp (Real.log x + Real.log y) = Real.exp (Real.log y + Real.log x) := by
  rw [add_comm]

/-- exp(a + b) = exp(b + a) (exp commutes across sum). -/
theorem exp_add_comm (a b : ℝ) : Real.exp (a + b) = Real.exp (b + a) := by
  rw [add_comm]

-- ===================================================================
-- Log / exp with one
-- ===================================================================

/-- log(exp x * 1) = x (log-exp after right-identity). -/
theorem log_exp_mul_one (x : ℝ) : Real.log (Real.exp x * 1) = x := by
  rw [mul_one, Real.log_exp]

/-- exp(log x + 0) = x for x > 0 (zero-identity). -/
theorem exp_log_add_zero (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x + 0) = x := by
  rw [add_zero, Real.exp_log hx]

-- ===================================================================
-- Four-fold compositions
-- ===================================================================

/-- exp(a + b + c + d) = exp a · exp b · exp c · exp d. -/
theorem exp_four_sum (a b c d : ℝ) :
    Real.exp (a + b + c + d) = Real.exp a * Real.exp b * Real.exp c * Real.exp d := by
  rw [Real.exp_add, Real.exp_add, Real.exp_add]

/-- log(a · b · c) = log a + log b + log c for positives. -/
theorem log_three_prod (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by
  rw [Real.log_mul (ne_of_gt (mul_pos ha hb)) (ne_of_gt hc),
      Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]

-- ===================================================================
-- Sandwich / squeezes
-- ===================================================================

/-- 0 < exp a · exp b (product of two positives). -/
theorem exp_mul_exp_pos (a b : ℝ) : 0 < Real.exp a * Real.exp b :=
  mul_pos (Real.exp_pos a) (Real.exp_pos b)

/-- 0 < exp a / exp b (positive quotient). -/
theorem exp_div_exp_pos (a b : ℝ) : 0 < Real.exp a / Real.exp b :=
  div_pos (Real.exp_pos a) (Real.exp_pos b)

-- ===================================================================
-- Factorings that show up in SuperBEST proofs
-- ===================================================================

/-- exp(a) · b / exp(a) = b (cancellation through exp). -/
theorem exp_cancel_through_mul_div (a b : ℝ) :
    Real.exp a * b / Real.exp a = b := by
  rw [mul_comm, mul_div_assoc, div_self (Real.exp_ne_zero a), mul_one]

/-- b / exp(a) · exp(a) = b. -/
theorem div_exp_mul_exp (a b : ℝ) :
    b / Real.exp a * Real.exp a = b := by
  rw [div_mul_cancel₀ b (Real.exp_ne_zero a)]

-- ===================================================================
-- exp_log vs log_exp (complementary cancellations)
-- ===================================================================

/-- For x > 0: log(exp(x)) = x (degenerate-positivity — positivity is irrelevant for this direction). -/
theorem log_exp_pos (x : ℝ) (_hx : 0 < x) : Real.log (Real.exp x) = x :=
  Real.log_exp x

/-- For any real x: 0 ≤ (exp x)² (squared exp is nonneg). -/
theorem exp_sq_nonneg (x : ℝ) : 0 ≤ (Real.exp x) ^ 2 := sq_nonneg _

-- ===================================================================
-- Symmetric sqrt and abs
-- ===================================================================

/-- sqrt(|x|²) = |x|. -/
theorem sqrt_abs_sq_eq_abs (x : ℝ) : Real.sqrt (|x| ^ 2) = |x| :=
  Real.sqrt_sq (abs_nonneg x)

/-- For x > 0: sqrt(x^2) = x. -/
theorem sqrt_sq_pos (x : ℝ) (hx : 0 < x) : Real.sqrt (x ^ 2) = x :=
  Real.sqrt_sq (le_of_lt hx)

-- ===================================================================
-- Non-negativity / monotone corollaries
-- ===================================================================

/-- 0 ≤ sqrt x for all real x. -/
theorem sqrt_nonneg_named (x : ℝ) : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x

/-- 0 ≤ x ^ (a : ℝ) for x ≥ 0 (rpow). -/
theorem rpow_nonneg_named (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : 0 ≤ x ^ a :=
  Real.rpow_nonneg hx a



