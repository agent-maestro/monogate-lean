-- MonogateEML/SinNotInEMLDepthBounds.lean
import MonogateEML.EMLDepth
import MonogateEML.InfiniteZerosBarrier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Pi.Bounds

/-!
# `sin ∉ EML_k` for fixed small `k` — direct case analysis

This file shows that `sin` is not the real evaluation of any EML tree of
depth ≤ 1 (and, as ongoing work, depth ≤ 2) by explicit two-point case
analysis, **without** the Khovanskii / o-minimal infrastructure that the
generic `InfiniteZerosBarrier.sin_not_in_eml` theorem is gated on.

The argument:

- Suppose `t.evalReal = Real.sin` globally on `ℝ`.
- Then in particular `t.evalReal 0 = Real.sin 0 = 0` and
  `t.evalReal (π/2) = Real.sin (π/2) = 1`.
- For each shape of `t` at depth ≤ k, the two-point evaluation produces
  a contradictory constraint on the free constants of the shape.

This is finite-cases-per-fixed-k. It cannot prove the uniform-in-k
statement (that requires Khovanskii). But it can ship a sequence of
positive booked theorems
`sin_not_in_eml_depth_le_1`, `sin_not_in_eml_depth_le_2`, ...
without waiting for Mathlib infrastructure.

Strategic context: see
`monogate-research/exploration/alpha_sin_not_in_eml_depth_2_feasibility_scoping_2026_06_10/FINDINGS.md`.
-/

open Real Complex

namespace MonogateEML

-- ===================================================================
-- Numeric helper lemmas
-- ===================================================================

/-- `π/2 > 1`, derived from `Real.pi_gt_three`. -/
private lemma pi_div_two_gt_one : Real.pi / 2 > 1 := by
  have : Real.pi > 3 := Real.pi_gt_three
  linarith

/-- `sin 1 > 0`, derived from `Real.sin_pos_of_pos_of_lt_pi`. -/
private lemma sin_one_pos : Real.sin 1 > 0 := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · norm_num
  · linarith [Real.pi_gt_three]

/-- `Real.exp (π/2) > 2`. -/
private lemma exp_pi_div_two_gt_two : Real.exp (Real.pi / 2) > 2 := by
  have h1 : Real.exp 1 > 2 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : Real.exp 1 < Real.exp (Real.pi / 2) :=
    Real.exp_lt_exp.mpr pi_div_two_gt_one
  linarith

-- ===================================================================
-- Depth-0 mini-theorem (warmup)
-- ===================================================================

/-- `sin` is not depth-0. (Depth 0 = const or var.) -/
theorem sin_not_in_eml_depth_le_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : ℝ, t.evalReal x = Real.sin x) := by
  intro hsin
  cases t with
  | const c =>
    have h0 := hsin 0
    have h1 := hsin (Real.pi / 2)
    simp only [EMLTree.evalReal, EMLTree.eval, Real.sin_zero, Real.sin_pi_div_two] at h0 h1
    linarith
  | var =>
    have h := hsin (Real.pi / 2)
    simp only [EMLTree.evalReal, EMLTree.eval, Real.sin_pi_div_two] at h
    -- h : (((Real.pi / 2 : ℝ) : ℂ).re) = 1
    have : ((Real.pi / 2 : ℝ) : ℂ).re = Real.pi / 2 := by simp
    rw [this] at h
    linarith [pi_div_two_gt_one]
  | ceml t1 t2 =>
    -- A `ceml` node has depth ≥ 1, contradicting ht : depth ≤ 0.
    simp only [EMLTree.depth] at ht
    omega

-- ===================================================================
-- Depth-1 main theorem
-- ===================================================================

/-- `sin` is not depth-≤-1.

Proof: two-point evaluation at `x = 0` and (for some cases) `x = 1` or
`x = π/2`. The depth-1 grammar has exactly six shapes; each forces a
contradiction on the assumed equation `t.evalReal = sin`. -/
theorem sin_not_in_eml_depth_le_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : ℝ, t.evalReal x = Real.sin x) := by
  intro hsin
  -- Shape: either depth 0 (handled above) or `ceml(t1, t2)` with both t1, t2
  -- of depth 0.
  match t, ht with
  | .const c, _ =>
    exact sin_not_in_eml_depth_le_0 (.const c) (by simp [EMLTree.depth]) hsin
  | .var, _ =>
    exact sin_not_in_eml_depth_le_0 .var (by simp [EMLTree.depth]) hsin
  | .ceml t1 t2, ht =>
    have ht_max : max t1.depth t2.depth ≤ 0 := by
      simp only [EMLTree.depth] at ht; omega
    have ht1 : t1.depth = 0 := by have := le_max_left t1.depth t2.depth; omega
    have ht2 : t2.depth = 0 := by have := le_max_right t1.depth t2.depth; omega
    -- Case split on the (depth-0) shapes of t1 and t2.
    match t1, ht1, t2, ht2 with
    | .ceml _ _, ht1, _, _ =>
      simp only [EMLTree.depth] at ht1; omega
    | _, _, .ceml _ _, ht2 =>
      simp only [EMLTree.depth] at ht2; omega
    | .const c1, _, .const c2, _ =>
      -- ceml(const c1, const c2): evalReal x = (exp c1 - log c2).re (constant).
      have h0 := hsin 0
      have h1 := hsin (Real.pi / 2)
      simp only [EMLTree.evalReal, EMLTree.eval,
                 Real.sin_zero, Real.sin_pi_div_two] at h0 h1
      linarith
    | .const c1, _, .var, _ =>
      -- ceml(const c1, var): evalReal 0 = (exp c1 - log 0).re = (exp c1).re.
      --                     evalReal 1 = (exp c1 - log 1).re = (exp c1).re.
      -- So (exp c1).re = sin 0 = 0 and (exp c1).re = sin 1 > 0. Contradiction.
      have h0 := hsin 0
      have h1 := hsin 1
      simp only [EMLTree.evalReal, EMLTree.eval,
                 Complex.ofReal_zero, Complex.ofReal_one,
                 Complex.log_zero, Complex.log_one,
                 sub_zero, Real.sin_zero] at h0 h1
      -- h0 : (Complex.exp c1).re = 0
      -- h1 : (Complex.exp c1).re = Real.sin 1
      have : Real.sin 1 = 0 := h1.symm.trans h0
      linarith [sin_one_pos]
    | .var, _, .const c2, _ =>
      -- ceml(var, const c2): evalReal x = (exp ↑x - log c2).re.
      -- At x = 0: 1 - (log c2).re = sin 0 = 0, so (log c2).re = 1.
      -- At x = π/2: exp(π/2) - (log c2).re = sin(π/2) = 1, so exp(π/2) = 2.
      -- But exp(π/2) > 2. Contradiction.
      have h0 := hsin 0
      have h1 := hsin (Real.pi / 2)
      simp only [EMLTree.evalReal, EMLTree.eval,
                 Complex.ofReal_zero, Complex.exp_zero,
                 Real.sin_zero, Real.sin_pi_div_two,
                 Complex.sub_re, Complex.one_re] at h0 h1
      -- h0: 1 - (Complex.log c2).re = 0
      -- h1: ((Complex.exp ↑(π/2)).re - (Complex.log c2).re = 1
      -- exp of a real → real
      have hexp_re : (Complex.exp ((Real.pi / 2 : ℝ) : ℂ)).re = Real.exp (Real.pi / 2) := by
        rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) from rfl]
        exact Complex.exp_ofReal_re _
      rw [hexp_re] at h1
      have hlogc2 : (Complex.log c2).re = 1 := by linarith
      rw [hlogc2] at h1
      -- h1: Real.exp (π/2) - 1 = 1, i.e., Real.exp(π/2) = 2.
      linarith [exp_pi_div_two_gt_two]
    | .var, _, .var, _ =>
      -- ceml(var, var): evalReal 0 = (exp 0 - log 0).re = (1 - 0).re = 1.
      -- sin 0 = 0. So 1 = 0. Contradiction.
      have h := hsin 0
      simp only [EMLTree.evalReal, EMLTree.eval,
                 Complex.ofReal_zero, Complex.exp_zero,
                 Complex.log_zero, sub_zero, Complex.one_re,
                 Real.sin_zero] at h
      -- h : 1 = 0
      linarith

-- ===================================================================
-- Depth-2 main theorem — NOT YET PROVEN
-- ===================================================================
--
-- `sin_not_in_eml_depth_le_2` is intentionally NOT stated here as a
-- `theorem ... := sorry`, because doing so would increment the public
-- Lean sorry count surfaced by PUB-R0 / PUB-R1 without adding a proven
-- statement to the library. The discipline is to land positive booked
-- theorems, not to publish placeholders.
--
-- The depth-2 case-enumeration strategy is recorded in
-- `monogate-research/exploration/alpha_sin_not_in_eml_depth_2_feasibility_scoping_2026_06_10/FINDINGS.md`.
-- A future session may add the theorem here once the proof closes; until
-- then, the Lean repo carries one fewer sorry than it would otherwise.

end MonogateEML
