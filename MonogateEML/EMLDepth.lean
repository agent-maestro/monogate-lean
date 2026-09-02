-- MonogateEML/EMLDepth.lean
-- Inductive type for Complex EML trees and depth classification.
--
-- ceml(z₁, z₂) = exp(z₁) − Log(z₂)   (principal branch)
-- Sessions 11-50 research — Lean 4 formalization skeleton.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.ExponentialBounds

open Real Complex

-- ============================================================
-- 1. EML Tree Inductive Type
-- ============================================================

/-- A Complex EML tree. Represents finite compositions of ceml. -/
inductive EMLTree : Type where
  | const  : ℂ → EMLTree           -- constant node
  | var    : EMLTree                 -- variable x
  | ceml   : EMLTree → EMLTree → EMLTree  -- ceml(t1, t2) = exp(t1) - Log(t2)

/-- Evaluate an EML tree at a complex input. -/
noncomputable def EMLTree.eval : EMLTree → ℂ → ℂ
  | .const c, _ => c
  | .var,      x => x
  | .ceml t1 t2, x => Complex.exp (t1.eval x) - Complex.log (t2.eval x)

/-- Depth of an EML tree (number of ceml nodes along longest path). -/
def EMLTree.depth : EMLTree → ℕ
  | .const _ => 0
  | .var     => 0
  | .ceml t1 t2 => 1 + max t1.depth t2.depth

-- ============================================================
-- 2. EML-k: Functions of depth ≤ k
-- ============================================================

/-- EML-k is the set of functions representable by a tree of depth ≤ k. -/
def EML_k (k : ℕ) : Set (ℂ → ℂ) :=
  { f | ∃ t : EMLTree, t.depth ≤ k ∧ ∀ x, f x = t.eval x }

-- ============================================================
-- 3. Basic Identities (CEML-T1 through T5)
-- ============================================================

/-- CEML-T1: Euler Gateway. ceml(ix, 1) = exp(ix). -/
theorem euler_gateway (x : ℝ) :
    EMLTree.eval (.ceml .var (.const 1)) (x * Complex.I) =
    Complex.exp (x * Complex.I) := by
  simp [EMLTree.eval, Complex.log_one]

/-- The depth-1 Euler gateway tree. -/
def eulerTree : EMLTree := .ceml .var (.const 1)

/-- CEML-T5: Euler Identity (principal branch).
    ceml(iπ, 1) = exp(iπ) = -1, so ceml(iπ, 1) + 1 = 0. -/
theorem euler_identity :
    EMLTree.eval (.ceml (.const (Complex.I * Real.pi)) (.const 1)) 0 + 1 = 0 := by
  simp only [EMLTree.eval, Complex.log_one, sub_zero]
  rw [show Complex.I * ↑Real.pi = ↑Real.pi * Complex.I from mul_comm _ _,
      Complex.exp_pi_mul_I]
  norm_num

-- ============================================================
-- 4. Depth Witnesses (CEML-T40 through T43)
-- ============================================================

/-- Witness for EML-0 ⊊ EML-1: exp(x) is EML-1 (depth 1), not constant. -/
def expTree : EMLTree := .ceml .var (.const 1)

theorem expTree_depth : expTree.depth = 1 := by
  simp [expTree, EMLTree.depth]

theorem expTree_eval (x : ℂ) :
    expTree.eval x = Complex.exp x := by
  simp [expTree, EMLTree.eval, Complex.log_one]

/-- expTree is not constant (EML-0 ⊊ EML-1). -/
theorem exp_not_constant : ¬ (∃ c : ℂ, ∀ x, expTree.eval x = c) := by
  intro ⟨c, hc⟩
  have h0 : Complex.exp 0 = c := by simpa [expTree_eval] using hc 0
  have h1 : Complex.exp 1 = c := by simpa [expTree_eval] using hc 1
  have heq : Complex.exp (1 : ℂ) = 1 := by rw [h1, ← h0]; simp
  have hre : Real.exp 1 = 1 := by
    have := congr_arg Complex.re heq
    simp only [Complex.one_re] at this
    rwa [show (Complex.exp (1:ℂ)).re = Real.exp 1 from by
      have : (1:ℂ) = ((1:ℝ):ℂ) := by norm_cast
      rw [this, Complex.exp_ofReal_re]] at this
  linarith [Real.exp_one_gt_d9]

-- ============================================================
-- 5. Real Restriction
-- ============================================================

/-- Real restriction: a real EML tree takes real inputs to real outputs
    when all log arguments are positive. -/
noncomputable def EMLTree.evalReal (t : EMLTree) (x : ℝ) : ℝ :=
  (t.eval (x : ℂ)).re

/-- Constant EML trees have constant real evaluation. -/
lemma const_tree_evalReal (c : ℂ) (x : ℝ) :
    (EMLTree.const c).evalReal x = c.re := by
  simp [EMLTree.evalReal, EMLTree.eval]

/-- The variable EML tree evaluates to x on the real line. -/
lemma var_tree_evalReal (x : ℝ) :
    EMLTree.var.evalReal x = x := by
  simp [EMLTree.evalReal, EMLTree.eval]

/-- sin is not monotone on [0, 2π]. -/
lemma sin_not_monotone_full :
    ¬ Monotone (fun x : ℝ => Real.sin x) := by
  intro h
  have h1 : Real.sin (Real.pi / 2) ≤ Real.sin Real.pi := by
    apply h; linarith [Real.pi_pos]
  rw [Real.sin_pi_div_two, Real.sin_pi] at h1
  linarith

-- ============================================================
-- 6. Sorry Census
-- ============================================================

/-
SORRY CENSUS (current — this file):
  0 sorries in EMLDepth.lean.

  depth1_finite_zeros_real and sin_not_in_real_EML_k have been moved to
  InfiniteZerosBarrier.lean to avoid circular imports.
  depth1_finite_zeros_real is now proved (0 sorry) in InfiniteZerosBarrier.lean.
  sin_not_in_real_EML_k remains sorry'd (o-minimal theory needed) there.
-/

-- ============================================================
-- 7. Verified Computations (no sorry)
-- ============================================================

/-- Tree count at depth ≤ 1: 3 trees (const, var, ceml(var, const 1)). -/
example : eulerTree.depth = 1 := expTree_depth

/-- The Euler gateway tree evaluates correctly at x = 0. -/
example : eulerTree.eval 0 = 1 := by
  simp [eulerTree, EMLTree.eval, Complex.log_one]

-- ============================================================
-- 8. Depth computation lemmas
-- ============================================================

/-- The depth of a constant node is 0. -/
theorem depth_of_const (c : ℂ) : (EMLTree.const c).depth = 0 := rfl

/-- The depth of the variable node is 0. -/
theorem depth_of_var : EMLTree.var.depth = 0 := rfl

/-- The depth of a `ceml` node is `1 + max`. -/
theorem depth_of_ceml (t₁ t₂ : EMLTree) :
    (EMLTree.ceml t₁ t₂).depth = 1 + max t₁.depth t₂.depth := rfl

/-- Depth is a natural number; `ceml` contributes at least 1. -/
theorem depth_ceml_pos (t₁ t₂ : EMLTree) :
    0 < (EMLTree.ceml t₁ t₂).depth := by
  simp [EMLTree.depth]

/-- Depth is monotone under the first argument of `ceml`. -/
theorem depth_mono_left (t₁ t₂ : EMLTree) :
    t₁.depth ≤ (EMLTree.ceml t₁ t₂).depth := by
  simp [EMLTree.depth]; linarith [le_max_left t₁.depth t₂.depth]

/-- Depth is monotone under the second argument of `ceml`. -/
theorem depth_mono_right (t₁ t₂ : EMLTree) :
    t₂.depth ≤ (EMLTree.ceml t₁ t₂).depth := by
  simp [EMLTree.depth]; linarith [le_max_right t₁.depth t₂.depth]

-- ============================================================
-- 9. EML-k membership witnesses (depth ≤ k)
-- ============================================================

/-- Any constant function c is in EML-k for every k (use a const tree of depth 0). -/
theorem const_in_EML_k (c : ℂ) (k : ℕ) : (fun _ : ℂ => c) ∈ EML_k k := by
  refine ⟨.const c, ?_, ?_⟩
  · simp [EMLTree.depth]
  · intro x; simp [EMLTree.eval]

/-- The identity function is in EML-k for every k (use the var tree of depth 0). -/
theorem id_in_EML_k (k : ℕ) : (fun x : ℂ => x) ∈ EML_k k := by
  refine ⟨.var, ?_, ?_⟩
  · simp [EMLTree.depth]
  · intro x; simp [EMLTree.eval]

/-- Complex.exp is in EML-1 (via the eulerTree depth-1 witness). -/
theorem exp_in_EML_one : (fun x : ℂ => Complex.exp x) ∈ EML_k 1 := by
  refine ⟨eulerTree, ?_, ?_⟩
  · simp [eulerTree, EMLTree.depth]
  · intro x; simp [eulerTree, EMLTree.eval, Complex.log_one]

-- ============================================================
-- 10. Tree depth monotone in k (EML-k ⊆ EML-(k+1))
-- ============================================================

/-- Any tree that is in EML-k is also in EML-(k+1) (trivial). -/
theorem EML_k_subset_EML_succ (k : ℕ) : EML_k k ⊆ EML_k (k + 1) := by
  rintro f ⟨t, hdepth, heval⟩
  exact ⟨t, by linarith, heval⟩

/-- Any tree in EML-k is in EML-m for m ≥ k. -/
theorem EML_k_subset_of_le {k m : ℕ} (h : k ≤ m) : EML_k k ⊆ EML_k m := by
  rintro f ⟨t, hdepth, heval⟩
  exact ⟨t, le_trans hdepth h, heval⟩

-- ============================================================
-- 11. Concrete depth evaluation
-- ============================================================

/-- `ceml (var) (const 1)` has depth 1 (the depth of eulerTree). -/
theorem eulerTree_depth_one : eulerTree.depth = 1 := by
  simp [eulerTree, EMLTree.depth]

/-- The `ceml` of two depth-0 trees has depth exactly 1. -/
theorem depth_ceml_of_atoms (t₁ t₂ : EMLTree)
    (h₁ : t₁.depth = 0) (h₂ : t₂.depth = 0) :
    (EMLTree.ceml t₁ t₂).depth = 1 := by
  simp [EMLTree.depth, h₁, h₂]

-- ============================================================
-- 12. Stability of evalReal for atoms
-- ============================================================

/-- The constant tree evaluates to the real part of its constant. -/
theorem evalReal_const_eq_re (c : ℂ) (x : ℝ) :
    (EMLTree.const c).evalReal x = c.re := const_tree_evalReal c x

/-- The var tree evaluates to the identity on reals. -/
theorem evalReal_var_eq_id (x : ℝ) :
    EMLTree.var.evalReal x = x := var_tree_evalReal x
