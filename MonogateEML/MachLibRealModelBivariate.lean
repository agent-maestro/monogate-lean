import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Floor.Ring

/-!
# `MachLib.Real` soundness witnesses: bivariate derivatives, the implicit-function derivative, `floor`

machlib's `BivariateDeriv.lean` axiomatises an opaque `HasDerivAt2 f fx fy x y` with its rules and the
implicit-function derivative; `Forge.lean` axiomatises `floor` with three laws. None had a Mathlib witness. This
file reads them as

* `HasDerivAt2 f fx fy x y` ↦ `HasDerivAt2R f fx fy x y`: `(a, b) ↦ f a b` is Fréchet differentiable at `(x, y)`
  with derivative `fx • fst + fy • snd`, so `fx`, `fy` are its partials;
* `floor` ↦ `x ↦ (⌊x⌋ : ℝ)`, Mathlib's `Int.floor` cast back to `ℝ`,

and proves each axiom at that reading. `AxiomWitnessBridge` checks every one against the axiom's interpreted type.
Two statements first witnessed here are no longer axioms in machlib: the rule `HasDerivAt2_sub` and the global
`hasDerivAt_implicit` became theorems on 2026-10-27. The global form's witness is deleted; `hasDerivAt2_sub` is kept
only because `old_implicit_statement_false` uses it.

**The implicit-function axiom was false until machlib restated it on 2026-10-27**, and this file keeps the proof:
`old_implicit_statement_false` refutes the old statement in Mathlib's `ℝ`, independently of the refutation machlib
proves from its own mean value theorem (`BivariateImplicitControls`). The old statement let the curve `yc` jump
between solution branches. The restated one takes `yc` continuous at `x`, and `implicit_deriv_core` proves the
derivative from exactly that: Fréchet differentiability at the one point, `fᵧ ≠ 0`, and the curve identity near
`x`. `sorryAx`-free.
-/

namespace MonogateEML.RealModel

open Filter Topology Asymptotics

/-- MachLib's `HasDerivAt2 f fx fy x y`, read in Mathlib: `(a, b) ↦ f a b` has Fréchet derivative
`fx • fst + fy • snd` at `(x, y)`. -/
def HasDerivAt2R (f : ℝ → ℝ → ℝ) (fx fy x y : ℝ) : Prop :=
  HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
    (fx • ContinuousLinearMap.fst ℝ ℝ ℝ + fy • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y)

/-- A linear map on `ℝ × ℝ` is fixed by its values at the two unit vectors. -/
theorem clm2_apply (L : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ) : L (u, v) = u * L (1, 0) + v * L (0, 1) := by
  have h : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem clm2_ext {L M : ℝ × ℝ →L[ℝ] ℝ} (h1 : L (1, 0) = M (1, 0)) (h2 : L (0, 1) = M (0, 1)) :
    L = M :=
  ContinuousLinearMap.ext fun ⟨u, v⟩ => by rw [clm2_apply L, clm2_apply M, h1, h2]

@[simp] theorem partials_apply (fx fy u v : ℝ) :
    (fx • ContinuousLinearMap.fst ℝ ℝ ℝ + fy • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) = fx * u + fy * v := by
  simp [smul_eq_mul]

/-! ## The `HasDerivAt2` rules -/

theorem hasDerivAt2_projX (x y : ℝ) : HasDerivAt2R (fun a _ => a) 1 0 x y := by
  have h : (1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ
      = ContinuousLinearMap.fst ℝ ℝ ℝ := by simp
  unfold HasDerivAt2R
  rw [h]
  exact hasFDerivAt_fst

theorem hasDerivAt2_projY (x y : ℝ) : HasDerivAt2R (fun _ b => b) 0 1 x y := by
  have h : (0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ
      = ContinuousLinearMap.snd ℝ ℝ ℝ := by simp
  unfold HasDerivAt2R
  rw [h]
  exact hasFDerivAt_snd

theorem hasDerivAt2_const (c x y : ℝ) : HasDerivAt2R (fun _ _ => c) 0 0 x y := by
  have h : (0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ = 0 := by simp
  unfold HasDerivAt2R
  rw [h]
  exact hasFDerivAt_const c (x, y)

theorem hasDerivAt2_add (f g : ℝ → ℝ → ℝ) (fx fy gx gy x y : ℝ) :
    HasDerivAt2R f fx fy x y → HasDerivAt2R g gx gy x y →
    HasDerivAt2R (fun a b => f a b + g a b) (fx + gx) (fy + gy) x y := by
  intro hf hg
  unfold HasDerivAt2R at *
  exact (hf.add hg).congr_fderiv (by refine clm2_ext ?_ ?_ <;> simp)

theorem hasDerivAt2_sub (f g : ℝ → ℝ → ℝ) (fx fy gx gy x y : ℝ) :
    HasDerivAt2R f fx fy x y → HasDerivAt2R g gx gy x y →
    HasDerivAt2R (fun a b => f a b - g a b) (fx - gx) (fy - gy) x y := by
  intro hf hg
  unfold HasDerivAt2R at *
  exact (hf.sub hg).congr_fderiv (by refine clm2_ext ?_ ?_ <;> simp)

theorem hasDerivAt2_mul (f g : ℝ → ℝ → ℝ) (fx fy gx gy x y : ℝ) :
    HasDerivAt2R f fx fy x y → HasDerivAt2R g gx gy x y →
    HasDerivAt2R (fun a b => f a b * g a b) (fx * g x y + f x y * gx) (fy * g x y + f x y * gy) x y := by
  intro hf hg
  unfold HasDerivAt2R at *
  exact (hf.mul hg).congr_fderiv (by refine clm2_ext ?_ ?_ <;> simp <;> ring)

theorem hasDerivAt2_scomp (φ : ℝ → ℝ) (φ' : ℝ) (u : ℝ → ℝ → ℝ) (ux uy x y : ℝ) :
    HasDerivAt φ φ' (u x y) → HasDerivAt2R u ux uy x y →
    HasDerivAt2R (fun a b => φ (u a b)) (φ' * ux) (φ' * uy) x y := by
  intro hφ hu
  unfold HasDerivAt2R at *
  exact (hφ.comp_hasFDerivAt (x, y) hu).congr_fderiv (by refine clm2_ext ?_ ?_ <;> simp)

theorem hasDerivAt2_comp (f : ℝ → ℝ → ℝ) (fx fy : ℝ) (γ₁ γ₂ : ℝ → ℝ) (d₁ d₂ t : ℝ) :
    HasDerivAt2R f fx fy (γ₁ t) (γ₂ t) → HasDerivAt γ₁ d₁ t → HasDerivAt γ₂ d₂ t →
    HasDerivAt (fun s => f (γ₁ s) (γ₂ s)) (fx * d₁ + fy * d₂) t := by
  intro hf h1 h2
  unfold HasDerivAt2R at hf
  have h := hf.comp_hasDerivAt (f := fun s => (γ₁ s, γ₂ s)) t (h1.prodMk h2)
  simpa [Function.comp_def] using h

/-! ## The implicit-function derivative -/

/-- **The implicit-function derivative from a continuous solution curve.** If `F` is Fréchet differentiable at
`(x, yc x)` with `L (0, 1) ≠ 0`, `yc` is continuous at `x`, and `F (s, yc s) = 0` for `s` near `x`, then
`yc' x = −L (1, 0) / L (0, 1)`. With `u = s − x` and `v = yc s − yc x`, differentiability along the curve (which
tends to `(x, yc x)` because `yc` is continuous) gives `a u + b v = o(‖(u, v)‖)`; so `v = O(u)`, then
`a u + b v = o(u)`, which is the derivative. Without continuity the curve need not approach `(x, yc x)` and the
argument has nothing to start from: `old_implicit_statement_false` below. -/
theorem implicit_deriv_core {F : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {yc : ℝ → ℝ} {x : ℝ}
    (hF : HasFDerivAt F L (x, yc x)) (hb : L (0, 1) ≠ 0) (hc : ContinuousAt yc x)
    (hid : ∀ᶠ s in 𝓝 x, F (s, yc s) = 0) :
    HasDerivAt yc (-(L (1, 0)) / L (0, 1)) x := by
  set a := L (1, 0) with ha
  set b := L (0, 1) with hb'
  have hγ : Tendsto (fun s => (s, yc s)) (𝓝 x) (𝓝 (x, yc x)) :=
    (continuousAt_id.prodMk hc).tendsto
  have hx0 : F (x, yc x) = 0 := hid.self_of_nhds
  have hlo := hF.isLittleO.comp_tendsto hγ
  -- along the curve: `a u + b v = o(‖(u, v)‖)`
  have hlin : (fun s => a * (s - x) + b * (yc s - yc x)) =o[𝓝 x]
      (fun s => ((s - x, yc s - yc x) : ℝ × ℝ)) := by
    have e : ((fun p => F p - F (x, yc x) - L (p - (x, yc x))) ∘ (fun s => (s, yc s))) =ᶠ[𝓝 x]
        (fun s => -(a * (s - x) + b * (yc s - yc x))) := by
      filter_upwards [hid] with s hs
      simp only [Function.comp_apply, hs, hx0, Prod.mk_sub_mk]
      rw [clm2_apply L]
      ring
    have e2 : ((fun p => p - (x, yc x)) ∘ (fun s => (s, yc s))) =ᶠ[𝓝 x]
        (fun s => ((s - x, yc s - yc x) : ℝ × ℝ)) :=
      Eventually.of_forall fun s => by simp [Prod.mk_sub_mk]
    exact isLittleO_neg_left.mp (hlo.congr' e e2)
  set k := a / b with hk
  have hw : (fun s => b⁻¹ * (a * (s - x) + b * (yc s - yc x))) =o[𝓝 x]
      (fun s => ((s - x, yc s - yc x) : ℝ × ℝ)) := hlin.const_mul_left b⁻¹
  -- `‖(u, v)‖ ≤ |u| + |v|`
  have hPle : (fun s => ((s - x, yc s - yc x) : ℝ × ℝ)) =O[𝓝 x]
      (fun s => |s - x| + |yc s - yc x|) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun s => ?_)
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |s - x| + |yc s - yc x|)]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  -- so `v = O(u)`: `|v| ≤ |w| + |k| |u|` with `|w| ≤ (|u| + |v|) / 2` eventually
  have hv : ∀ᶠ s in 𝓝 x, |yc s - yc x| ≤ (1 + 2 * |k|) * |s - x| := by
    filter_upwards [(hw.trans_isBigO hPle).def (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |s - x| + |yc s - yc x|)] at hs
    have hsplit : yc s - yc x = b⁻¹ * (a * (s - x) + b * (yc s - yc x)) - k * (s - x) := by
      rw [hk]
      field_simp
      ring
    have h1 : |yc s - yc x| ≤ |b⁻¹ * (a * (s - x) + b * (yc s - yc x))| + |k| * |s - x| := by
      calc |yc s - yc x| = |b⁻¹ * (a * (s - x) + b * (yc s - yc x)) - k * (s - x)| := by
            rw [← hsplit]
        _ ≤ |b⁻¹ * (a * (s - x) + b * (yc s - yc x))| + |k * (s - x)| := abs_sub _ _
        _ = |b⁻¹ * (a * (s - x) + b * (yc s - yc x))| + |k| * |s - x| := by rw [abs_mul k]
    nlinarith [abs_nonneg (s - x), abs_nonneg k]
  have hPO : (fun s => ((s - x, yc s - yc x) : ℝ × ℝ)) =O[𝓝 x] (fun s => s - x) := by
    refine hPle.trans (IsBigO.of_bound (2 + 2 * |k|) ?_)
    filter_upwards [hv] with s hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |s - x| + |yc s - yc x|)]
    nlinarith [abs_nonneg (s - x), abs_nonneg k]
  rw [hasDerivAt_iff_isLittleO]
  refine (hw.trans_isBigO hPO).congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [smul_eq_mul]
  field_simp
  ring

/-- MachLib's `ContinuousAt` (its own ε-δ definition, as `AxiomWitnessBridge` interprets it) is Mathlib's. -/
theorem continuousAt_of_eps_delta {g : ℝ → ℝ} {x : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |g y - g x| < ε) :
    ContinuousAt g x :=
  Metric.continuousAt_iff.mpr fun ε hε => by
    obtain ⟨δ, hδ, H⟩ := h ε hε
    exact ⟨δ, hδ, fun {y} hy => by
      simpa [Real.dist_eq] using H y (by simpa [Real.dist_eq] using hy)⟩

/-- **The witness of the restated `hasDerivAt_implicit_local`.** -/
theorem hasDerivAt_implicit_local_witness (f : ℝ → ℝ → ℝ) (fx fy : ℝ) (yc : ℝ → ℝ) (x p q : ℝ)
    (hp : p < x) (hq : x < q) :
    HasDerivAt2R f fx fy x (yc x) → fy ≠ 0 →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |yc y - yc x| < ε) →
    (∀ s : ℝ, p < s → s < q → f s (yc s) = 0) → HasDerivAt yc (-fx / fy) x := by
  intro h2 hfy hc hid
  have hev : ∀ᶠ s in 𝓝 x, (fun p : ℝ × ℝ => f p.1 p.2) (s, yc s) = 0 := by
    filter_upwards [Ioo_mem_nhds hp hq] with s hs
    exact hid s hs.1 hs.2
  have h := implicit_deriv_core (F := fun p : ℝ × ℝ => f p.1 p.2) h2 (by simpa using hfy)
    (continuousAt_of_eps_delta hc) hev
  simpa using h

/-- **The statement `hasDerivAt_implicit` had until 2026-10-27 is false in Mathlib's `ℝ`.** With
`f a b = b (b − 1)` and `yc` the step from `0` to `1` at `0`, the curve identity holds everywhere and
`fᵧ = 2 yc 0 − 1 = 1 ≠ 0` at `(0, yc 0)`, so the old statement makes `yc` differentiable at `0`, hence continuous
there, which a jump is not. -/
theorem old_implicit_statement_false :
    ¬ (∀ (f : ℝ → ℝ → ℝ) (fx fy : ℝ) (yc : ℝ → ℝ) (x : ℝ),
        HasDerivAt2R f fx fy x (yc x) → fy ≠ 0 → (∀ s : ℝ, f s (yc s) = 0) →
        HasDerivAt yc (-fx / fy) x) := by
  intro hold
  classical
  let yc : ℝ → ℝ := fun s => if s < 0 then 0 else 1
  have h2 : HasDerivAt2R (fun _ b => b * (b - 1)) (0 * (yc 0 - 1) + yc 0 * (0 - 0))
      (1 * (yc 0 - 1) + yc 0 * (1 - 0)) 0 (yc 0) :=
    hasDerivAt2_mul (fun _ b => b) (fun _ b => b - 1) 0 1 (0 - 0) (1 - 0) 0 (yc 0)
      (hasDerivAt2_projY 0 (yc 0))
      (hasDerivAt2_sub (fun _ b => b) (fun _ _ => 1) 0 1 0 0 0 (yc 0)
        (hasDerivAt2_projY 0 (yc 0)) (hasDerivAt2_const 1 0 (yc 0)))
  have hy0 : yc 0 = 1 := by simp [yc]
  have hfy : 1 * (yc 0 - 1) + yc 0 * (1 - 0) ≠ 0 := by rw [hy0]; norm_num
  have hroot : ∀ s : ℝ, (fun _ b : ℝ => b * (b - 1)) s (yc s) = 0 := by
    intro s
    by_cases h : s < 0 <;> simp [yc, h]
  have hd := hold _ _ _ yc 0 h2 hfy hroot
  have hcont := hd.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, H⟩ := hcont (1 / 2) (by norm_num)
  have hneg : -(δ / 2) < 0 := by linarith
  have := H (x := -(δ / 2)) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  simp [yc, hneg, Real.dist_eq] at this
  norm_num at this

/-! ## `floor` -/

theorem floor_le_witness (x : ℝ) : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x

theorem lt_floor_add_one_witness (x : ℝ) : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x

theorem floor_zero_witness : ((⌊(0 : ℝ)⌋ : ℤ) : ℝ) = 0 := by simp

end MonogateEML.RealModel
