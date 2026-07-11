import MachLib.ExpPolyEffectiveBound
import MachLib.ChainExpPoly

/-!
# Gate 2 — the geometry reduction, machine-checked on the simplest slice

The tameness backbone's **Gate 2** asks whether the string-landscape's own functions land in
monogate's exp-Pfaffian zero-count class, so that the now-proven **effective** bound
`expPoly_effective_bound` gives an actual *number* where o-minimality gives only "finite."

This file carries out the simplest reachable case and machine-checks it: the **one-modulus,
one-instanton** flux F-term on a **real slice**, reduced to an `ExpPoly`, with the crux certifying an
explicit bound on its zeros.

## The reduction (see `monogate-research/GATE2_GEOMETRY_REDUCTION.md` for the geometry)

Near a large-complex-structure limit the period vector is `Π(t) = e^{tN}(a₀ + a₁ q + …)` with `N` the
nilpotent log-monodromy (`N⁴=0`, so `e^{tN}` is a cubic polynomial in `t`) and `q = e^{2πi t}` the
worldsheet-instanton factor (Schmid's nilpotent orbit theorem). The flux superpotential
`W(t) = (f−τh)ᵀ Σ Π(t)` is therefore `W = P₀(t) + P₁(t) q + O(q²)` with `P₀, P₁` cubic in `t`. Its
holomorphic critical-point equation, keeping the first instanton, is

    ∂_t W(t) = Q₀(t) + Q₁(t)·q ,   Q₀ = P₀′ (deg ≤ 2),   Q₁ = P₁′ + 2πi P₁ (deg ≤ 3).

On the real slice `t = i y` (`y>0`) the instanton factor `q = e^{-2πy}` is a **real** decaying
exponential, so after an affine reparametrisation `x` of the slice (with `q ↦ e^{x}`) this is a genuine
real `ExpPoly` `⟨[Q₀, Q₁]⟩` — `eval x = Q₀(x) + Q₁(x)·e^{x}`. `expPoly_effective_bound` then bounds its
real zeros by `length + Σdeg = 2 + deg Q₀ + deg Q₁ ≤ 2 + 2 + 3 = 7`.

The coefficients below are **arbitrary reals** (any flux quanta / geometry data): the bound `≤ 7` is
uniform in them — the effective count depends only on the nilpotent order and the number of instanton
modes kept, exactly as an *effective* Khovanskii bound should.

## Honest scope

The certified `≤ 7` bounds **real critical points of the truncated holomorphic `W` on the slice**, given
the genericity hypothesis `hne` (the F-term is not identically zero on the slice — true for generic
flux). It is *not yet* a count of the flux landscape: real→complex vacua (Gate 2a), critical-points→
F-flatness (2b), finite→full instanton series which needs `ℝ_{an}` (2c), and one→many moduli (2d) each
remain — see the scoping doc. What this file establishes is that Gate 2's simplest slice **closes**, on
the landscape's own function class, with a machine-checked explicit number.

Footprint is inherited from `expPoly_effective_bound`: `rolle_ct`-only + Lean/`MachLib.Real` core.
-/

open MachLib.SingleExpKhovanskii
open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

namespace MonogateEML.FluxLandscapeGate2

/-- `Q₀ = c₂·x² + c₁·x + c₀` — the nilpotent-orbit part `P₀′` of the F-term (degree ≤ 2). -/
noncomputable def Q0 (c0 c1 c2 : MachLib.Real) : Poly :=
  Poly.add (Poly.mul (Poly.const c2) (Poly.mul Poly.var Poly.var))
           (Poly.add (Poly.mul (Poly.const c1) Poly.var) (Poly.const c0))

/-- `Q₁ = d₃·x³ + d₂·x² + d₁·x + d₀` — the first-instanton coefficient `P₁′ + 2πi P₁` (degree ≤ 3). -/
noncomputable def Q1 (d0 d1 d2 d3 : MachLib.Real) : Poly :=
  Poly.add (Poly.mul (Poly.const d3) (Poly.mul Poly.var (Poly.mul Poly.var Poly.var)))
           (Poly.add (Poly.mul (Poly.const d2) (Poly.mul Poly.var Poly.var))
                     (Poly.add (Poly.mul (Poly.const d1) Poly.var) (Poly.const d0)))

/-- The one-modulus, one-instanton flux F-term on the real slice, as an `ExpPoly`:
`fTermSlice.eval x = Q₀(x) + Q₁(x)·e^{x}`. -/
noncomputable def fTermSlice (c0 c1 c2 d0 d1 d2 d3 : MachLib.Real) : ExpPoly :=
  ⟨[Q0 c0 c1 c2, Q1 d0 d1 d2 d3]⟩

/-- The nilpotent-orbit part has syntactic degree exactly 2. -/
theorem degreeUpper_Q0 (c0 c1 c2 : MachLib.Real) : degreeUpper (Q0 c0 c1 c2) = 2 := rfl

/-- The first-instanton coefficient has syntactic degree exactly 3. -/
theorem degreeUpper_Q1 (d0 d1 d2 d3 : MachLib.Real) : degreeUpper (Q1 d0 d1 d2 d3) = 3 := rfl

/-- **Gate 2, simplest slice — machine-checked effective count.**

For *any* flux quanta / geometry data `(c₀,c₁,c₂,d₀,d₁,d₂,d₃)`, any slice interval `(a,b)`, and the
genericity condition that the F-term is not identically zero on it, the real critical points of the
one-modulus one-instanton flux superpotential on the slice number **at most 7** — an explicit number
where asymptotic Hodge theory / o-minimality gives only "finitely many."

This is `expPoly_effective_bound` (`rolle_ct`-only, no propagation hypotheses) instantiated on the
landscape's own `ExpPoly`; the bound `2 + deg Q₀ + deg Q₁ = 2 + 2 + 3 = 7` is uniform in the fluxes. -/
theorem fTerm_slice_effective_bound
    (c0 c1 c2 d0 d1 d2 d3 : MachLib.Real) (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ x : MachLib.Real, a < x ∧ x < b ∧ (fTermSlice c0 c1 c2 d0 d1 d2 d3).eval x ≠ 0)
    (zeros : List MachLib.Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ (fTermSlice c0 c1 c2 d0 d1 d2 d3).eval z = 0) :
    zeros.length ≤ 7 := by
  have h := expPoly_effective_bound (fTermSlice c0 c1 c2 d0 d1 d2 d3) a b hab hne zeros hnd hz
  -- `h : zeros.length ≤ coeffs.length + sumSimplifiedDegrees coeffs`
  have hlen : (fTermSlice c0 c1 c2 d0 d1 d2 d3).coeffs.length = 2 := rfl
  -- bound the simplified-degree sum by the computable syntactic-degree sum (= 5)
  have hbound := MachLib.ChainExpPolyMod.sumSimplifiedDegrees_le_sum_degreeUpper
                   (fTermSlice c0 c1 c2 d0 d1 d2 d3).coeffs
  have hfold :
      ((fTermSlice c0 c1 c2 d0 d1 d2 d3).coeffs.map degreeUpper).foldr (· + ·) 0 = 5 := rfl
  rw [hfold] at hbound
  omega

/-- **K-mode effective count — closed form.** Along the `R2` (mode-truncation) axis: for the
`K`-instanton-truncated one-modulus flux F-term — an `ExpPoly` of length `K+1` (modes
`e^{0·x}, …, e^{K·x}`) whose coefficients all have syntactic degree `≤ D` (the nilpotent / polynomial
order) — the real critical points on the slice number **at most `(K+1)·(D+1)`**, given non-degeneracy.

This is the explicit **`(modes)·(degree+1)`** dependence an effective *counting* bound wants — precisely
what the flux counting conjectures (Grimm, arXiv:2311.09295) lack and what o-minimality cannot supply.
For the concrete one-instanton model above (`K=1`, `D=3`) it gives `2·4 = 8`, consistent with (and
looser than) the tight `≤ 7` from the exact per-mode degrees. `rolle_ct`-only, via
`expPoly_effective_bound_uniform`. -/
theorem fTerm_mode_count_bound
    (ep : ExpPoly) (K D : Nat)
    (hlen : ep.coeffs.length = K + 1)
    (hdeg : ∀ p ∈ ep.coeffs, degreeUpper p ≤ D)
    (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ x : MachLib.Real, a < x ∧ x < b ∧ ep.eval x ≠ 0)
    (zeros : List MachLib.Real) (hnd : zeros.Nodup)
    (hz : ∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) :
    zeros.length ≤ (K + 1) * (D + 1) := by
  have h := expPoly_effective_bound_uniform ep D hdeg a b hab hne zeros hnd hz
  rw [hlen] at h
  exact h

end MonogateEML.FluxLandscapeGate2
