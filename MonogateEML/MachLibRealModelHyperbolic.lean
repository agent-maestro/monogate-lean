import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.Exponential

/-!
# `MachLib.Real` soundness witness — the hyperbolic axioms (`sinh`, `cosh`, `tanh`)

Extends the Scope-B soundness witness (`MachLibRealModel.lean` for the field/order/literal core,
`MachLibRealModelAnalytic.lean`/`Batch3`/`Batch4` for exp/log/trig/differentiation/analyticity) to
the hyperbolic family (`MachLib/Hyperbolic.lean`, `MachLib/Trig.lean`'s `tanh`-related axioms) —
the primitives `certcom`'s `pid_tanh_grounded`/`pid_sinh_grounded`/`pid_cosh_grounded` groundings
(`FPGrounding.lean`) rest on. Picked as the first extension target because it's what the newest
certcom result (`CompiledClosedLoop.lean`'s `tanhVar_controller_tracking`) actually needs, closing
the loop on the "which analytic axioms are witnessed" scoping note left there.

**Covered here** (mirrors the axioms verbatim in shape, name in the comment): `sinh`, `cosh`, `tanh`
as opaque constants (`MachLib/Hyperbolic.lean` `sinh`/`cosh`, `MachLib/Trig.lean` `tanh`),
`cosh_pos`, `cosh_ge_one`, `sinh_eq`, `cosh_eq`, `tanh_eq_sinh_div_cosh`, `tanh_zero`, `tanh_lt_one`,
`tanh_neg`. All discharged against Mathlib's `Real.sinh`/`Real.cosh`/`Real.tanh` — every one is a
direct Mathlib lemma citation, no new proof content, matching the "one-liner" character of the
earlier batches' field/exp/log axioms rather than the harder Rolle/finite-zeros ones.

**Follow-on (not here):** the trig-proper family (`sin`/`cos`'s own VALUE axioms — `HasDerivAt_sin`/
`HasDerivAt_cos` are already witnessed via `MachLibRealModelAnalytic.lean`, but `pythagorean`,
`cos_pi_div_two`, `cos_add`, `sin_periodic`, etc. are not), inverse trig (`atan`/`arcsin`/`arccos` and
their `HasDerivAt_*`), `sqrt`, `log10`, and `sin_pos_of_pos_lt_pi_div_two` (`TanLipschitz.lean`) — the
remaining certcom-grounded primitives' axiom footprints, a larger follow-on batch. Also NOT covered,
structurally rather than by omission: `Certcom.realToR`/`real_fpbridge`/`real_X_eps`/`real_X_rounds` —
these are about Lean's opaque `Float`, not about `MachLib.Real`'s own axioms, and cannot be witnessed
by ANY model of `MachLib.Real`'s mathematical structure (see `FPGrounding.lean`'s own docstring).

Everything reduces to the three irreducible Lean axioms; no `sorryAx`.
-/

namespace MonogateEML.RealModel

/-- The hyperbolic axioms of `MachLib.Real`, bundled as an interface. A term of this type is a
model of `sinh`/`cosh`/`tanh` and their defining properties. -/
structure HyperbolicModel where
  R : Type
  zero : R
  one : R
  add : R → R → R
  sub : R → R → R
  div : R → R → R
  neg : R → R
  exp : R → R
  lt : R → R → Prop
  le : R → R → Prop
  sinh : R → R
  cosh : R → R
  tanh : R → R
  cosh_pos : ∀ x, lt zero (cosh x)                                    -- cosh_pos
  cosh_ge_one : ∀ x, le one (cosh x)                                  -- cosh_ge_one
  sinh_eq : ∀ x, sinh x = div (sub (exp x) (exp (neg x))) (add one one)  -- sinh_eq
  cosh_eq : ∀ x, cosh x = div (add (exp x) (exp (neg x))) (add one one)  -- cosh_eq
  tanh_eq_sinh_div_cosh : ∀ x, tanh x = div (sinh x) (cosh x)         -- tanh_eq_sinh_div_cosh
  tanh_zero : tanh zero = zero                                        -- tanh_zero
  tanh_lt_one : ∀ x, lt (tanh x) one                                  -- tanh_lt_one
  tanh_neg : ∀ x, tanh (neg x) = neg (tanh x)                         -- tanh_neg

/-- **The witness.** Mathlib's `ℝ` with `Real.sinh`/`Real.cosh`/`Real.tanh` satisfies every
hyperbolic axiom of `MachLib.Real`. Existence of the term proves that layer consistent relative to
Mathlib — every rule here is a direct Mathlib lemma, no new analysis content. -/
noncomputable def mathlibHyperbolicModel : HyperbolicModel where
  R    := ℝ
  zero := 0
  one  := 1
  add  := (· + ·)
  sub  := (· - ·)
  div  := (· / ·)
  neg  := (- ·)
  exp  := Real.exp
  lt   := (· < ·)
  le   := (· ≤ ·)
  sinh := Real.sinh
  cosh := Real.cosh
  tanh := Real.tanh
  cosh_pos := Real.cosh_pos
  cosh_ge_one := Real.one_le_cosh
  sinh_eq := fun x => by rw [Real.sinh_eq]; norm_num
  cosh_eq := fun x => by rw [Real.cosh_eq]; norm_num
  tanh_eq_sinh_div_cosh := fun x => by
    show Real.tanh x = Real.sinh x / Real.cosh x
    exact Real.tanh_eq_sinh_div_cosh x
  tanh_zero := Real.tanh_zero
  tanh_lt_one := fun x => by
    show Real.tanh x < 1
    rw [Real.tanh_eq_sinh_div_cosh x, div_lt_one (Real.cosh_pos x)]
    exact Real.sinh_lt_cosh x
  tanh_neg := fun x => by
    show Real.tanh (-x) = -Real.tanh x
    exact Real.tanh_neg x

end MonogateEML.RealModel
