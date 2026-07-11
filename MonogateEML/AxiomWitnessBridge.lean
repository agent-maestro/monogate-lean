import MachLib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import MonogateEML.MachLibRealModelRolle
import MonogateEML.MachLibRealModelLog

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
  (`MachLib.Real.HasDerivAt,    Unhygienic.run `(fun (f : ℝ → ℝ) (f' x : ℝ) => HasDerivAt f f' x)),
  (`MachLib.RealSet,            Unhygienic.run `((Set ℝ))),
  (`MachLib.Ioi,                Unhygienic.run `((fun a : ℝ => Set.Ioi a))),
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
  (`MachLib.Real.add_lt_add_left, Unhygienic.run `(fun {a b} h c => add_lt_add_left h c)),
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
  (`MachLib.Real.HasDerivAt_inv, Unhygienic.run `(fun f a x hfx hf => by simpa [one_div, sq] using hf.inv hfx)) ]

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
def trustedFootprint : List Name := [`Classical.choice, `MachLib.IsAnalyticOnReals, `MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.Real.HasDerivAt_add, `MachLib.Real.HasDerivAt_comp, `MachLib.Real.HasDerivAt_const, `MachLib.Real.HasDerivAt_exp, `MachLib.Real.HasDerivAt_id, `MachLib.Real.HasDerivAt_inv, `MachLib.Real.HasDerivAt_log_pos, `MachLib.Real.HasDerivAt_mul, `MachLib.Real.HasDerivAt_sub, `MachLib.Real.HasDerivAt_unique, `MachLib.Real.addR, `MachLib.Real.add_assoc, `MachLib.Real.add_comm, `MachLib.Real.add_lt_add_left, `MachLib.Real.add_neg, `MachLib.Real.add_zero, `MachLib.Real.divR, `MachLib.Real.div_def, `MachLib.Real.exp, `MachLib.Real.exp_pos, `MachLib.Real.exp_surj, `MachLib.Real.leR, `MachLib.Real.le_iff_lt_or_eq, `MachLib.Real.ltR, `MachLib.Real.lt_irrefl_ax, `MachLib.Real.lt_total, `MachLib.Real.lt_trans_ax, `MachLib.Real.mulR, `MachLib.Real.mul_assoc, `MachLib.Real.mul_comm, `MachLib.Real.mul_distrib, `MachLib.Real.mul_inv, `MachLib.Real.mul_one_ax, `MachLib.Real.mul_pos, `MachLib.Real.natCast, `MachLib.Real.natCast_succ, `MachLib.Real.natCast_zero, `MachLib.Real.negR, `MachLib.Real.oneR, `MachLib.Real.one_div_pos_of_pos, `MachLib.Real.rolle_ct, `MachLib.Real.subR, `MachLib.Real.sub_def, `MachLib.Real.zeroR, `MachLib.Real.zero_lt_one_ax, `MachLib.Real.zero_ne_one_ax, `MachLib.analytic_add, `MachLib.analytic_comp, `MachLib.analytic_const, `MachLib.analytic_exp, `MachLib.analytic_id, `MachLib.analytic_log_pos, `MachLib.analytic_mul, `MachLib.analytic_one_div_pos, `MachLib.analytic_sub, `Quot.sound, `propext]

/-- Standard Lean axioms — sound by construction, not witnessed here. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Carrier/predicate constants — interpretation-map entries (`Real ↦ ℝ`, `HasDerivAt` /
`IsAnalyticOnReals ↦` Mathlib's), not propositions to witness. -/
def mappedConstants : List Name := [`MachLib.Real, `MachLib.Real.HasDerivAt, `MachLib.IsAnalyticOnReals]

/-- Known-unwitnessed trusted axioms + machine-readable reason. CI-visible; shrinks as witnesses
are added. Trusted-but-unaccounted (not here, not registered, not standard/mapped) FAILS. -/
def witnessGap : List (Name × String) := []

run_cmd Command.liftTermElabM do
  let registered := witnessRegistry.map Prod.fst
  let accounted := registered ++ standardAxioms ++ mappedConstants ++ witnessGap.map Prod.fst
  let unaccounted := trustedFootprint.filter (fun a => !(accounted.contains a))
  unless unaccounted.isEmpty do
    logError m!"AxiomWitnessBridge: {unaccounted.length} trusted axiom(s) UNACCOUNTED \
(not witnessed, not standard/mapped, not a tracked gap): {unaccounted}"
  let staleGap := (witnessGap.map Prod.fst).filter (fun a => !(trustedFootprint.contains a))
  unless staleGap.isEmpty do
    logError m!"AxiomWitnessBridge: stale witnessGap entr(y/ies) no longer trusted: {staleGap}"
  logInfo m!"AxiomWitnessBridge coverage: {registered.length} witnessed + {standardAxioms.length} \
standard + {mappedConstants.length} mapped + {witnessGap.length} tracked-gap = full accounting of \
{trustedFootprint.length} trusted axioms."

end AxiomWitnessBridge
