import MachLib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import MonogateEML.MachLibRealModelRolle

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
def interpEntries : List (Name × Syntax) := [
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
  (`MachLib.Real.exp,           Unhygienic.run `(Real.exp)),
  (`MachLib.Real.HasDerivAt,    Unhygienic.run `(fun (f : ℝ → ℝ) (f' x : ℝ) => HasDerivAt f f' x)) ]

/-- Witness registry: MachLib axiom ↦ a Mathlib term claimed to inhabit its interpreted type.
The claim is CHECKED (not trusted): a wrong entry fails the gate. -/
def witnessRegistry : List (Name × Syntax) := [
  (`MachLib.Real.add_comm,       Unhygienic.run `(add_comm)),
  (`MachLib.Real.add_assoc,      Unhygienic.run `(add_assoc)),
  (`MachLib.Real.add_zero,       Unhygienic.run `(add_zero)),
  (`MachLib.Real.mul_comm,       Unhygienic.run `(mul_comm)),
  (`MachLib.Real.mul_assoc,      Unhygienic.run `(mul_assoc)),
  (`MachLib.Real.mul_one_ax,     Unhygienic.run `(mul_one)),
  (`MachLib.Real.mul_pos,        Unhygienic.run `(fun {a b} => mul_pos)),
  (`MachLib.Real.lt_irrefl_ax,   Unhygienic.run `(lt_irrefl)),
  (`MachLib.Real.lt_trans_ax,    Unhygienic.run `(fun {a b c} => lt_trans)),
  (`MachLib.Real.zero_lt_one_ax, Unhygienic.run `(zero_lt_one)),
  (`MachLib.Real.exp_pos,        Unhygienic.run `(Real.exp_pos)),
  (`MachLib.Real.exp_add,        Unhygienic.run `(Real.exp_add)),
  (`MachLib.Real.exp_zero,       Unhygienic.run `(Real.exp_zero)),
  (`MachLib.Real.rolle_ct,       Unhygienic.run `(MonogateEML.RealModel.rolle_witnessed)) ]

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
def checkWitnessed (m : List (Name × Expr)) (axName : Name) (witnessStx : Syntax) : TermElabM Bool := do
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

end AxiomWitnessBridge
