import Lean
import Lean.Util.CollectAxioms

/-!
Source-local validation support. This module defines no mathematical axioms.
The command is appended to an exact source replay after the last declaration.
It enumerates the checked kernel environment, including private and generated
declarations of the current module, and asks Lean for every transitive axiom
closure. It fails on every axiom except the three explicitly permitted ones.
-/

open Lean Elab Command

namespace KEBallValidation

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def definitionValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

private def allUsedConstants (ci : ConstantInfo) : Array Name := Id.run do
  let mut names := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    names := names ++ value.getUsedConstants
  return (names.foldl (fun (s : NameSet) n => s.insert n) {}).toArray.qsort Name.lt

private def permittedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def fullPP (e : Expr) : CommandElabM String := do
  runTermElabM fun _ => withOptions (fun o =>
      let o := o.setBool `pp.all true
      let o := o.setBool `pp.privateNames true
      let o := o.setBool `pp.proofs true
      let o := o.setBool `pp.deepTerms true
      let o := o.setBool `pp.fullNames true
      let o := o.setBool `pp.universes true
      let o := o.setBool `pp.notation false
      let o := o.set `pp.maxSteps (10000000 : Nat)
      let o := o.set `pp.width (120 : Nat)
      o.set `maxRecDepth (100000 : Nat)) do
    return (← Meta.ppExpr e).pretty 120

syntax (name := keAuditCurrentModule)
  "#ke_audit_current_module " str str str : command

@[command_elab keAuditCurrentModule]
def elabAuditCurrentModule : CommandElab := fun stx => do
  let expectedModule := stx[1].isStrLit?.getD ""
  let nonce := stx[2].isStrLit?.getD ""
  let sourceHash := stx[3].isStrLit?.getD ""
  let env := (← getEnv).setExporting false
  if env.mainModule.toString != expectedModule then
    throwError "audit module mismatch: expected {expectedModule}, actual {env.mainModule}"
  -- `toKernelEnv` forces pending kernel checks. No textual declaration list is used.
  let declarations := (env.constants.toList.filter fun (name, _) =>
    (env.getModuleIdxFor? name).isNone).toArray.qsort (fun a b => Name.lt a.1 b.1)
  let mut violations : Array String := #[]
  for (name, ci) in declarations do
    unless (env.checked.get.find? name).isSome do
      throwError "audit cannot find checked declaration {name}"
    let axioms ← collectAxioms name
    let forbidden := axioms.filter (fun a => !permittedAxiom a)
    if !forbidden.isEmpty then
      violations := violations.push name.toString
    let typeText ← fullPP ci.type
    let bodyText ← match definitionValue? ci with
      | some e => Json.str <$> fullPP e
      | none => pure Json.null
    let row := Json.mkObj [
      ("record", toJson ("declaration" : String)),
      ("nonce", toJson nonce),
      ("module", toJson expectedModule),
      ("source_sha256", toJson sourceHash),
      ("name", toJson name.toString),
      ("kind", toJson (kindName ci)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type_pp_all", toJson typeText),
      ("type_expression", toJson (reprStr ci.type)),
      ("definition_body_pp_all", bodyText),
      ("direct_dependencies", toJson ((allUsedConstants ci).map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString)),
      ("forbidden_axioms", toJson (forbidden.map Name.toString)),
      ("has_type_metavariables", toJson ci.type.hasMVar),
      ("is_private_name", toJson (isPrivateName name))]
    liftIO <| IO.println ("KE_BALL_AUDIT_JSON:" ++ row.compress)
  let summary := Json.mkObj [
    ("record", toJson ("module_complete" : String)),
    ("nonce", toJson nonce),
    ("module", toJson expectedModule),
    ("source_sha256", toJson sourceHash),
    ("declaration_count", toJson declarations.size),
    ("forbidden_declarations", toJson violations)]
  liftIO <| IO.println ("KE_BALL_AUDIT_JSON:" ++ summary.compress)
  unless violations.isEmpty do
    throwError "Forbidden transitive axioms in {violations.size} current-module declarations"

end KEBallValidation

namespace KEBallValidation

syntax (name := keAuditEndpoint)
  "#ke_audit_endpoint " str str str str : command

@[command_elab keAuditEndpoint]
def elabAuditEndpoint : CommandElab := fun stx => do
  let role := stx[1].isStrLit?.getD ""
  let proofName := (stx[2].isStrLit?.getD "").toName
  let specificationName := (stx[3].isStrLit?.getD "").toName
  let nonce := stx[4].isStrLit?.getD ""
  let env := (← getEnv).setExporting false
  let some ci := env.find? proofName
    | throwError "Endpoint proof declaration is missing: {proofName}"
  unless (env.find? specificationName).isSome do
    throwError "Endpoint specification is missing: {specificationName}"
  let typeMatches ← runTermElabM fun _ =>
    Meta.withTransparency .all <| Meta.isDefEq ci.type (mkConst specificationName)
  unless typeMatches do
    throwError "Endpoint {proofName} does not prove the exact specification {specificationName}"
  let axioms ← collectAxioms proofName
  unless axioms.all permittedAxiom do
    throwError "Endpoint {proofName} uses a forbidden axiom"
  let row := Json.mkObj [
    ("record", toJson ("endpoint" : String)), ("nonce", toJson nonce),
    ("role", toJson role), ("proof_declaration", toJson proofName.toString),
    ("specification", toJson specificationName.toString),
    ("exact_type_matches", toJson typeMatches),
    ("transitive_axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.println ("KE_BALL_AUDIT_JSON:" ++ row.compress)

end KEBallValidation
