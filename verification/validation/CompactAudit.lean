import Lean
import Lean.Util.CollectAxioms

/-! Compact source-local audit. It prints no proof or definition bodies.
The exact source and emitted olean are bound by the external SHA256 manifest.
All declarations of the actual current module, including private/generated
ones, are enumerated from Lean's environment and their axiom closures checked.
Endpoint types are additionally compared by fully transparent definitional
equality against an independently named proposition specification. -/

open Lean Elab Command

namespace KEBallCompactValidation

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def permittedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def allUsedConstants (ci : ConstantInfo) : Array Name := Id.run do
  let mut names := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    names := names ++ value.getUsedConstants
  return (names.foldl (fun (s : NameSet) n => s.insert n) {}).toArray.qsort Name.lt

private def typePP (e : Expr) : CommandElabM String := do
  runTermElabM fun _ => withOptions (fun o =>
      let o := o.setBool `pp.proofs false
      let o := o.setBool `pp.fullNames true
      let o := o.setBool `pp.universes true
      let o := o.setBool `pp.privateNames true
      o.set `pp.width (120 : Nat)) do
    return (← Meta.ppExpr e).pretty 120

syntax (name := keCompactAuditModule)
  "#ke_compact_audit_module " str str str : command

@[command_elab keCompactAuditModule]
def elabCompactAuditModule : CommandElab := fun stx => do
  let expectedModule := stx[1].isStrLit?.getD ""
  let nonce := stx[2].isStrLit?.getD ""
  let sourceHash := stx[3].isStrLit?.getD ""
  let env := (← getEnv).setExporting false
  unless env.mainModule.toString == expectedModule do
    throwError "audit module mismatch: expected {expectedModule}, actual {env.mainModule}"
  let declarations := (env.constants.toList.filter fun (name, _) =>
    (env.getModuleIdxFor? name).isNone).toArray.qsort (fun a b => Name.lt a.1 b.1)
  let mut violations : Array String := #[]
  for (name, ci) in declarations do
    unless (env.checked.get.find? name).isSome do
      throwError "audit cannot find checked declaration {name}"
    let axioms ← collectAxioms name
    let forbidden := axioms.filter (fun a => !permittedAxiom a)
    if !forbidden.isEmpty || ci.type.hasMVar then
      violations := violations.push name.toString
    let row := Json.mkObj [
      ("record", toJson ("declaration" : String)),
      ("nonce", toJson nonce), ("module", toJson expectedModule),
      ("source_sha256", toJson sourceHash),
      ("name", toJson name.toString), ("kind", toJson (kindName ci)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type_structural_hash_lean_uint64", toJson (toString (hash ci.type))),
      ("direct_dependencies", toJson ((allUsedConstants ci).map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString)),
      ("forbidden_axioms", toJson (forbidden.map Name.toString)),
      ("has_type_metavariables", toJson ci.type.hasMVar),
      ("is_private_name", toJson (isPrivateName name))]
    liftIO <| IO.println ("KE_BALL_COMPACT_JSON:" ++ row.compress)
  let summary := Json.mkObj [
    ("record", toJson ("module_complete" : String)),
    ("nonce", toJson nonce), ("module", toJson expectedModule),
    ("source_sha256", toJson sourceHash),
    ("declaration_count", toJson declarations.size),
    ("forbidden_declarations", toJson violations)]
  liftIO <| IO.println ("KE_BALL_COMPACT_JSON:" ++ summary.compress)
  unless violations.isEmpty do
    throwError "Forbidden axioms or metavariables in {violations.size} declarations"

syntax (name := keCompactAuditEndpoint)
  "#ke_compact_audit_endpoint " str str str str : command

@[command_elab keCompactAuditEndpoint]
def elabCompactAuditEndpoint : CommandElab := fun stx => do
  let role := stx[1].isStrLit?.getD ""
  let proofName := (stx[2].isStrLit?.getD "").toName
  let specificationName := (stx[3].isStrLit?.getD "").toName
  let nonce := stx[4].isStrLit?.getD ""
  let env := (← getEnv).setExporting false
  let some ci := env.find? proofName
    | throwError "Endpoint proof declaration is missing: {proofName}"
  let some si := env.find? specificationName
    | throwError "Endpoint specification is missing: {specificationName}"
  unless ci.isTheorem do
    throwError "Endpoint proof is not a theorem declaration: {proofName}"
  let typeMatches ← runTermElabM fun _ =>
    Meta.withTransparency .all <| Meta.isDefEq ci.type (mkConst specificationName)
  unless typeMatches do
    throwError "Endpoint {proofName} does not prove specification {specificationName}"
  let axioms ← collectAxioms proofName
  unless axioms.all permittedAxiom do
    throwError "Endpoint {proofName} uses a forbidden axiom"
  let specText ← match si.value? with
    | some e => typePP e
    | none => pure "NO_DEFINITION_BODY"
  let row := Json.mkObj [
    ("record", toJson ("endpoint" : String)), ("nonce", toJson nonce),
    ("role", toJson role), ("proof_declaration", toJson proofName.toString),
    ("specification", toJson specificationName.toString),
    ("exact_type_matches", toJson typeMatches),
    ("proof_type_expression", toJson (reprStr ci.type)),
    ("specification_pretty_without_proofs", toJson specText),
    ("transitive_axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.println ("KE_BALL_COMPACT_JSON:" ++ row.compress)

end KEBallCompactValidation
