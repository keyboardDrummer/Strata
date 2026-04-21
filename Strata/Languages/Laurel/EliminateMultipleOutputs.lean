/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Eliminate Multiple Outputs

Transforms functional procedures (`.isFunctional = true`) with multiple outputs
into procedures that return a single synthesized result datatype. Call sites are
rewritten to destructure the result using the generated accessors.

This pass operates on `Program → Program`.
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkTy (t : HighType) : HighTypeMd := { val := t, source := none }

/-- Info about a function whose multiple outputs have been collapsed into a result datatype. -/
private structure MultiOutInfo where
  funcName : String
  resultTypeName : String
  constructorName : String
  outputs : List Parameter

/-- Identify functional procedures with multiple outputs. -/
private def collectMultiOutFunctions (procs : List Procedure) : List MultiOutInfo :=
  procs.filterMap fun f =>
    if f.isFunctional && f.outputs.length > 1 then
      some {
        funcName := f.name.text
        resultTypeName := s!"{f.name.text}$result"
        constructorName := s!"{f.name.text}$result$mk"
        outputs := f.outputs
      }
    else none

/-- Generate a result datatype for a multi-output function. -/
private def mkResultDatatype (info : MultiOutInfo) : DatatypeDefinition :=
  let args := info.outputs.zipIdx.map fun (p, i) =>
    { name := mkId s!"out{i}", type := p.type : Parameter }
  { name := mkId info.resultTypeName
    typeArgs := []
    constructors := [{ name := mkId info.constructorName, args := args }] }

/-- Transform a multi-output function to return the result datatype. -/
private def transformFunction (info : MultiOutInfo) (proc : Procedure) : Procedure :=
  let resultOutput : Parameter :=
    { name := mkId "$result", type := mkTy (.UserDefined (mkId info.resultTypeName)) }
  { proc with outputs := [resultOutput] }

/-- Destructor name for field `outN` of the result datatype. -/
private def destructorName (info : MultiOutInfo) (idx : Nat) : String :=
  s!"{info.resultTypeName}..out{idx}"

/-- Rewrite a statement list, replacing multi-output call patterns. -/
private def rewriteStmts (infoMap : Std.HashMap String MultiOutInfo)
    (stmts : List StmtExprMd) : List StmtExprMd :=
  let rec go (remaining : List StmtExprMd) (acc : List StmtExprMd) : List StmtExprMd :=
    match remaining with
    | [] => acc.reverse
    | stmt :: rest =>
      match stmt.val with
      | .Assign targets ⟨.StaticCall callee args, callSrc, callMd⟩ =>
        match infoMap.get? callee.text with
        | some info =>
          let tempName := mkId s!"${callee.text}$temp"
          let tempTy := mkTy (.UserDefined (mkId info.resultTypeName))
          let tempDecl := mkMd (.LocalVariable tempName tempTy
            (some ⟨.StaticCall callee args, callSrc, callMd⟩))
          let assigns := targets.zipIdx.map fun (tgt, i) =>
            mkMd (.Assign [tgt]
              (mkMd (.StaticCall (mkId (destructorName info i))
                [mkMd (.Identifier tempName)])))
          go rest (assigns.reverse ++ (tempDecl :: acc))
        | none => go rest (stmt :: acc)
      | .LocalVariable name _ty (some ⟨.StaticCall callee args, callSrc, callMd⟩) =>
        match infoMap.get? callee.text with
        | some info =>
          match info.outputs with
          | firstOut :: _ =>
            let tempName := mkId s!"${callee.text}$temp"
            let tempTy := mkTy (.UserDefined (mkId info.resultTypeName))
            let tempDecl := mkMd (.LocalVariable tempName tempTy
              (some ⟨.StaticCall callee args, callSrc, callMd⟩))
            let localDecl := mkMd (.LocalVariable name firstOut.type
              (some (mkMd (.StaticCall (mkId (destructorName info 0))
                [mkMd (.Identifier tempName)]))))
            go rest (localDecl :: tempDecl :: acc)
          | [] => go rest (stmt :: acc)
        | none => go rest (stmt :: acc)
      | _ => go rest (stmt :: acc)
  go stmts []

/-- Rewrite blocks in a StmtExprMd tree to handle multi-output calls. -/
private def rewriteExpr (infoMap : Std.HashMap String MultiOutInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label => ⟨.Block (rewriteStmts infoMap stmts) label, e.source, e.md⟩
    | _ => e) expr

/-- Rewrite all procedure bodies. -/
private def rewriteProcedure (infoMap : Std.HashMap String MultiOutInfo)
    (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent b =>
    let wrapped := mkMd (.Block [b] none)
    let rewritten := rewriteExpr infoMap wrapped
    { proc with body := .Transparent rewritten }
  | .Opaque posts (some impl) mods =>
    let wrapped := mkMd (.Block [impl] none)
    let rewritten := rewriteExpr infoMap wrapped
    { proc with body := .Opaque posts (some rewritten) mods }
  | _ => proc

/-- Eliminate multiple outputs from a Program. Only applies to functional procedures. -/
def eliminateMultipleOutputs (program : Program) : Program :=
  let infos := collectMultiOutFunctions program.staticProcedures
  if infos.isEmpty then program else
  let infoMap : Std.HashMap String MultiOutInfo :=
    infos.foldl (fun m info => m.insert info.funcName info) {}
  let newDatatypes := infos.map mkResultDatatype
  let procs := program.staticProcedures.map fun f =>
    match infoMap.get? f.name.text with
    | some info => rewriteProcedure infoMap (transformFunction info f)
    | none => rewriteProcedure infoMap f
  { program with
    staticProcedures := procs
    types := program.types ++ newDatatypes.map TypeDefinition.Datatype }

end -- public section
end Strata.Laurel
