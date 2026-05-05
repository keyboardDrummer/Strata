/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Eliminate Return Statements

Replaces `return` statements in imperative procedure bodies with assignments
to the output parameters followed by an `exit` to a labelled block that wraps
the entire body. This ensures that code placed after the body block (e.g.,
postcondition assertions inserted by the contract pass) is always reached.

This pass should run after `EliminateReturnsInExpression` (which handles
functional/expression-position returns) and before the contract pass.
-/

namespace Strata.Laurel

public section

private def returnLabel : String := "$return"

/-- Replace `Return val` with `output := val; exit "$return"` (or just `exit`
    for valueless returns). Uses `mapStmtExpr` for bottom-up traversal. -/
private def replaceReturn (source: Option FileRange) (outputs : List Parameter) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Return (some val) =>
      match outputs with
      | [out] =>
        let assign := ⟨ .Assign [⟨ .Local out.name, source⟩ ] val, source⟩
        let exit := ⟨ .Exit returnLabel, source⟩
        ⟨.Block [assign, exit] none, e.source⟩
      | _ => ⟨ .Exit returnLabel, source⟩
    | .Return none => ⟨ .Exit returnLabel, source⟩
    | _ => e) expr

/-- Transform a single procedure: wrap body in a labelled block and replace returns. -/
private def eliminateReturnStmts (proc : Procedure) : Procedure :=
  match proc.body with
  | .Opaque postconds (some impl) mods =>
    let impl' := (replaceReturn proc.name.source) proc.outputs impl
    let wrapped : StmtExprMd := { val := .Block [impl'] (some returnLabel), source := impl.source }
    { proc with body := .Opaque postconds (some wrapped) mods }
  | .Transparent body =>
    let body' := (replaceReturn proc.name.source) proc.outputs body
    let wrapped : StmtExprMd := { val := .Block [body'] (some returnLabel), source := body.source }
    { proc with body := .Transparent wrapped }
  | _ => proc

/-- Transform a program by eliminating return statements in all procedure bodies. -/
def eliminateReturnStatements (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateReturnStmts }

end -- public section

end Strata.Laurel
