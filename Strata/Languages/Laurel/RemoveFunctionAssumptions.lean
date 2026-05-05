/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
## Remove Function Assumptions (Laurel → Laurel)

Removes `assume` statements from the bodies of functional procedures.
Functions (procedures with `isFunctional = true`) should not contain
assumptions since they are pure and their bodies are inlined at call sites.
Assumptions left over from the contract pass would incorrectly constrain
the function's evaluation context.
-/

namespace Strata.Laurel

public section

/-- Remove all `Assume` nodes from a statement/expression tree. -/
private def removeAssumes (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label =>
      let filtered := stmts.filter fun s =>
        match s.val with
        | .Assume _ => false
        | _ => true
      if filtered.length == stmts.length then e
      else ⟨.Block filtered label, e.source⟩
    | _ => e) expr

/-- Remove assumptions from the body of a single functional procedure. -/
private def removeFunctionAssumptionsProc (proc : Procedure) : Procedure :=
  if !proc.isFunctional then proc
  else
    match proc.body with
    | .Transparent body =>
      { proc with body := .Transparent (removeAssumes body) }
    | .Opaque posts (some impl) mods =>
      { proc with body := .Opaque posts (some (removeAssumes impl)) mods }
    | _ => proc

/-- Remove assumptions from all functional procedures in a program. -/
def removeFunctionAssumptions (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map removeFunctionAssumptionsProc }

end -- public section
end Strata.Laurel
