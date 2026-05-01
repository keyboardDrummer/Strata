/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

/-!
## Transparency Pass

For each Core procedure, generate a function with the same signature and name
suffixed with `$asFunction`. If a Core procedure is marked as transparent,
attempt to add a body to its function version. In the functional body,
assertions are erased and all calls are to functional versions. If the function
has a body, add a free postcondition to the related procedure that equates the
two.

This IR sits between Laurel and CoreWithLaurelTypes in the pipeline:
  Laurel → UnorderedCoreWithLaurelTypes → CoreWithLaurelTypes → Core
-/

namespace Strata.Laurel

public section

/--
An intermediate representation produced by the transparency pass.
Functions are pure computational procedures (suffixed `$asFunction`);
coreProcedures are the original procedures, each paired with a free
postcondition expression (equating the procedure to its functional version).
-/
public structure UnorderedCoreWithLaurelTypes where
  functions : List Procedure
  coreProcedures : List (Procedure × StmtExprMd)
  datatypes : List DatatypeDefinition
  constants : List Constant

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/-- Deep traversal that strips all Assert and Assume nodes from a StmtExpr tree.
    Assert/Assume nodes are replaced with `LiteralBool true`, and Block nodes
    are collapsed by filtering out trivial `LiteralBool true` leftovers. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert _ | .Assume _ => ⟨.LiteralBool true, e.source⟩
    | .Block stmts label =>
      let stmts' := stmts.filter fun s =>
        match s.val with | .LiteralBool true => false | _ => true
      match stmts' with
      | [] => ⟨.LiteralBool true, e.source⟩
      | [s] => if label.isNone then s else ⟨.Block [s] label, e.source⟩
      | _ => ⟨.Block stmts' label, e.source⟩
    | _ => e) expr

/-- Rewrite StaticCall callees to their `$asFunction` versions,
    but only for procedures whose names appear in `nonExternalNames`. -/
private def rewriteCallsToFunctional (nonExternalNames : List String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .StaticCall callee args =>
      if nonExternalNames.contains callee.text then
        let funcCallee := { callee with text := callee.text ++ "$asFunction", uniqueId := none }
        ⟨.StaticCall funcCallee args, e.source⟩
      else e
    | _ => e) expr

/-- Build a free postcondition equating the procedure's output to its functional version.
    For a procedure `foo(a, b) returns (r)`, produces:
      `r == foo$asFunction(a, b)` -/
private def mkFreePostcondition (proc : Procedure) : StmtExprMd :=
  let funcName := { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
  let inputArgs := proc.inputs.map fun p => mkMd (.Var (.Local p.name))
  let funcCall := mkMd (.StaticCall funcName inputArgs)
  match proc.outputs with
  | [out] => mkMd (.PrimitiveOp .Eq [mkMd (.Var (.Local out.name)), funcCall])
  | _ => mkMd (.LiteralBool true)

/-- Create the function copy of a procedure (suffixed `$asFunction`).
    If the procedure is transparent, include a functional body.
    Otherwise the function is opaque. -/
private def mkFunctionCopy (nonExternalNames : List String) (proc : Procedure) : Procedure :=
  let funcName := { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
  let body := match proc.body with
    | .Transparent b => .Transparent (rewriteCallsToFunctional nonExternalNames (stripAssertAssume b))
    | .Opaque _ _ _ => .Opaque [] none []
    | x => x
  { proc with name := funcName, isFunctional := true, body := body }

/-- Check whether a function copy has a body (i.e. the procedure was transparent). -/
private def functionHasBody (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent _ => true
  | _ => false

/--
Transparency pass: translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.

For each procedure:
- Generate a function with the same signature, named `foo$asFunction`
- If transparent, the function gets a functional body (assertions erased, calls to functional versions)
- If the function has a body, add a free postcondition equating the procedure output to the function
-/
def transparencyPass (program : Program) : UnorderedCoreWithLaurelTypes :=
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let nonExternalNames := nonExternal.map (fun p => p.name.text)
  -- $asFunction copies for non-external procedures
  let asFunctions := nonExternal.map (mkFunctionCopy nonExternalNames)
  -- External procedures get a plain function copy (they have no $asFunction version)
  let externalFunctions := program.staticProcedures.filter (fun p => p.body.isExternal)
    |>.map fun proc => { proc with isFunctional := true }
  let functions := externalFunctions ++ asFunctions
  let coreProcedures := nonExternal.map fun p =>
    let funcCopy := mkFunctionCopy nonExternalNames p
    let freePostcondition :=
      if functionHasBody funcCopy then mkFreePostcondition p
      else mkMd (.LiteralBool true)
    let proc := { p with isFunctional := false }
    (proc, freePostcondition)
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, coreProcedures, datatypes, constants := program.constants }

open Std (Format ToFormat)

def formatUnorderedCoreWithLaurelTypes (p : UnorderedCoreWithLaurelTypes) : Format :=
  let datatypeFmts := p.datatypes.map ToFormat.format
  let constantFmts := p.constants.map ToFormat.format
  let functionFmts := p.functions.map ToFormat.format
  let procFmts := p.coreProcedures.map fun (proc, post) =>
    f!"{ToFormat.format proc}\n  // free postcondition: {ToFormat.format post}"
  Format.joinSep (datatypeFmts ++ constantFmts ++ functionFmts ++ procFmts) "\n\n"

instance : ToFormat UnorderedCoreWithLaurelTypes where
  format := formatUnorderedCoreWithLaurelTypes

end -- public section
end Strata.Laurel
