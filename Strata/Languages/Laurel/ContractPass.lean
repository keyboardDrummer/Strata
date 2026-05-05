/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
## Contract Pass (Laurel → Laurel)

Removes pre- and postconditions from all procedures and replaces them with
explicit precondition/postcondition helper procedures, assumptions, and
assertions.

For each procedure with contracts:
- Generate a precondition procedure (`foo$pre`) returning the conjunction of preconditions.
- Generate a postcondition procedure (`foo$post`) that takes all inputs and all
  outputs as parameters and returns the conjunction of postconditions. The $post
  procedure is marked as functional and does not call the original procedure.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs, outputs)` at the end of the body.

For each call to a contracted procedure:
- Assign all input arguments to temporary variables before the call.
- Insert `assert foo$pre(temps)` before the call (precondition check).
- After the call, insert `assume foo$post(temps, outputs)` (postcondition assumption).
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkVarMd (v : Variable) : VariableMd := { val := v, source := none }

/-- Build a conjunction of expressions. Returns `LiteralBool true` for an empty list. -/
private def conjoin (exprs : List StmtExprMd) : StmtExprMd :=
  match exprs with
  | [] => mkMd (.LiteralBool true)
  | [e] => e
  | e :: rest => rest.foldl (fun acc x =>
      mkMd (.PrimitiveOp .And [acc, x])) e

/-- Name for the precondition helper procedure. -/
def preCondProcName (procName : String) : String := s!"{procName}$pre"

/-- Name for the postcondition helper procedure. -/
def postCondProcName (procName : String) : String := s!"{procName}$post"

/-- Get postconditions from a procedure body. -/
private def getPostconditions (body : Body) : List Condition :=
  match body with
  | .Opaque postconds _ _ => postconds
  | .Abstract postconds => postconds
  | _ => []

/-- Build a call expression. -/
private def mkCall (callee : String) (args : List StmtExprMd) : StmtExprMd :=
  mkMd (.StaticCall (mkId callee) args)

/-- Convert parameters to identifier expressions. -/
private def paramsToArgs (params : List Parameter) : List StmtExprMd :=
  params.map fun p => mkMd (.Var (.Local p.name))

/-- Build a helper function that returns the conjunction of the given conditions. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (conditions : List Condition) : Procedure :=
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin (conditions.map (·.condition))) }

/-- Build a postcondition function that takes all inputs and all outputs as
    parameters and returns the conjunction of postconditions. The function is
    marked as functional and does not call the original procedure.

    For a procedure `foo(a, b) returns (x, y)` with postcondition `P(a, b, x, y)`,
    generates:
    ```
    function foo$post(a, b, x, y) returns ($result : bool) {
      P(a, b, x, y)
    }
    ``` -/
private def mkPostConditionProc (name : String)
    (inputParams : List Parameter) (outputParams : List Parameter)
    (conditions : List Condition) : Procedure :=
  let allParams := inputParams ++ outputParams
  { name := mkId name
    inputs := allParams
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin (conditions.map (·.condition))) }

/-- Extract a combined summary from a list of conditions. -/
private def combinedSummary (clauses : List Condition) : Option String :=
  let summaries := clauses.filterMap (·.summary)
  match summaries with
  | [] => none
  | [s] => some s
  | ss => some (String.intercalate ", " ss)

/-- Information about a procedure's contracts. -/
private structure ContractInfo where
  hasPreCondition : Bool
  hasPostCondition : Bool
  preName : String
  postName : String
  preSummary : Option String
  postSummary : Option String
  inputParams : List Parameter
  outputParams : List Parameter

/-- Collect contract info for all procedures with contracts. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    let postconds := getPostconditions proc.body
    let hasPre := !proc.preconditions.isEmpty
    let hasPost := !postconds.isEmpty
    if hasPre || hasPost then
      m.insert proc.name.text {
        hasPreCondition := hasPre
        hasPostCondition := hasPost
        preName := preCondProcName proc.name.text
        postName := postCondProcName proc.name.text
        preSummary := combinedSummary proc.preconditions
        postSummary := combinedSummary postconds
        inputParams := proc.inputs
        outputParams := proc.outputs
      }
    else m) {}

/-- Transform a procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let outputArgs := paramsToArgs proc.outputs
  let postconds := getPostconditions proc.body
  let preAssume : List StmtExprMd :=
    if info.hasPreCondition then
      let preSrc := match proc.preconditions.head? with
        | some pc => pc.condition.source
        | none => none
      [⟨.Assume (mkCall info.preName inputArgs), preSrc⟩]
    else []
  let postAssert : List StmtExprMd :=
    if info.hasPostCondition then
      let baseSrc := match postconds.head? with
        | some pc => pc.condition.source
        | none => none
      let summary := info.postSummary.getD "postcondition"
      [⟨.Assert { condition := mkCall info.postName (inputArgs ++ outputArgs), summary := some summary },
        baseSrc⟩]
    else []
  match proc.body with
  | .Transparent body =>
    .Transparent ⟨.Block (preAssume ++ [body] ++ postAssert) none, body.source⟩
  | .Opaque _ (some impl) _ =>
    .Opaque [] (some ⟨.Block (preAssume ++ [impl] ++ postAssert) none, impl.source⟩) []
  | .Opaque _ none _ | .Abstract _ =>
    .Opaque [] (some ⟨ .Block [] none, none⟩) []
  | b => b

/-- Generate a temporary variable name for a call-site input argument. -/
private def tempArgName (calleeText : String) (idx : Nat) : String :=
  s!"${calleeText}$arg{idx}"

/-- Build temp variable assignments and references for a list of arguments. -/
private def mkTempAssigns (callee : Identifier) (args : List StmtExprMd)
    (src : Option FileRange) : List StmtExprMd × List StmtExprMd :=
  let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
  let indexed := args.foldl (fun (acc : List (StmtExprMd × Nat) × Nat) arg =>
    (acc.1 ++ [(arg, acc.2)], acc.2 + 1)) ([], 0) |>.1
  let assigns := indexed.map fun (arg, i) =>
    let tName := tempArgName callee.text i
    let tParam : Parameter := { name := mkId tName, type := { val := .Unknown, source := none } }
    mkWithSrc (.Assign [mkVarMd (.Declare tParam)] arg)
  let refs := indexed.map fun (_, i) =>
    mkMd (.Var (.Local (mkId (tempArgName callee.text i))))
  (assigns, refs)

/-- Rewrite a single statement that may be a call to a contracted procedure.
    Returns a list of statements (the original plus any inserted assert/assume).

    At call sites:
    1. Assign each input argument to a temporary variable.
    2. Assert `foo$pre(temps)` before the call.
    3. Execute the call (using temps as arguments).
    4. Assume `foo$post(temps, outputs)` after the call. -/
private def rewriteStmt (contractInfoMap : Std.HashMap String ContractInfo)
    (e : StmtExprMd) : List StmtExprMd :=
  let src := e.source
  let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
  match e.val with
  | .Assign targets (.mk (.StaticCall callee args) callSrc) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let (tempAssigns, tempArgs) := mkTempAssigns callee args src
      -- Pre-assert
      let preAssert := if info.hasPreCondition
        then [mkWithSrc (.Assert { condition := mkCall info.preName tempArgs, summary := info.preSummary })] else []
      -- Rewrite the call to use temp args
      let rewrittenCall : StmtExprMd := ⟨.Assign targets ⟨.StaticCall callee tempArgs, callSrc⟩, src⟩
      -- Post-assume: pass temps (inputs) ++ targets (outputs)
      let outputArgs := targets.map fun t =>
        match t.val with
        | .Local name => mkMd (.Var (.Local name))
        | .Declare p => mkMd (.Var (.Local p.name))
        | .Field target fieldName => mkMd (.Var (.Field target fieldName))
      let postAssume := if info.hasPostCondition
        then [mkWithSrc (.Assume (mkCall info.postName (tempArgs ++ outputArgs)))] else []
      tempAssigns ++ preAssert ++ [rewrittenCall] ++ postAssume
    | none => [e]
  | .StaticCall callee args =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let (tempAssigns, tempArgs) := mkTempAssigns callee args src
      let preAssert := if info.hasPreCondition
        then [mkWithSrc (.Assert { condition := mkCall info.preName tempArgs, summary := info.preSummary })] else []
      let postAssume := if info.hasPostCondition
        then [mkWithSrc (.Assume (mkCall info.postName tempArgs))] else []
      tempAssigns ++ preAssert ++ postAssume ++ [⟨.StaticCall callee tempArgs, src⟩]
    | none => [e]
  | _ => [e]

/-- Rewrite call sites in a statement/expression tree. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  let result := mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label =>
      let stmts' := stmts.flatMap (rewriteStmt contractInfoMap)
      if stmts'.length == stmts.length then e
      else ⟨.Block stmts' label, e.source⟩
    | _ => e) expr
  -- Handle top-level non-Block statements
  let expanded := rewriteStmt contractInfoMap result
  match expanded with
  | [single] => single
  | many => mkMd (.Block many none)

/-- Rewrite call sites in all bodies of a procedure. -/
private def rewriteCallSitesInProc (contractInfoMap : Std.HashMap String ContractInfo)
    (proc : Procedure) : Procedure :=
  let rw := rewriteCallSites contractInfoMap
  match proc.body with
  | .Transparent body =>
    { proc with body := .Transparent (rw body) }
  | .Opaque posts impl mods =>
    let body := Body.Opaque (posts.map (·.mapCondition rw)) (impl.map rw) (mods.map rw)
    { proc with body := body }
  | _ => proc

/-- Run the contract pass on a Laurel program.
    All procedures with contracts are transformed. -/
def contractPass (program : Program) : Program :=
  let contractInfoMap := collectContractInfo program.staticProcedures

  -- Generate helper procedures for all procedures with contracts
  let helperProcs := program.staticProcedures.flatMap fun proc =>
    let postconds := getPostconditions proc.body
    let preProc :=
      if proc.preconditions.isEmpty then []
      else [mkConditionProc (preCondProcName proc.name.text) proc.inputs proc.preconditions]
    let postProc :=
      if postconds.isEmpty then []
      else [mkPostConditionProc (postCondProcName proc.name.text)
              proc.inputs proc.outputs postconds]
    preProc ++ postProc

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  let transformedProcs := program.staticProcedures.map fun proc =>
    let proc := match contractInfoMap.get? proc.name.text with
      | some info =>
        { proc with
          preconditions := []
          body := transformProcBody proc info }
      | none => proc
    -- Rewrite call sites in the procedure body
    rewriteCallSitesInProc contractInfoMap proc

  { program with staticProcedures := helperProcs ++ transformedProcs }

end -- public section
end Strata.Laurel
