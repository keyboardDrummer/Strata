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
- Generate a postcondition procedure (`foo$post`) that takes only the *input*
  parameters, internally calls the original procedure to obtain the outputs,
  and returns the conjunction of postconditions.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs)` at the end of the body.

For each call to a contracted procedure:
- Insert `assert foo$pre(args)` before the call (precondition check).
- Insert `assume foo$post(args)` after the call (postcondition assumption).

The postcondition procedure calls the original procedure internally so that
the `assume` at call sites only references pre-call arguments. This avoids
a soundness issue where mutable variables (e.g. `$heap`) are overwritten by
the call's result destructuring before the `assume` is evaluated.
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
  -- Use "$result" as the output name to avoid clashing with user-defined
  -- parameter names (user names cannot contain '$').
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩] -- TODO, enable anonymous output parameters
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin (conditions.map (·.condition))) }

/-- Build a postcondition function that takes both input and output parameters
    and returns the conjunction of postconditions.

    For a procedure `foo(a, b) returns (x, y)` with postcondition `P(a, b, x, y)`,
    generates:
    ```
    function foo$post(a, b, x, y) returns ($result : bool) {
      P(a, b, x, y)
    }
    ```

    At call sites, the assume is placed *after* the assignment so that the
    output variables are bound:
    ```
    var x, y := foo(a_saved, b_saved);
    assume foo$post(a_saved, b_saved, x, y);
    ``` -/
private def mkPostConditionProc (name : String) (_originalProcName : String)
    (inputParams : List Parameter) (outputParams : List Parameter)
    (conditions : List Condition) : Procedure :=
  { name := mkId name
    inputs := inputParams ++ outputParams
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
  /-- Implicit heap parameters that must be prepended to explicit call args. -/
  implicitArgs : List StmtExprMd

/-- Collect contract info for all procedures with contracts. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    let postconds := getPostconditions proc.body
    let hasPre := !proc.preconditions.isEmpty
    let hasPost := !postconds.isEmpty
    if hasPre || hasPost then
      let implicitArgs : List StmtExprMd := []
      m.insert proc.name.text {
        hasPreCondition := hasPre
        hasPostCondition := hasPost
        preName := preCondProcName proc.name.text
        postName := postCondProcName proc.name.text
        preSummary := combinedSummary proc.preconditions
        postSummary := combinedSummary postconds
        inputParams := proc.inputs
        outputParams := proc.outputs
        implicitArgs := implicitArgs
      }
    else m) {}

/-- Transform a procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let postconds := getPostconditions proc.body
  -- Use the source location from the first precondition for the assume node
  let preAssume : List StmtExprMd :=
    if info.hasPreCondition then
      let preSrc := match proc.preconditions.head? with
        | some pc => pc.condition.source
        | none => none
      [⟨.Assume (mkCall info.preName inputArgs), preSrc⟩]
    else []
  let postAssert : List StmtExprMd :=
    if info.hasPostCondition then
      -- Use the source location from the first postcondition so
      -- the diagnostic carries the source location of the `ensures` clause.
      let baseSrc := match postconds.head? with
        | some pc => pc.condition.source
        | none => none
      let summary := info.postSummary.getD "postcondition"
      -- Directly assert the postcondition conjunction rather than calling $post.
      -- The $post procedure re-invokes the original (opaque) procedure to obtain
      -- outputs, which is correct at *call sites* but wrong inside the body:
      -- here the output variables (e.g. $heap) are already in scope with their
      -- actual values, so we assert the postcondition directly.
      [⟨.Assert { condition := conjoin (postconds.map (·.condition)), summary := some summary },
        baseSrc⟩]
    else []
  match proc.body with
  | .Transparent body =>
    .Transparent ⟨.Block (preAssume ++ [body] ++ postAssert) none, body.source⟩
  | .Opaque _ (some impl) _ =>
    .Opaque [] (some ⟨.Block (preAssume ++ [impl] ++ postAssert) none, impl.source⟩)  []
  | .Opaque _ none _ | .Abstract _ =>
    .Opaque [] (some ⟨ .Block [] none, none⟩)  []
  | b => b

/-- Convert assignment targets to variable reference expressions. -/
private def targetsToArgs (targets : List (AstNode Variable)) : List StmtExprMd :=
  targets.map fun t =>
    let name := match t.val with
      | .Local n => n
      | .Declare p => p.name
      | .Field _ n => n  -- best effort
    mkMd (.Var (.Local name))

/-- Rewrite a single statement that may be a call to a contracted procedure.
    Returns a list of statements (the original plus any inserted assert/assume).
    Uses the call site's metadata for generated assert/assume nodes.
    The postcondition assume is placed after the assignment and passes both
    the call arguments and the assigned target variables. -/
private def rewriteStmt (contractInfoMap : Std.HashMap String ContractInfo)
    (e : StmtExprMd) : List StmtExprMd :=
  let src := e.source
  let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
  match e.val with
  | .Assign targets (.mk (.StaticCall callee args) ..) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let fullArgs := info.implicitArgs ++ args
      let preAssert := if info.hasPreCondition
        then [mkWithSrc (.Assert { condition := mkCall info.preName fullArgs, summary := info.preSummary })] else []
      -- Assume $post *after* the assignment, passing both the call arguments
      -- and the assigned target variables so the postcondition can reference outputs.
      let postAssume := if info.hasPostCondition
        then [mkWithSrc (.Assume (mkCall info.postName (fullArgs ++ targetsToArgs targets)))] else []
      preAssert ++ [e] ++ postAssume
    | none => [e]
  | .StaticCall callee args =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let fullArgs := info.implicitArgs ++ args
      let preAssert := if info.hasPreCondition
        then [mkWithSrc (.Assert { condition := mkCall info.preName fullArgs, summary := info.preSummary })] else []
      preAssert ++ [e]
    | none => [e]
  | _ => [e]

/-- Rewrite call sites in a statement/expression tree. Processes Block children
    at the statement level to avoid interfering with expression-level calls.
    For each statement-level call to a contracted procedure, inserts
    `assert pre(args)` before and `assume post(args)` after. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  let result := mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label =>
      let stmts' := stmts.flatMap (rewriteStmt contractInfoMap)
      if stmts'.length == stmts.length then e
      else ⟨.Block stmts' label, e.source⟩
    | _ => e) expr
  -- Handle top-level non-Block statements (e.g., bare Assign or StaticCall)
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

/-- Build an axiom expression from `invokeOn` trigger and ensures clauses.
    Produces `∀ p1, ∀ p2, ..., ∀ pn :: { trigger } (ensures1 && ensures2 && ...)`. -/
private def mkInvokeOnAxiom (params : List Parameter) (trigger : StmtExprMd)
    (postconds : List Condition) : StmtExprMd :=
  let body := conjoin (postconds.map (·.condition))
  -- Wrap in nested Forall from last param (innermost) to first (outermost).
  -- The trigger is placed on the innermost quantifier.
  params.foldr (init := (body, true)) (fun p (acc, isInnermost) =>
    let trig := if isInnermost then some trigger else none
    (mkMd (.Quantifier .Forall p trig acc), false)) |>.1

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
      else [mkPostConditionProc (postCondProcName proc.name.text) proc.name.text
              proc.inputs proc.outputs postconds]
    preProc ++ postProc

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  let transformedProcs := program.staticProcedures.map fun proc =>
    -- Build axioms from invokeOn + ensures BEFORE transforming the body
    -- (transformProcBody strips postconditions from the body)
    let proc := match proc.invokeOn with
      | some trigger =>
        let postconds := getPostconditions proc.body
        if postconds.isEmpty then { proc with invokeOn := none }
        else { proc with
          axioms := [mkInvokeOnAxiom proc.inputs trigger postconds]
          invokeOn := none }
      | none => proc
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
