/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Generic Bottom-Up AST Traversal

Provides `mapStmtExprM`, a generic bottom-up monadic traversal of `StmtExprMd`.
Children are recursively traversed first, then the user-supplied function `f` is
applied to the result. Passes that only need custom logic for a few constructors
can pattern-match in `f` and fall through for the rest.

Also provides `mapProcedureBodiesM` and `mapProgramM` to eliminate the
`Body`/`Procedure`/`Program` boilerplate shared by nearly every pass.

## Pre/Post Hook Traversal

`mapStmtExprPrePostM` extends the basic traversal with:
- A `pre` hook that can override recursion for specific constructors
- A `reverseChildren` flag for right-to-left sibling traversal

When `pre` returns `some result`, the traversal skips recursion and uses that
result directly. When `pre` returns `none`, the generic recursion + `post`
proceeds as normal.
-/

namespace Strata.Laurel

public section

/--
Bottom-up monadic traversal of `StmtExprMd`. Recurses into all `StmtExprMd`
children first, then applies `f` to the rebuilt node.
-/
def mapStmtExprM [Monad m] (f : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd := do
  let source := expr.source
  -- `.attach` wraps each element with a proof of membership, which the
  -- termination checker uses to show the recursive call is on a smaller value.
  let rebuilt ← match _h : expr.val with
  | .IfThenElse cond th el =>
    pure ⟨.IfThenElse (← mapStmtExprM f cond) (← mapStmtExprM f th)
      (← el.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Block stmts label =>
    pure ⟨.Block (← stmts.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e) label, source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprM f cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← mapStmtExprM f body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Assign targets value =>
    let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprM f target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← mapStmtExprM f value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← mapStmtExprM f target) fieldName), source⟩
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← mapStmtExprM f target) fieldName (← mapStmtExprM f newValue), source⟩
  | .StaticCall callee args =>
    pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .PrimitiveOp op args =>
    pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← mapStmtExprM f lhs) (← mapStmtExprM f rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← mapStmtExprM f target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← mapStmtExprM f target) ty, source⟩
  | .InstanceCall target callee args =>
    pure ⟨.InstanceCall (← mapStmtExprM f target) callee
      (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← mapStmtExprM f body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← mapStmtExprM f name), source⟩
  | .Old value =>
    pure ⟨.Old (← mapStmtExprM f value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← mapStmtExprM f value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← mapStmtExprM f cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← mapStmtExprM f cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← mapStmtExprM f value) (← mapStmtExprM f proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← mapStmtExprM f func), source⟩
  -- Leaves: no StmtExprMd children.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise all passes will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  f rebuilt
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- Pure bottom-up traversal of `StmtExprMd`. -/
def mapStmtExpr (f : StmtExprMd → StmtExprMd) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprM (m := Id) f expr)

/--
Map a monadic function over the immediate `StmtExprMd` children of a node
(one level only, no recursion). The node is rebuilt with the transformed children.

When `reverseChildren` is `true`, list-valued children (e.g. arguments) are
traversed right-to-left and the results are reversed back to original order.

This is useful for passes that handle specific constructors with custom logic
but want generic child traversal for all other constructors.
-/
def mapStmtExprChildrenM [Monad m] (f : StmtExprMd → m StmtExprMd)
    (reverseChildren : Bool := false)
    (expr : StmtExprMd) : m StmtExprMd := do
  let source := expr.source
  match expr.val with
  | .IfThenElse cond th el =>
    let seqEl ← el.mapM fun e => f e
    pure ⟨.IfThenElse (← f cond) (← f th) seqEl, source⟩
  | .Block stmts label =>
    let mapped ← if reverseChildren then do
      let r ← stmts.reverse.mapM f
      pure r.reverse
    else
      stmts.mapM f
    pure ⟨.Block mapped label, source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← f cond) (← invs.mapM f) (← dec.mapM f) (← f body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.mapM f), source⟩
  | .Assign targets value =>
    let targets' ← targets.mapM fun v => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← f target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← f value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← f target) fieldName), source⟩
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← f target) fieldName (← f newValue), source⟩
  | .StaticCall callee args =>
    let mapped ← if reverseChildren then do
      let r ← args.reverse.mapM f
      pure r.reverse
    else
      args.mapM f
    pure ⟨.StaticCall callee mapped, source⟩
  | .PrimitiveOp op args =>
    let mapped ← if reverseChildren then do
      let r ← args.reverse.mapM f
      pure r.reverse
    else
      args.mapM f
    pure ⟨.PrimitiveOp op mapped, source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← f lhs) (← f rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← f target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← f target) ty, source⟩
  | .InstanceCall target callee args =>
    let mapped ← if reverseChildren then do
      let r ← args.reverse.mapM f
      pure r.reverse
    else
      args.mapM f
    pure ⟨.InstanceCall (← f target) callee mapped, source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param (← trigger.mapM f) (← f body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← f name), source⟩
  | .Old value =>
    pure ⟨.Old (← f value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← f value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← f cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← f cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← f value) (← f proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← f func), source⟩
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr

/--
Monadic traversal of `StmtExprMd` with pre/post hooks and optional right-to-left
child traversal.

- `pre`: called before recursion. If it returns `some e`, that value is used
  directly (no recursion into children). If it returns `none`, the generic
  recursion proceeds followed by `post`.
- `post`: applied to the rebuilt node after children have been recursively
  traversed. Only called when `pre` returned `none`.
- `reverseChildren`: when `true`, list-valued children (e.g. arguments) are
  traversed right-to-left and the results are reversed back to original order.
-/
def mapStmtExprPrePostM [Monad m]
    (pre : StmtExprMd → m (Option StmtExprMd))
    (post : StmtExprMd → m StmtExprMd)
    (reverseChildren : Bool := false)
    (expr : StmtExprMd) : m StmtExprMd := do
  match ← pre expr with
  | some result => return result
  | none =>
  let source := expr.source
  let rebuilt ← match _h : expr.val with
  | .IfThenElse cond th el =>
    let seqEl ← el.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
    pure ⟨.IfThenElse (← mapStmtExprPrePostM pre post reverseChildren cond)
      (← mapStmtExprPrePostM pre post reverseChildren th) seqEl, source⟩
  | .Block stmts label =>
    let mapped ← if reverseChildren then do
      let r ← stmts.attach.reverse.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
      pure r.reverse
    else
      stmts.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
    pure ⟨.Block mapped label, source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprPrePostM pre post reverseChildren cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e)
      (← mapStmtExprPrePostM pre post reverseChildren body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e), source⟩
  | .Assign targets value =>
    let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprPrePostM pre post reverseChildren target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← mapStmtExprPrePostM pre post reverseChildren value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← mapStmtExprPrePostM pre post reverseChildren target) fieldName), source⟩
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← mapStmtExprPrePostM pre post reverseChildren target) fieldName
      (← mapStmtExprPrePostM pre post reverseChildren newValue), source⟩
  | .StaticCall callee args =>
    let mapped ← if reverseChildren then do
      let r ← args.attach.reverse.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
      pure r.reverse
    else
      args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
    pure ⟨.StaticCall callee mapped, source⟩
  | .PrimitiveOp op args =>
    let mapped ← if reverseChildren then do
      let r ← args.attach.reverse.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
      pure r.reverse
    else
      args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
    pure ⟨.PrimitiveOp op mapped, source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← mapStmtExprPrePostM pre post reverseChildren lhs)
      (← mapStmtExprPrePostM pre post reverseChildren rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← mapStmtExprPrePostM pre post reverseChildren target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← mapStmtExprPrePostM pre post reverseChildren target) ty, source⟩
  | .InstanceCall target callee args =>
    let mapped ← if reverseChildren then do
      let r ← args.attach.reverse.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
      pure r.reverse
    else
      args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e
    pure ⟨.InstanceCall (← mapStmtExprPrePostM pre post reverseChildren target) callee mapped, source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param
      (← trigger.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post reverseChildren e)
      (← mapStmtExprPrePostM pre post reverseChildren body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← mapStmtExprPrePostM pre post reverseChildren name), source⟩
  | .Old value =>
    pure ⟨.Old (← mapStmtExprPrePostM pre post reverseChildren value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← mapStmtExprPrePostM pre post reverseChildren value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← mapStmtExprPrePostM pre post reverseChildren cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← mapStmtExprPrePostM pre post reverseChildren cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← mapStmtExprPrePostM pre post reverseChildren value)
      (← mapStmtExprPrePostM pre post reverseChildren proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← mapStmtExprPrePostM pre post reverseChildren func), source⟩
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  post rebuilt
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- Apply a monadic transformation to all procedure bodies. -/
def mapProcedureBodiesM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  match proc.body with
  | .Transparent b => return { proc with body := .Transparent (← f b) }
  | .Opaque posts impl mods =>
    return { proc with body := .Opaque (← posts.mapM (·.mapM f)) (← impl.mapM f) (← mods.mapM f) }
  | .Abstract posts => return { proc with body := .Abstract (← posts.mapM (·.mapM f)) }
  | .External => return proc

/-- Apply a monadic transformation to all `StmtExprMd` nodes in a procedure
    (preconditions, decreases, body, and invokeOn). -/
def mapProcedureM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  let proc ← mapProcedureBodiesM f proc
  return { proc with
    preconditions := ← proc.preconditions.mapM (·.mapM f)
    decreases := ← proc.decreases.mapM f
    invokeOn := ← proc.invokeOn.mapM f }

/-- Apply a monadic transformation to procedure bodies in a program.
    Does **not** traverse preconditions, decreases, or invokeOn — use
    `mapProcedureM` directly if those are needed. -/
def mapProgramM [Monad m] (f : StmtExprMd → m StmtExprMd) (program : Program) : m Program := do
  return { program with staticProcedures := ← program.staticProcedures.mapM (mapProcedureBodiesM f) }

/-- Apply a pure transformation to all `StmtExprMd` nodes in a program. -/
def mapProgram (f : StmtExprMd → StmtExprMd) (program : Program) : Program :=
  mapProgramM (m := Id) f program

end -- public section
end Strata.Laurel
