/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Syntax
public import Strata.Languages.Laurel.Laurel
public import Strata.DL.Imperative.MetaData
import Strata.DDM.Util.Decimal

/-! # Laurel Grammar via Bidirectional Parser Combinators

This module defines the Laurel grammar using the bidirectional syntax
combinator library from `Strata.Util.Syntax`. The same grammar definition
is used for both parsing (String → Laurel.Program) and pretty-printing
(Laurel.Program → String).

## Mutual recursion

The expression grammar is inherently mutually recursive (e.g. `atom` references
`prec0` for sub-expressions, while `prec0` references `postfix` which references
`atom`). We resolve this using a `GrammarLibrary` that maps names (`"atom"`,
`"postfix"`, `"prec0"`) to grammars, allowing each grammar to reference the
others via `ref`.
-/

namespace Strata.Laurel.CombinatorGrammar

open Strata.Syntax
open Strata.Laurel

private def emptyMd : Imperative.MetaData Core.Expression := .empty

private def wm (v : a) : WithMetadata a := ⟨v, emptyMd⟩

/-! ## Reserved words -/

private def operationBEq : Operation → Operation → Bool
  | .Eq, .Eq => true | .Neq, .Neq => true | .And, .And => true | .Or, .Or => true
  | .Not, .Not => true | .Implies, .Implies => true | .AndThen, .AndThen => true
  | .OrElse, .OrElse => true | .Neg, .Neg => true | .Add, .Add => true
  | .Sub, .Sub => true | .Mul, .Mul => true | .Div, .Div => true | .Mod, .Mod => true
  | .DivT, .DivT => true | .ModT, .ModT => true | .Lt, .Lt => true | .Leq, .Leq => true
  | .Gt, .Gt => true | .Geq, .Geq => true | .StrConcat, .StrConcat => true
  | _, _ => false

private def reservedWords : List String :=
  ["procedure", "function", "composite", "constrained", "datatype",
   "var", "if", "then", "else", "while", "for", "return", "assert",
   "assume", "requires", "ensures", "modifies", "invokeOn", "returns",
   "new", "true", "false", "forall", "exists", "exit", "external",
   "int", "bool", "real", "float64", "string", "is", "as",
   "extends", "invariant", "witness", "where", "summary"]

private def identNotReserved : Syntax String :=
  { parse := fun s => do
      let (name, s') ← ident.parse s
      if reservedWords.contains name then none
      else some (name, s')
    print := fun name =>
      if reservedWords.contains name then none
      else ident.print name }

/-! ## Type syntax -/

private partial def mkHighTypeSyntax (_ : Unit) : Syntax HighTypeMd :=
  let self := mkHighTypeSyntax ()
  alt (map { apply := fun () => some (wm .TInt), unapply := fun t => if t.val matches .TInt then some () else none } (keyword "int"))
  (alt (map { apply := fun () => some (wm .TBool), unapply := fun t => if t.val matches .TBool then some () else none } (keyword "bool"))
  (alt (map { apply := fun () => some (wm .TReal), unapply := fun t => if t.val matches .TReal then some () else none } (keyword "real"))
  (alt (map { apply := fun () => some (wm .TFloat64), unapply := fun t => if t.val matches .TFloat64 then some () else none } (keyword "float64"))
  (alt (map { apply := fun () => some (wm .TString), unapply := fun t => if t.val matches .TString then some () else none } (keyword "string"))
  (alt (map { apply := fun ((), name) => some (wm (.TCore name))
              unapply := fun t => match t.val with | .TCore s => some ((), s) | _ => none }
         (seq (keyword "Core") ident))
  (alt (map { apply := fun (((), k), v) => some (wm (.TMap k v))
              unapply := fun t => match t.val with | .TMap k v => some (((), k), v) | _ => none }
         (seq (seq (keyword "Map") self) self))
  (map { apply := fun name => some (wm (.UserDefined (mkId name)))
         unapply := fun t => match t.val with | .UserDefined id => some id.text | _ => none }
    identNotReserved)))))))

def highTypeSyntax : Syntax HighTypeMd := mkHighTypeSyntax ()

/-! ## Parameter syntax -/

def parameterSyntax : Syntax Parameter :=
  map { apply := fun (name, ((), ty)) =>
          some { name := mkId name, type := ty }
        unapply := fun p =>
          some (p.name.text, ((), p.type)) }
    (seq identNotReserved (seq (token ":") highTypeSyntax))

def parameterList : Syntax (List Parameter) :=
  sepBy parameterSyntax (token ",")

/-! ## Binary operators -/

private structure BinOp where
  sym : String
  op : Operation
  prec : Nat
  rightAssoc : Bool := false

private def binOps : List BinOp := [
  { sym := " ==> ", op := .Implies, prec := 15, rightAssoc := true },
  { sym := " || ", op := .OrElse, prec := 20 },
  { sym := " | ", op := .Or, prec := 20 },
  { sym := " && ", op := .AndThen, prec := 30 },
  { sym := " & ", op := .And, prec := 30 },
  { sym := " == ", op := .Eq, prec := 40 },
  { sym := " != ", op := .Neq, prec := 40 },
  { sym := " >= ", op := .Geq, prec := 40 },
  { sym := " <= ", op := .Leq, prec := 40 },
  { sym := " > ", op := .Gt, prec := 40 },
  { sym := " < ", op := .Lt, prec := 40 },
  { sym := " ++ ", op := .StrConcat, prec := 60 },
  { sym := " + ", op := .Add, prec := 60 },
  { sym := " - ", op := .Sub, prec := 60 },
  { sym := " /t ", op := .DivT, prec := 70 },
  { sym := " %t ", op := .ModT, prec := 70 },
  { sym := " * ", op := .Mul, prec := 70 },
  { sym := " / ", op := .Div, prec := 70 },
  { sym := " % ", op := .Mod, prec := 70 }
]

private def isWsChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def countWsPrefix (s : String) : Nat :=
  s.toList.takeWhile isWsChar |>.length

private def tryParseBinOp (s : PState) : Option (BinOp × PState) :=
  let rest := (s.input.drop s.pos).toString
  let wsConsumed := countWsPrefix rest
  let s' := { s with pos := s.pos + wsConsumed }
  binOps.findSome? fun bop =>
    let trimSym := (bop.sym.dropWhile isWsChar).toString
    let rest' := (s.input.drop s'.pos).toString
    if rest'.startsWith trimSym then
      some (bop, { s' with pos := s'.pos + trimSym.length })
    else none

private def opSym (op : Operation) : Option String :=
  binOps.findSome? fun bop => if operationBEq bop.op op then some bop.sym else none

/-! ## Expression syntax helpers -/


private partial def applyPostfix (base : StmtExprMd) (s : PState) : Option (StmtExprMd × PState) :=
  match (token "#").parse s with
  | some ((), s') =>
    match ident.parse s' with
    | some (field, s'') =>
      applyPostfix (wm (.FieldSelect base (mkId field))) s''
    | none => some (base, s)
  | none =>
    match (keyword "is").parse s with
    | some ((), s') =>
      match identNotReserved.parse s' with
      | some (tyName, s'') =>
        applyPostfix (wm (.IsType base (wm (.UserDefined (mkId tyName))))) s''
      | none => some (base, s)
    | none =>
      match (keyword "as").parse s with
      | some ((), s') =>
        match identNotReserved.parse s' with
        | some (tyName, s'') =>
          applyPostfix (wm (.AsType base (wm (.UserDefined (mkId tyName))))) s''
        | none => some (base, s)
      | none => some (base, s)

private partial def parsePrecClimb (postfixRef : Syntax StmtExprMd) (minPrec : Nat) (s : PState) : Option (StmtExprMd × PState) := do
  let (lhs, st) ← postfixRef.parse s
  precLoop postfixRef minPrec lhs st
where
  precLoop (postfixRef : Syntax StmtExprMd) (minPrec : Nat) (lhs : StmtExprMd) (st : PState) : Option (StmtExprMd × PState) :=
    match tryParseBinOp st with
    | some (bop, st') =>
      if bop.prec >= minPrec then
        let nextPrec := if bop.rightAssoc then bop.prec else bop.prec + 1
        match parsePrecClimb postfixRef nextPrec st' with
        | some (rhs, st'') =>
          precLoop postfixRef minPrec (wm (.PrimitiveOp bop.op [lhs, rhs])) st''
        | none => some (lhs, st)
      else some (lhs, st)
    | none =>
      if minPrec == 0 then
        match (token ":=").parse st with
        | some ((), st') =>
          match parsePrecClimb postfixRef 0 st' with
          | some (rhs, st'') =>
            precLoop postfixRef minPrec (wm (.Assign [lhs] rhs)) st''
          | none => some (lhs, st)
        | none => some (lhs, st)
      else some (lhs, st)

private partial def printExpr (postfixRef : Syntax StmtExprMd) (e : StmtExprMd) (minPrec : Nat) : Option String :=
  match e.val with
  | .PrimitiveOp op [lhs, rhs] =>
    match opSym op with
    | some sym => do
      let l ← printExpr postfixRef lhs minPrec
      let r ← printExpr postfixRef rhs minPrec
      some s!"{l}{sym}{r}"
    | none => postfixRef.print e
  | .Assign [target] value => do
    let t ← printExpr postfixRef target 0
    let v ← printExpr postfixRef value 0
    some s!"{t} := {v}"
  | _ => postfixRef.print e

/-! ### Grammar library for mutually recursive expression grammars -/

private partial def mkExprLib (_ : Unit) : GrammarLibrary StmtExprMd :=
  let lib : Unit → GrammarLibrary StmtExprMd := fun () => mkExprLib ()
  let atomRef := ref lib "atom"
  let postfixRef := ref lib "postfix"
  let prec0Ref := ref lib "prec0"
  let typeSyn := highTypeSyntax
  let atomSyntax : Syntax StmtExprMd :=
    alt (map { apply := fun () => some (wm (.LiteralBool true))
               unapply := fun e => match e.val with | .LiteralBool true => some () | _ => none }
          (keyword "true"))
    (alt (map { apply := fun () => some (wm (.LiteralBool false))
                unapply := fun e => match e.val with | .LiteralBool false => some () | _ => none }
           (keyword "false"))
    (alt (map { apply := fun () => some (wm (.Hole true none))
                unapply := fun e => match e.val with | .Hole true none => some () | _ => none }
           (token "<?>"))
    (alt (map { apply := fun () => some (wm (.Hole false none))
                unapply := fun e => match e.val with | .Hole false none => some () | _ => none }
           (token "<??>"))
    (alt (map { apply := fun ((), inner) => some (wm (.PrimitiveOp .Neg [inner]))
                unapply := fun e => match e.val with
                  | .PrimitiveOp .Neg [inner] => some ((), inner) | _ => none }
           (seq (text "-") atomRef))
    (alt (map { apply := fun ((), inner) => some (wm (.PrimitiveOp .Not [inner]))
                unapply := fun e => match e.val with
                  | .PrimitiveOp .Not [inner] => some ((), inner) | _ => none }
           (seq (text "!") atomRef))
    (alt (map { apply := fun ((), v) => some (wm (.Return (some v)))
                unapply := fun e => match e.val with
                  | .Return (some v) => some ((), v) | _ => none }
           (seq (keyword "return") prec0Ref))
    (alt (map { apply := fun ((), cond) => some (wm (.Assert cond))
                unapply := fun e => match e.val with
                  | .Assert cond => some ((), cond) | _ => none }
           (seq (keyword "assert") prec0Ref))
    (alt (map { apply := fun ((), cond) => some (wm (.Assume cond))
                unapply := fun e => match e.val with
                  | .Assume cond => some ((), cond) | _ => none }
           (seq (keyword "assume") prec0Ref))
    (alt (map { apply := fun ((), name) => some (wm (.Exit name))
                unapply := fun e => match e.val with
                  | .Exit name => some ((), name) | _ => none }
           (seq (keyword "exit") ident))
    (alt (map { apply := fun ((((), name), ((), ty)), init) =>
                  some (wm (.LocalVariable (mkId name) ty (init.map Prod.snd)))
                unapply := fun e => match e.val with
                  | .LocalVariable id ty init =>
                    some ((((), id.text), ((), ty)), init.map fun v => ((), v))
                  | _ => none }
           (seq (seq (seq (keyword "var") identNotReserved)
                     (seq (token ":") typeSyn))
                (optional (seq (token ":=") prec0Ref))))
    (alt (map { apply := fun ((), name) => some (wm (.New (mkId name)))
                unapply := fun e => match e.val with
                  | .New id => some ((), id.text) | _ => none }
           (seq (keyword "new") ident))
    (alt (map { apply := fun (((((), cond), ((), thenBr)), elseBr)) =>
                  some (wm (.IfThenElse cond thenBr (elseBr.map Prod.snd)))
                unapply := fun e => match e.val with
                  | .IfThenElse cond thenBr elseBr =>
                    some (((((), cond), ((), thenBr)), elseBr.map fun v => ((), v)))
                  | _ => none }
           (seq (seq (seq (keyword "if") prec0Ref)
                     (seq (keyword "then") prec0Ref))
                (optional (seq (keyword "else") prec0Ref))))
    (alt (map { apply := fun (((((), ((), cond)), ()), invs), body) =>
                  some (wm (.While cond (invs.map Prod.snd) none body))
                unapply := fun e => match e.val with
                  | .While cond invs none body =>
                    some (((((), ((), cond)), ()), invs.map fun v => ((), v)), body)
                  | _ => none }
           (seq (seq (seq (seq (keyword "while") (seq (token "(") prec0Ref))
                          (token ")"))
                     (many (seq (keyword "invariant") prec0Ref)))
                prec0Ref))
    (alt (map { apply := fun ((((((), ((), init)), ((), cond)), ((), step)), ((), invs)), body) =>
                  let whileBody := wm (.Block [body, step] none)
                  let whileStmt := wm (.While cond (invs.map Prod.snd) none whileBody)
                  some (wm (.Block [init, whileStmt] none))
                unapply := fun _ => none }
           (seq (seq (seq (seq (seq (keyword "for") (seq (token "(") prec0Ref))
                               (seq (token ";") prec0Ref))
                          (seq (token ";") prec0Ref))
                     (seq (token ")") (many (seq (keyword "invariant") prec0Ref))))
                prec0Ref))
    (alt (map { apply := fun ((((((), ((), name)), ((), ty)), ()), trigger), body) =>
                  some (wm (.Forall { name := mkId name, type := ty } trigger body))
                unapply := fun e => match e.val with
                  | .Forall param trigger body =>
                    some ((((((), ((), param.name.text)), ((), param.type)), ()),
                      trigger), body)
                  | _ => none }
           (seq (seq (seq (seq (seq (keyword "forall") (seq (token "(") identNotReserved))
                               (seq (token ":") typeSyn))
                          (token ")"))
                     (optional (seqRight (token "{") (seqLeft prec0Ref (token "}")))))
                (seqRight (token "=>") prec0Ref)))
    (alt (map { apply := fun ((((((), ((), name)), ((), ty)), ()), trigger), body) =>
                  some (wm (.Exists { name := mkId name, type := ty } trigger body))
                unapply := fun e => match e.val with
                  | .Exists param trigger body =>
                    some ((((((), ((), param.name.text)), ((), param.type)), ()),
                      trigger), body)
                  | _ => none }
           (seq (seq (seq (seq (seq (keyword "exists") (seq (token "(") identNotReserved))
                               (seq (token ":") typeSyn))
                          (token ")"))
                     (optional (seqRight (token "{") (seqLeft prec0Ref (token "}")))))
                (seqRight (token "=>") prec0Ref)))
    (alt (alt -- labelled block
           (map { apply := fun ((((), stmts), ()), label) =>
                    some (wm (.Block stmts (some label)))
                  unapply := fun e => match e.val with
                    | .Block stmts (some label) => some ((((), stmts), ()), label)
                    | _ => none }
             (seq (seq (seq (token "{") (sepBy prec0Ref (token ";")))
                       (token "}"))
                  identNotReserved))
           -- unlabelled block
           (map { apply := fun (((), stmts), ()) =>
                    some (wm (.Block stmts none))
                  unapply := fun e => match e.val with
                    | .Block stmts none => some (((), stmts), ())
                    | _ => none }
             (seq (seq (token "{") (sepBy prec0Ref (token ";")))
                  (token "}"))))
    (alt (map { apply := fun (((), e), ()) => some e
                unapply := fun e => some (((), e), ()) }
           (seq (seq (token "(") prec0Ref) (token ")")))
    (alt (map { apply := fun ((intPart : Int), (fracPart : Nat)) =>
                  let fracStr := toString fracPart
                  let exp : Int := -(fracStr.length : Int)
                  let mantissa : Int := intPart * (10 ^ fracStr.length : Int) + (fracPart : Int)
                  some (wm (.LiteralDecimal ⟨mantissa, exp⟩))
                unapply := fun e => match e.val with
                  | .LiteralDecimal d =>
                    if d.exponent < 0 then
                      let width := (-d.exponent).natAbs
                      let ne := (10 : Int) ^ width
                      some (d.mantissa / ne, (d.mantissa % ne).natAbs)
                    else none
                  | _ => none }
           decimal)
    (alt (map { apply := fun n => some (wm (.LiteralInt n))
                unapply := fun e => match e.val with
                  | .LiteralInt n => some n | _ => none }
           int)
    (alt (map { apply := fun s => some (wm (.LiteralString s))
                unapply := fun e => match e.val with
                  | .LiteralString s => some s | _ => none }
           stringLit)
    -- call or identifier (must be last)
    { parse := fun s => do
        let (name, s') ← identNotReserved.parse s
        match (token "(").parse s' with
        | some ((), s'') =>
          let (args, s''') ← (sepBy prec0Ref (token ",")).parse s''
          let ((), s4) ← (token ")").parse s'''
          return (wm (.StaticCall (mkId name) args), s4)
        | none =>
          return (wm (.Identifier (mkId name)), s')
      print := fun e => match e.val with
        | .StaticCall callee args => do
          let argsStr ← args.mapM fun a => prec0Ref.print a
          some s!"{callee.text}({String.intercalate ", " argsStr})"
        | .Identifier id => some id.text
        | _ => none }
    )))))))))))))))))))))
  let postfixSyntax : Syntax StmtExprMd :=
    { parse := fun s => do
        let (base, s') ← atomRef.parse s
        applyPostfix base s'
      print := fun e => match e.val with
        | .FieldSelect target field => do
          let tStr ← postfixRef.print target
          some s!"{tStr}#{field.text}"
        | .IsType target ty => do
          let tStr ← postfixRef.print target
          let tyStr ← typeSyn.print ty
          some s!"{tStr} is {tyStr}"
        | .AsType target ty => do
          let tStr ← postfixRef.print target
          let tyStr ← typeSyn.print ty
          some s!"{tStr} as {tyStr}"
        | _ => atomRef.print e }
  let prec0Syntax : Syntax StmtExprMd :=
    { parse := fun s => parsePrecClimb postfixRef 0 s
      print := fun e => printExpr postfixRef e 0 }
  GrammarLibrary.empty
    |>.add "atom" atomSyntax
    |>.add "postfix" postfixSyntax
    |>.add "prec0" prec0Syntax

def grammarLibrary : GrammarLibrary StmtExprMd := mkExprLib ()

private def stmtExprPrec0 : Syntax StmtExprMd := ref (fun () => grammarLibrary) "prec0"

/-! ## Procedure syntax -/

private def requiresClause : Syntax StmtExprMd :=
  seqRight (keyword "requires") stmtExprPrec0

private def ensuresClause : Syntax StmtExprMd :=
  seqRight (keyword "ensures") stmtExprPrec0

private def modifiesClause : Syntax (List StmtExprMd) :=
  seqRight (keyword "modifies") (sepBy1 stmtExprPrec0 (token ","))

private def invokeOnClause : Syntax StmtExprMd :=
  seqRight (keyword "invokeOn") stmtExprPrec0

private def returnType : Syntax HighTypeMd :=
  seqRight (token ":") highTypeSyntax

private def returnParameters : Syntax (List Parameter) :=
  seqRight (keyword "returns")
    (seqRight (token "(")
      (seqLeft parameterList (token ")")))

private def bodyExternalSyntax : Syntax (Option StmtExprMd × Bool) :=
  alt
    (map { apply := fun () => some (none, true)
           unapply := fun | (none, true) => some () | _ => none }
      (keyword "external"))
    (map { apply := fun e => some (some e, false)
           unapply := fun | (some e, false) => some e | _ => none }
      stmtExprPrec0)

private def procedureSyntax (isFunctional : Bool) : Syntax Procedure :=
  { parse := fun s => do
      let kw := if isFunctional then "function" else "procedure"
      let ((), s) ← (keyword kw).parse s
      let (name, s) ← identNotReserved.parse s
      let ((), s) ← (token "(").parse s
      let (params, s) ← parameterList.parse s
      let ((), s) ← (token ")").parse s
      -- Optional return type
      let (retType, s) ← (optional returnType).parse s
      -- Optional return parameters
      let (retParams, s) ← (optional returnParameters).parse s
      -- Requires clauses
      let (reqs, s) ← (many requiresClause).parse s
      -- Optional invokeOn
      let (invokeOn, s) ← (optional invokeOnClause).parse s
      -- Ensures clauses
      let (enss, s) ← (many ensuresClause).parse s
      -- Modifies clauses
      let (mods, s) ← (many modifiesClause).parse s
      let allMods := mods.flatten
      -- Optional body or external
      let (bodyOpt, s) ← (optional bodyExternalSyntax).parse s
      -- Trailing semicolon
      let ((), s) ← (token ";").parse s
      let outputs := match retType with
        | some ty => [{ name := mkId "result", type := ty : Parameter }]
        | none => match retParams with
          | some ps => ps
          | none => []
      let body := match bodyOpt with
        | some (_, true) => Body.External
        | some (some e, false) =>
          if enss.isEmpty then Body.Transparent e
          else Body.Opaque enss (some e) allMods
        | some (none, _) => Body.Opaque enss none allMods
        | none =>
          if enss.isEmpty then Body.Opaque [] none allMods
          else Body.Opaque enss none allMods
      return ({ name := mkId name
                inputs := params
                outputs := outputs
                preconditions := reqs
                decreases := none
                isFunctional := isFunctional
                invokeOn := invokeOn
                body := body
                md := emptyMd }, s)
    print := fun proc => do
      let kw := if proc.isFunctional then "function" else "procedure"
      let paramsStr ← proc.inputs.mapM fun p => do
        let tyStr ← highTypeSyntax.print p.type
        some s!"{p.name.text}: {tyStr}"
      let mut result := s!"{kw} {proc.name.text}({String.intercalate ", " paramsStr})"
      -- Return type
      match proc.outputs with
      | [out] =>
        if out.name.text == "result" then
          let tyStr ← highTypeSyntax.print out.type
          result := result ++ s!": {tyStr}"
      | _ =>
        if !proc.outputs.isEmpty then
          let outStrs ← proc.outputs.mapM fun p => do
            let tyStr ← highTypeSyntax.print p.type
            some s!"{p.name.text}: {tyStr}"
          result := result ++ s!" returns ({String.intercalate ", " outStrs})"
      -- Requires
      for req in proc.preconditions do
        let reqStr ← stmtExprPrec0.print req
        result := result ++ s!"\nrequires {reqStr}"
      -- InvokeOn
      if let some inv := proc.invokeOn then
        let invStr ← stmtExprPrec0.print inv
        result := result ++ s!"\ninvokeOn {invStr}"
      -- Body
      match proc.body with
      | .Transparent body =>
        let bodyStr ← stmtExprPrec0.print body
        result := result ++ s!"\n{bodyStr};"
      | .Opaque posts impl mods =>
        for ens in posts do
          let ensStr ← stmtExprPrec0.print ens
          result := result ++ s!"\nensures {ensStr}"
        for m in mods do
          let mStr ← stmtExprPrec0.print m
          result := result ++ s!"\nmodifies {mStr}"
        if let some body := impl then
          let bodyStr ← stmtExprPrec0.print body
          result := result ++ s!"\n{bodyStr};"
        else
          result := result ++ ";"
      | .External => result := result ++ "\nexternal;"
      | .Abstract posts =>
        for ens in posts do
          let ensStr ← stmtExprPrec0.print ens
          result := result ++ s!"\nensures {ensStr}"
        result := result ++ ";"
      some result }


/-! ## Composite type syntax -/

private def fieldSyntax : Syntax Field :=
  alt mutableFieldSyntax immutableFieldSyntax
where
  mutableFieldSyntax : Syntax Field :=
    map { apply := fun (((), name), ((), ty)) =>
            some { name := mkId name, isMutable := true, type := ty }
          unapply := fun f =>
            if f.isMutable then some (((), f.name.text), ((), f.type))
            else none }
      (seq (seq (keyword "var") identNotReserved) (seq (token ":") highTypeSyntax))
  immutableFieldSyntax : Syntax Field :=
    map { apply := fun (name, ((), ty)) =>
            some { name := mkId name, isMutable := false, type := ty }
          unapply := fun f =>
            if !f.isMutable then some (f.name.text, ((), f.type))
            else none }
      (seq identNotReserved (seq (token ":") highTypeSyntax))

private def compositeSyntax : Syntax TypeDefinition :=
  { parse := fun s => do
      let ((), s) ← (keyword "composite").parse s
      let (name, s) ← identNotReserved.parse s
      -- Optional extends
      let (ext, s) ← (optional (seqRight (keyword "extends")
        (sepBy1 identNotReserved (token ",")))).parse s
      let ((), s) ← (token "{").parse s
      let (fields, s) ← (many fieldSyntax).parse s
      let (procs, s) ← (many (alt (procedureSyntax false) (procedureSyntax true))).parse s
      let ((), s) ← (token "}").parse s
      let extending := (ext.getD []).map mkId
      return (.Composite { name := mkId name
                           extending := extending
                           fields := fields
                           instanceProcedures := procs }, s)
    print := fun td => match td with
      | .Composite ct => do
        let mut result := s!"composite {ct.name.text}"
        if !ct.extending.isEmpty then
          result := result ++ s!" extends {String.intercalate ", " (ct.extending.map (·.text))}"
        result := result ++ " {"
        for f in ct.fields do
          let tyStr ← highTypeSyntax.print f.type
          if f.isMutable then
            result := result ++ s!"\n  var {f.name.text}: {tyStr}"
          else
            result := result ++ s!"\n  {f.name.text}: {tyStr}"
        for p in ct.instanceProcedures do
          let pStr ← (if p.isFunctional then procedureSyntax true else procedureSyntax false).print p
          result := result ++ s!"\n  {pStr}"
        result := result ++ "\n}"
        some result
      | _ => none }

/-! ## Constrained type syntax -/

private def constrainedTypeSyntax : Syntax TypeDefinition :=
  { parse := fun s => do
      let ((), s) ← (keyword "constrained").parse s
      let (name, s) ← identNotReserved.parse s
      let ((), s) ← (token "=").parse s
      let (valueName, s) ← identNotReserved.parse s
      let ((), s) ← (token ":").parse s
      let (base, s) ← highTypeSyntax.parse s
      let ((), s) ← (keyword "where").parse s
      let (constraint, s) ← stmtExprPrec0.parse s
      let ((), s) ← (keyword "witness").parse s
      let (witness, s) ← stmtExprPrec0.parse s
      return (.Constrained { name := mkId name
                             base := base
                             valueName := mkId valueName
                             constraint := constraint
                             witness := witness }, s)
    print := fun td => match td with
      | .Constrained ct => do
        let baseStr ← highTypeSyntax.print ct.base
        let conStr ← stmtExprPrec0.print ct.constraint
        let witStr ← stmtExprPrec0.print ct.witness
        some s!"constrained {ct.name.text} = {ct.valueName.text}: {baseStr} where {conStr} witness {witStr}"
      | _ => none }

/-! ## Datatype syntax -/

private def datatypeConstructorSyntax : Syntax DatatypeConstructor :=
  { parse := fun s => do
      let (name, s) ← identNotReserved.parse s
      match (token "(").parse s with
      | some ((), s') =>
        let (args, s'') ← (sepBy parameterSyntax (token ",")).parse s'
        let ((), s''') ← (token ")").parse s''
        return ({ name := mkId name, args := args }, s''')
      | none =>
        return ({ name := mkId name, args := [] }, s)
    print := fun c => do
      if c.args.isEmpty then
        some c.name.text
      else
        let argsStr ← c.args.mapM fun p => do
          let tyStr ← highTypeSyntax.print p.type
          some s!"{p.name.text}: {tyStr}"
        some s!"{c.name.text}({String.intercalate ", " argsStr})" }

private def datatypeSyntax : Syntax TypeDefinition :=
  { parse := fun s => do
      let ((), s) ← (keyword "datatype").parse s
      let (name, s) ← identNotReserved.parse s
      let ((), s) ← (token "{").parse s
      let (ctors, s) ← (sepBy datatypeConstructorSyntax (token ",")).parse s
      let ((), s) ← (token "}").parse s
      return (.Datatype { name := mkId name
                          typeArgs := []
                          constructors := ctors }, s)
    print := fun td => match td with
      | .Datatype dt => do
        let ctorStrs ← dt.constructors.mapM datatypeConstructorSyntax.print
        some s!"datatype {dt.name.text} \{{String.intercalate ", " ctorStrs}}"
      | _ => none }

/-! ## Top-level program syntax -/

private def topLevelItem : Syntax (Option Procedure × Option TypeDefinition) :=
  alt
    (map { apply := fun p => some (some p, none)
           unapply := fun | (some p, none) => some p | _ => none }
      (alt (procedureSyntax false) (procedureSyntax true)))
  (alt
    (map { apply := fun td => some (none, some td)
           unapply := fun | (none, some td) => some td | _ => none }
      compositeSyntax)
  (alt
    (map { apply := fun td => some (none, some td)
           unapply := fun | (none, some td) => some td | _ => none }
      constrainedTypeSyntax)
    (map { apply := fun td => some (none, some td)
           unapply := fun | (none, some td) => some td | _ => none }
      datatypeSyntax)))

def programSyntax : Syntax Program :=
  { parse := fun s => do
      let ((), s) ← skipWsAndComments.parse s
      let (items, s) ← (many topLevelItem).parse s
      let mut procs : List Procedure := []
      let mut types : List TypeDefinition := []
      for (procOpt, typeOpt) in items do
        if let some p := procOpt then procs := procs ++ [p]
        if let some t := typeOpt then types := types ++ [t]
      return ({ staticProcedures := procs
                staticFields := []
                types := types }, s)
    print := fun prog => do
      let mut parts : List String := []
      for td in prog.types do
        match td with
        | .Composite _ => parts := parts ++ [← compositeSyntax.print td]
        | .Constrained _ => parts := parts ++ [← constrainedTypeSyntax.print td]
        | .Datatype _ => parts := parts ++ [← datatypeSyntax.print td]
      for proc in prog.staticProcedures do
        let syn := if proc.isFunctional then procedureSyntax true else procedureSyntax false
        parts := parts ++ [← syn.print proc]
      some (String.intercalate "\n\n" parts) }

/-! ## Public API -/

/-- Parse a Laurel source string into a `Laurel.Program`. -/
def parseLaurelString (input : String) : Option Program :=
  runParse programSyntax input

/-- Pretty-print a `Laurel.Program` back to a string. -/
def printLaurelProgram (prog : Program) : Option String :=
  runPrint programSyntax prog

end CombinatorGrammar
end Strata.Laurel
