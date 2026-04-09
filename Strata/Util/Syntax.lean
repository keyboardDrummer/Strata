/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Bidirectional Syntax Combinators

A library of syntax descriptions that can be used both for parsing and
pretty-printing, following the approach of Rendel & Ostermann (2010):
"Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing".
-/

namespace Strata.Syntax

public section

structure Iso (a b : Type) where
  apply : a → Option b
  unapply : b → Option a

def Iso.inverse (i : Iso a b) : Iso b a :=
  { apply := i.unapply, unapply := i.apply }

abbrev Pos := Nat

structure PState where
  input : String
  pos : Pos

/-- Get the remaining input as a plain String. -/
private def PState.rest (s : PState) : String :=
  (s.input.drop s.pos).toString

structure Syntax (a : Type) where
  parse : PState → Option (a × PState)
  print : a → Option String

def pure : Syntax Unit :=
  { parse := fun s => some ((), s)
    print := fun () => some "" }

def seq (s1 : Syntax a) (s2 : Syntax b) : Syntax (a × b) :=
  { parse := fun s => do
      let (v1, s') ← s1.parse s
      let (v2, s'') ← s2.parse s'
      return ((v1, v2), s'')
    print := fun (v1, v2) => do
      let t1 ← s1.print v1
      let t2 ← s2.print v2
      return t1 ++ t2 }

def map (iso : Iso a b) (s : Syntax a) : Syntax b :=
  { parse := fun st => do
      let (v, st') ← s.parse st
      let w ← iso.apply v
      return (w, st')
    print := fun w => do
      let v ← iso.unapply w
      s.print v }

def alt (s1 : Syntax a) (s2 : Syntax a) : Syntax a :=
  { parse := fun s => s1.parse s |>.orElse (fun () => s2.parse s)
    print := fun v => s1.print v |>.orElse (fun () => s2.print v) }

def text (t : String) : Syntax Unit :=
  { parse := fun s =>
      if s.rest.startsWith t then
        some ((), { s with pos := s.pos + t.length })
      else
        none
    print := fun () => some t }

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def countLeadingWs (s : String) : Nat :=
  let chars := s.toList
  chars.takeWhile isWs |>.length

def skipWs : Syntax Unit :=
  { parse := fun s =>
      let rest := s.rest
      let consumed := countLeadingWs rest
      some ((), { s with pos := s.pos + consumed })
    print := fun () => some "" }

/-- Skip whitespace and line comments starting with `//`. -/
def skipWsAndComments : Syntax Unit :=
  { parse := fun s =>
      let rec loop (pos : Pos) (fuel : Nat) : Pos :=
        match fuel with
        | 0 => pos
        | fuel + 1 =>
          let rest := (s.input.drop pos).toString
          let wsCount := countLeadingWs rest
          let pos' := pos + wsCount
          let rest' := (s.input.drop pos').toString
          if rest'.startsWith "//" then
            let afterSlashes := (rest'.drop 2).toString
            let lineChars := afterSlashes.toList.takeWhile (· != '\n')
            let skip := 2 + lineChars.length
            let pos'' := pos' + skip
            let rest'' := (s.input.drop pos'').toString
            if rest''.startsWith "\n" then loop (pos'' + 1) fuel
            else loop pos'' fuel
          else pos'
      some ((), { s with pos := loop s.pos (s.input.length - s.pos + 1) })
    print := fun () => some "" }

def keyword (t : String) : Syntax Unit :=
  map { apply := fun (((), ()), ()) => some ()
        unapply := fun () => some (((), ()), ()) }
    (seq (seq skipWsAndComments (text t)) skipWsAndComments)

def token (t : String) : Syntax Unit :=
  map { apply := fun ((), ()) => some ()
        unapply := fun () => some ((), ()) }
    (seq skipWsAndComments (text t))

private def isDigit (c : Char) : Bool := c >= '0' && c <= '9'
private def isAlpha (c : Char) : Bool := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
private def isIdentStart (c : Char) : Bool := isAlpha c || c == '_'
private def isIdentChar (c : Char) : Bool := isAlpha c || isDigit c || c == '_'

def nat : Syntax Nat :=
  { parse := fun s =>
      let rest := s.rest
      let digits := rest.toList.takeWhile isDigit
      if digits.isEmpty then none
      else
        let digitStr := String.ofList digits
        match digitStr.toNat? with
        | some n => some (n, { s with pos := s.pos + digits.length })
        | none => none
    print := fun n => some (toString n) }

def int : Syntax Int :=
  { parse := fun s =>
      let rest := s.rest
      let (neg, numStart) :=
        if rest.startsWith "-" then (true, s.pos + 1)
        else (false, s.pos)
      let numRest := (s.input.drop numStart).toString
      let digits := numRest.toList.takeWhile isDigit
      if digits.isEmpty then none
      else
        let digitStr := String.ofList digits
        match digitStr.toNat? with
        | some n =>
          let v : Int := if neg then -n else n
          some (v, { s with pos := numStart + digits.length })
        | none => none
    print := fun i => some (toString i) }

def decimal : Syntax (Int × Nat) :=
  { parse := fun s =>
      let rest := s.rest
      let (neg, numStart) :=
        if rest.startsWith "-" then (true, s.pos + 1)
        else (false, s.pos)
      let numRest := (s.input.drop numStart).toString
      let intChars := numRest.toList.takeWhile isDigit
      if intChars.isEmpty then none
      else
        let afterInt := numStart + intChars.length
        let afterDot := (s.input.drop afterInt).toString
        if afterDot.startsWith "." then
          let fracRest := (s.input.drop (afterInt + 1)).toString
          let fracChars := fracRest.toList.takeWhile isDigit
          if fracChars.isEmpty then none
          else
            let intStr := String.ofList intChars
            let fracStr := String.ofList fracChars
            match intStr.toNat?, fracStr.toNat? with
            | some intPart, some fracPart =>
              let wholePart : Int := if neg then -(intPart : Int) else intPart
              some ((wholePart, fracPart), { s with pos := afterInt + 1 + fracChars.length })
            | _, _ => none
        else none
    print := fun (intPart, fracPart) =>
      some s!"{intPart}.{fracPart}" }

def ident : Syntax String :=
  { parse := fun s =>
      let rest := s.rest
      let wsCount := countLeadingWs rest
      let trimmed := (rest.drop wsCount).toString
      if trimmed.isEmpty then none
      else
        let chars := trimmed.toList
        match chars with
        | first :: _ =>
          if isIdentStart first then
            let nameChars := chars.takeWhile isIdentChar
            some (String.ofList nameChars, { s with pos := s.pos + wsCount + nameChars.length })
          else none
        | [] => none
    print := fun name => some name }

def stringLit : Syntax String :=
  { parse := fun s =>
      let rest := s.rest
      if rest.startsWith "\"" then
        let inner := (rest.drop 1).toString
        let contentChars := inner.toList.takeWhile (· != '"')
        let afterContent := (inner.drop contentChars.length).toString
        if afterContent.startsWith "\"" then
          some (String.ofList contentChars, { s with pos := s.pos + 1 + contentChars.length + 1 })
        else none
      else none
    print := fun str => some s!"\"{str}\"" }

partial def many (s : Syntax a) : Syntax (List a) :=
  { parse := fun st =>
      let rec loop (st : PState) (acc : List a) : List a × PState :=
        match s.parse st with
        | some (v, st') =>
          if st'.pos > st.pos then loop st' (acc ++ [v])
          else (acc, st)
        | none => (acc, st)
      some (loop st [])
    print := fun vs => do
      let strs ← vs.mapM s.print
      return String.join strs }

partial def sepBy1 (item : Syntax a) (sep : Syntax Unit) : Syntax (List a) :=
  { parse := fun st => do
      let (first, st') ← item.parse st
      let rec loop (st : PState) (acc : List a) : List a × PState :=
        match sep.parse st with
        | some ((), st'') =>
          match item.parse st'' with
          | some (v, st''') =>
            if st'''.pos > st.pos then loop st''' (acc ++ [v])
            else (acc, st)
          | none => (acc, st)
        | none => (acc, st)
      let (rest, st'') := loop st' []
      return (first :: rest, st'')
    print := fun vs => match vs with
      | [] => none
      | [x] => item.print x
      | x :: xs => do
        let first ← item.print x
        let rest ← xs.mapM fun v => do
          let s ← sep.print ()
          let t ← item.print v
          return s ++ t
        return first ++ String.join rest }

def sepBy (item : Syntax a) (sep : Syntax Unit) : Syntax (List a) :=
  alt (sepBy1 item sep)
    (map { apply := fun () => some [], unapply := fun | [] => some () | _ => none } pure)

def optional (s : Syntax a) : Syntax (Option a) :=
  alt
    (map { apply := fun v => some (some v), unapply := fun | some v => some v | none => none } s)
    (map { apply := fun () => some none, unapply := fun | none => some () | some _ => none } pure)

def seqLeft (s1 : Syntax a) (s2 : Syntax Unit) : Syntax a :=
  map { apply := fun (v, ()) => some v
        unapply := fun v => some (v, ()) }
    (seq s1 s2)

def seqRight (s1 : Syntax Unit) (s2 : Syntax a) : Syntax a :=
  map { apply := fun ((), v) => some v
        unapply := fun v => some ((), v) }
    (seq s1 s2)

def runParse (s : Syntax a) (input : String) : Option a := do
  let (v, st) ← s.parse { input := input, pos := 0 }
  let rest := (input.drop st.pos).toString
  let trimmed := rest.toList.dropWhile isWs
  if trimmed.isEmpty then some v
  else none

def runPrint (s : Syntax a) (v : a) : Option String :=
  s.print v

end
end Strata.Syntax
