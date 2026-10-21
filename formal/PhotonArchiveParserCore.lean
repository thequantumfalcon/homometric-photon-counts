import Mathlib.Data.Rat.Defs

namespace PhotonArchiveParser

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 1024

abbrev Coeff := ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ
abbrev Phase := Coeff × Coeff

instance coeffDecidableEq : DecidableEq Coeff := inferInstance
instance phaseDecidableEq : DecidableEq Phase := inferInstance

def ws (xs : List Char) : List Char := xs.dropWhile Char.isWhitespace

def token (s : String) (xs : List Char) : Option (List Char) :=
  let ys := ws xs
  if ys.take s.length = s.toList then some (ys.drop s.length) else none

def quoted : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '"' :: rest, acc => some (acc.reverse, rest)
  | c :: rest, acc =>
      if c == '\\' || c.toNat < 32 then none else quoted rest (c :: acc)

def digits : Nat → List Char → Option Nat
  | n, [] => some n
  | n, c :: cs =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        digits (10 * n + c.toNat - 48) cs
      else none

def natural (xs : List Char) : Option Nat :=
  if xs = [] then none else digits 0 xs

def integer (xs : List Char) : Option Int := do
  match xs with
  | '-' :: rest => return -(← natural rest : Int)
  | _ => return (← natural xs : Int)

def rationalChars (xs : List Char) : Option ℚ := do
  let n ← integer (xs.takeWhile (· != '/'))
  match xs.dropWhile (· != '/') with
  | [] => return (n : ℚ)
  | '/' :: den =>
      let d ← natural den
      if d = 0 then none else some ((n : ℚ) / (d : ℚ))
  | _ => none

def readRat (xs : List Char) : Option (ℚ × List Char) := do
  let rest ← token "\"" xs
  let (s, tail) ← quoted rest []
  let value ← rationalChars s
  return (value, tail)

def readCoeff (xs : List Char) : Option (Coeff × List Char) := do
  let xs ← token "[" xs
  let (a, xs) ← readRat xs
  let xs ← token "," xs
  let (b, xs) ← readRat xs
  let xs ← token "," xs
  let (c, xs) ← readRat xs
  let xs ← token "," xs
  let (d, xs) ← readRat xs
  let xs ← token "," xs
  let (e, xs) ← readRat xs
  let xs ← token "," xs
  let (f, xs) ← readRat xs
  let xs ← token "," xs
  let (g, xs) ← readRat xs
  let xs ← token "," xs
  let (h, xs) ← readRat xs
  let xs ← token "]" xs
  return ((a, b, c, d, e, f, g, h), xs)

def readPhase (xs : List Char) : Option (Phase × List Char) := do
  let xs ← token "{" xs
  let xs ← token "\"re\"" xs
  let xs ← token ":" xs
  let (re, xs) ← readCoeff xs
  let xs ← token "," xs
  let xs ← token "\"im\"" xs
  let xs ← token ":" xs
  let (im, xs) ← readCoeff xs
  let xs ← token "}" xs
  return ((re, im), xs)

def readPhases : Nat → List Char → Option (List Phase × List Char)
  | 0, _ => none
  | fuel + 1, xs => do
      let (p, xs) ← readPhase xs
      match ws xs with
      | ',' :: rest =>
          let (ps, tail) ← readPhases fuel rest
          return (p :: ps, tail)
      | ']' :: rest => return ([p], rest)
      | _ => none

def parse (input : List Char) : Option (List Phase) := do
  let xs ← token "[" input
  match ws xs with
  | ']' :: tail => if ws tail = [] then some [] else none
  | _ =>
      let (ps, tail) ← readPhases 64 xs
      if ws tail = [] then some ps else none

theorem rational_probe : rationalChars "-1/10".toList = some ((-1 : ℚ) / 10) := by decide +kernel
theorem zero_denominator_rejected : rationalChars "1/0".toList = none := by decide
theorem trailing_input_rejected : parse "[] trailing".toList = none := by decide

#print axioms rational_probe
#print axioms zero_denominator_rejected
#print axioms trailing_input_rejected

end PhotonArchiveParser
