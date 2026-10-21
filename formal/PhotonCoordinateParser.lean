import PhotonArchiveParserCore

namespace PhotonCoordinateInput

open PhotonArchiveParser

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Integer base, offset kind (0=none, 1=theta, 2=phi), and signed offset. -/
abbrev Record := Nat × Nat × Int

def digit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

def readNat (input : List Char) : Option (Nat × List Char) := do
  let xs := ws input
  let n ← natural (xs.takeWhile digit)
  return (n, xs.dropWhile digit)

def readInt (input : List Char) : Option (Int × List Char) := do
  match ws input with
  | '-' :: xs =>
      let n ← natural (xs.takeWhile digit)
      return (-(n : Int), xs.dropWhile digit)
  | xs =>
      let (n, tail) ← readNat xs
      return ((n : Int), tail)

def readString (xs : List Char) : Option (List Char × List Char) := do
  let xs ← token "\"" xs
  quoted xs []

/-- Decimal display text is consumed as text, not interpreted as an exact real. -/
def readRecord (xs : List Char) : Option (Record × List Char) := do
  let xs ← token "{" xs
  let xs ← token "\"ordinal\"" xs
  let xs ← token ":" xs
  let (_, xs) ← readNat xs
  let xs ← token "," xs
  let xs ← token "\"coordinate_decimal\"" xs
  let xs ← token ":" xs
  let (_, xs) ← readString xs
  let xs ← token "," xs
  let xs ← token "\"base_integer\"" xs
  let xs ← token ":" xs
  let (base, xs) ← readNat xs
  let xs ← token "," xs
  let xs ← token "\"offset_kind\"" xs
  let xs ← token ":" xs
  let (kind, xs) ← readString xs
  let k ← if kind = "none".toList then some 0 else
    if kind = "theta".toList then some 1 else
    if kind = "phi".toList then some 2 else none
  let xs ← token "," xs
  let xs ← token "\"offset_sign\"" xs
  let xs ← token ":" xs
  let (sign, xs) ← readInt xs
  let xs ← token "}" xs
  if (k = 0 ∧ sign = 0) ∨ (k ≠ 0 ∧ (sign = 1 ∨ sign = -1)) then
    return ((base, k, sign), xs)
  else none

def readRecords : Nat → List Char → Option (List Record × List Char)
  | 0, _ => none
  | fuel + 1, xs => do
      let (p, xs) ← readRecord xs
      match ws xs with
      | ',' :: rest =>
          let (ps, tail) ← readRecords fuel rest
          return (p :: ps, tail)
      | ']' :: rest => return ([p], rest)
      | _ => none

def parseCoordinates (input : List Char) : Option (List Record) := do
  let xs ← token "[" input
  match ws xs with
  | ']' :: tail => if ws tail = [] then some [] else none
  | _ =>
      let (ps, tail) ← readRecords 64 xs
      if ws tail = [] then some ps else none

theorem trailing_input_rejected : parseCoordinates "[] trailing".toList = none := by decide
theorem negative_sign_parsed : readInt "-1,".toList = some (-1, [',']) := by decide
theorem separated_sign_rejected : readInt "- 1,".toList = none := by decide

#print axioms trailing_input_rejected
#print axioms negative_sign_parsed
#print axioms separated_sign_rejected

end PhotonCoordinateInput
