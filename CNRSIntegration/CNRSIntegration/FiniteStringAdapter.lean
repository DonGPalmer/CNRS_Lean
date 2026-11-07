import CNRSIntegration.AdditionBridge
import Mathlib.Tactic

/-!
CNRS-R1 working proof adapter for public Lean v1.0.3.
No change to any adopted theorem or to the private E2 source.
-/

open Zsqrtd

namespace CNRSIntegration

structure FiniteSpelling where
  integer : List (Fin 5)
  fraction : List (Fin 5)
  deriving Repr, DecidableEq

def digitOfChar (c : Char) : Option (Fin 5) :=
  if c == '0' then some 0 else
  if c == '1' then some 1 else
  if c == '2' then some 2 else
  if c == '3' then some 3 else
  if c == '4' then some 4 else none

def decodeDigits : List Char → Option (List (Fin 5))
  | [] => some []
  | c :: cs => do
      let digit ← digitOfChar c
      let tail ← decodeDigits cs
      some (digit :: tail)

/-- The grammar is a nonempty sequence of 0..4 digits, optionally with
    one radix point; one side of the radix may be empty but not both. -/
def parseFinite (s : String) : Option FiniteSpelling :=
  match s.splitOn "." with
  | [whole] =>
      if whole.isEmpty then none else do
        let i ← decodeDigits whole.toList
        some ⟨i, []⟩
  | [whole, frac] =>
      if whole.isEmpty && frac.isEmpty then none else do
        let i ← decodeDigits whole.toList
        let f ← decodeDigits frac.toList
        some ⟨i, f⟩
  | _ => none

theorem parse_examples :
    parseFinite "1" = some ⟨[1], []⟩ ∧
    parseFinite "01" = some ⟨[0, 1], []⟩ ∧
    parseFinite ".1" = some ⟨[], [1]⟩ ∧
    parseFinite "1." = some ⟨[1], []⟩ ∧
    parseFinite "." = none ∧
    parseFinite "1..2" = none ∧
    parseFinite "5" = none ∧
    parseFinite "-1" = none := by
  decide

/-- Numerator digit word, in the least-significant-digit-first order. -/
def spellingWord (s : FiniteSpelling) : List (Fin 5) :=
  s.fraction.reverse ++ s.integer.reverse

/-- Exact Gaussian-rational value, with the fractional offset as denominator. -/
noncomputable def spellingValue (s : FiniteSpelling) : CnrsQ2.GaussianFrac :=
  CnrsQ2.evalFiniteLaurent s.fraction.length (spellingWord s)

/-- Align a spelling to a common number of fractional digits. -/
def padWord (s : FiniteSpelling) (depth : ℕ) : List (Fin 5) :=
  List.replicate (depth - s.fraction.length) 0 ++ spellingWord s

/-- Addition of aligned finite words remains correct at an arbitrary
    shared fractional depth, not just the zero-offset integer case. -/
theorem addWord_at_depth (depth : ℕ) (xs ys : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent depth (CNRSArithmetic.addWords xs ys) =
      CnrsQ2.evalFiniteLaurent depth xs +
      CnrsQ2.evalFiniteLaurent depth ys := by
  unfold CnrsQ2.evalFiniteLaurent
  change
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue (CNRSArithmetic.addWords xs ys))) /
       CnrsQ2.betaFrac ^ depth =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue xs)) / CnrsQ2.betaFrac ^ depth +
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue ys)) / CnrsQ2.betaFrac ^ depth
  rw [CNRSArithmetic.addWords_correct, map_add, add_div]

theorem addPadded_correct (a b : FiniteSpelling) :
    let depth := max a.fraction.length b.fraction.length
    CnrsQ2.evalFiniteLaurent depth
        (CNRSArithmetic.addWords (padWord a depth) (padWord b depth)) =
      CnrsQ2.evalFiniteLaurent depth (padWord a depth) +
      CnrsQ2.evalFiniteLaurent depth (padWord b depth) := by
  exact addWord_at_depth _ _ _

/-- Zero prefixes have no numerical value as finite words. -/
theorem zeroWord_value (n : ℕ) :
    CNRSArithmetic.wordValue (List.replicate n (0 : Fin 5)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [CNRSArithmetic.wordValue, ih]

/-- Padding inserts low zero digits and multiplies the raw numerator
    by the corresponding power of the Gaussian base. -/
theorem padWord_factor (s : FiniteSpelling) (depth : ℕ) :
    CNRSArithmetic.wordValue (padWord s depth) =
      beta ^ (depth - s.fraction.length) *
        CNRSArithmetic.wordValue (spellingWord s) := by
  simp [padWord, CNRSCore.wordValue_append, zeroWord_value]

end CNRSIntegration
