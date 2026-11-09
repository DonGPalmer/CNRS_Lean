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
  native_decide

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
  | succ n ih => simp [List.replicate_succ, ih]

/-- Padding inserts low zero digits and multiplies the raw numerator
    by the corresponding power of the Gaussian base. -/
theorem padWord_factor (s : FiniteSpelling) (depth : ℕ) :
    CNRSArithmetic.wordValue (padWord s depth) =
      CNRSCore.beta ^ (depth - s.fraction.length) *
        CNRSArithmetic.wordValue (spellingWord s) := by
  simp [padWord, CNRSCore.wordValue_append, zeroWord_value]


/-- The base is nonzero in the exact Gaussian fraction field, proved
    from its established nonzero five-adic norm. -/
theorem betaFrac_ne_zero : CnrsQ2.betaFrac ≠ 0 := by
  intro h
  have hn : ‖CnrsQ2.fracToPadic CnrsQ2.betaFrac‖ = (5 : ℝ)⁻¹ := by
    simpa [CnrsQ2.betaFrac] using CnrsQ2.norm_fracToPadic_beta
  rw [h, map_zero] at hn
  norm_num at hn

/-- Fractional right-padding is exactly value-preserving in R_A. -/
theorem padWord_value (s : FiniteSpelling) (depth : ℕ)
    (h : s.fraction.length ≤ depth) :
    CnrsQ2.evalFiniteLaurent depth (padWord s depth) = spellingValue s := by
  have hk : depth - s.fraction.length + s.fraction.length = depth :=
    Nat.sub_add_cancel h
  unfold spellingValue CnrsQ2.evalFiniteLaurent
  change
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue (padWord s depth))) / CnrsQ2.betaFrac ^ depth =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue (spellingWord s))) / CnrsQ2.betaFrac ^ s.fraction.length
  rw [padWord_factor, map_mul, map_pow]
  change
    CnrsQ2.betaFrac ^ (depth - s.fraction.length) *
      (algebraMap GaussianInt CnrsQ2.GaussianFrac
         (CNRSArithmetic.wordValue (spellingWord s))) / CnrsQ2.betaFrac ^ depth =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
       (CNRSArithmetic.wordValue (spellingWord s))) / CnrsQ2.betaFrac ^ s.fraction.length
  have hpow : CnrsQ2.betaFrac ^ depth =
    CnrsQ2.betaFrac ^ (depth - s.fraction.length) *
      CnrsQ2.betaFrac ^ s.fraction.length := by
    simpa only [hk] using (pow_add CnrsQ2.betaFrac (depth - s.fraction.length) s.fraction.length)
  rw [hpow]
  field_simp [betaFrac_ne_zero] <;> ring

/-- Composed, exact correctness theorem for accepted, typed CNRS strings,
    including mixed lengths and all finite fractional offsets. -/
theorem addFiniteStrings_value (a b : FiniteSpelling) :
    let depth := max a.fraction.length b.fraction.length
    CnrsQ2.evalFiniteLaurent depth
        (CNRSArithmetic.addWords (padWord a depth) (padWord b depth)) =
      spellingValue a + spellingValue b := by
  dsimp
  rw [addWord_at_depth,
      padWord_value a _ (le_max_left _ _),
      padWord_value b _ (le_max_right _ _)]

/-- Leading integer zeros are value-neutral. -/
theorem append_high_zero_value (xs : List (Fin 5)) :
    CNRSArithmetic.wordValue (xs ++ [0]) = CNRSArithmetic.wordValue xs := by
  simp [CNRSCore.wordValue_append]

/-- Removing one fractional trailing zero and its denominator beta factor
    is value-preserving, so repeated normalization is sound by induction. -/
theorem drop_fraction_zero_value (depth : ℕ) (xs : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent (depth + 1) (0 :: xs) =
      CnrsQ2.evalFiniteLaurent depth xs := by
  unfold CnrsQ2.evalFiniteLaurent
  change
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
      (CNRSArithmetic.wordValue (0 :: xs))) / CnrsQ2.betaFrac ^ (depth + 1) =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
      (CNRSArithmetic.wordValue xs)) / CnrsQ2.betaFrac ^ depth
  simp only [CNRSCore.wordValue_cons, CNRSCore.digit_zero, zero_add, map_mul,
    pow_succ]
  change
    CnrsQ2.betaFrac *
      (algebraMap GaussianInt CnrsQ2.GaussianFrac (CNRSArithmetic.wordValue xs)) /
      (CnrsQ2.betaFrac ^ depth * CnrsQ2.betaFrac) =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac (CNRSArithmetic.wordValue xs)) /
      CnrsQ2.betaFrac ^ depth
  field_simp [betaFrac_ne_zero]


/-- Remove leading integer-side zeros from a most-significant-first digit list. -/
def trimHigh : List (Fin 5) → List (Fin 5)
  | [] => []
  | d :: ds => if d = 0 then trimHigh ds else d :: ds

/-- All leading integer-side zeros are value-neutral, not only one zero. -/
theorem trimHigh_value (xs : List (Fin 5)) :
    CNRSArithmetic.wordValue ((trimHigh xs).reverse) =
      CNRSArithmetic.wordValue xs.reverse := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
      by_cases hd : d = 0
      · subst d
        simpa [trimHigh, append_high_zero_value] using ih
      · simp [trimHigh, hd]

/-- Remove fraction-side zeroes only while the fractional depth is positive. -/
def trimLow : ℕ → List (Fin 5) → ℕ × List (Fin 5)
  | 0, ds => (0, ds)
  | depth + 1, [] => (0, [])
  | depth + 1, d :: ds =>
      if d = 0 then trimLow depth ds else (depth + 1, d :: ds)

/-- All fractional trailing zeros are value-neutral, not only one zero. -/
theorem trimLow_value (depth : ℕ) (ds : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent (trimLow depth ds).1 (trimLow depth ds).2 =
      CnrsQ2.evalFiniteLaurent depth ds := by
  induction depth generalizing ds with
  | zero => simp [trimLow]
  | succ depth ih =>
      cases ds with
      | nil => simp [trimLow, CnrsQ2.evalFiniteLaurent, CnrsQ2.evalGaussianDigits]
      | cons d tail =>
          by_cases hd : d = 0
          · subst d
            change
              CnrsQ2.evalFiniteLaurent (trimLow depth tail).1
                (trimLow depth tail).2 =
              CnrsQ2.evalFiniteLaurent (depth + 1) (0 :: tail)
            exact (ih tail).trans (drop_fraction_zero_value depth tail).symm
          · simp [trimLow, hd]

/-- Numeric normalizer for a finite least-significant-first word with
    an explicit count of fractional places. This is a mathematical specification
    of the Python formatting operations, not an extraction of Python code. -/
def normalizeWord (depth : ℕ) (ds : List (Fin 5)) : ℕ × List (Fin 5) :=
  let p := trimLow depth ds
  (p.1, (trimHigh p.2.reverse).reverse)

/-- Complete numeric normalization preserves exact Gaussian-fraction value. -/
theorem normalizeWord_value (depth : ℕ) (ds : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent (normalizeWord depth ds).1
      (normalizeWord depth ds).2 = CnrsQ2.evalFiniteLaurent depth ds := by
  let p := trimLow depth ds
  have hlow : CnrsQ2.evalFiniteLaurent p.1 p.2 =
      CnrsQ2.evalFiniteLaurent depth ds := trimLow_value depth ds
  calc
    CnrsQ2.evalFiniteLaurent (normalizeWord depth ds).1
        (normalizeWord depth ds).2 =
      CnrsQ2.evalFiniteLaurent p.1 ((trimHigh p.2.reverse).reverse) := rfl
    _ = CnrsQ2.evalFiniteLaurent p.1 p.2 := by
      unfold CnrsQ2.evalFiniteLaurent
      change
        (algebraMap GaussianInt CnrsQ2.GaussianFrac
          (CNRSArithmetic.wordValue ((trimHigh p.2.reverse).reverse))) /
          CnrsQ2.betaFrac ^ p.1 =
        (algebraMap GaussianInt CnrsQ2.GaussianFrac
          (CNRSArithmetic.wordValue p.2)) / CnrsQ2.betaFrac ^ p.1
      have hw := trimHigh_value p.2.reverse
      simpa only [List.reverse_reverse] using
        congrArg
          (fun v : GaussianInt =>
            (algebraMap GaussianInt CnrsQ2.GaussianFrac v) / CnrsQ2.betaFrac ^ p.1)
          hw
    _ = CnrsQ2.evalFiniteLaurent depth ds := hlow

/-- Finite exact addition followed by numeric canonical normalization. -/
def addNormalized (a b : FiniteSpelling) : ℕ × List (Fin 5) :=
  let depth := max a.fraction.length b.fraction.length
  normalizeWord depth (CNRSArithmetic.addWords (padWord a depth) (padWord b depth))

/-- The composed string/offset/alignment/addition/normalization value theorem. -/
theorem addNormalized_value (a b : FiniteSpelling) :
    CnrsQ2.evalFiniteLaurent (addNormalized a b).1 (addNormalized a b).2 =
      spellingValue a + spellingValue b := by
  exact (normalizeWord_value (max a.fraction.length b.fraction.length)
    (CNRSArithmetic.addWords
      (padWord a (max a.fraction.length b.fraction.length))
      (padWord b (max a.fraction.length b.fraction.length)))).trans
      (addFiniteStrings_value a b)

end CNRSIntegration
