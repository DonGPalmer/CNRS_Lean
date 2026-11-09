import CNRSIntegration.FiniteStringAdapter

/-!
CNRS-R1 follow-up: nonempty output spelling boundary.

The earlier `normalizeWord_value` theorem proves exact numerical preservation,
but an all-zero word may be reduced to the empty list. This module explicitly
restores one zero digit for display without changing the exact value.

Scope: proof of nonempty output and numerical preservation only.
No claim that arbitrary Python formatting code is formally verified.
-/

open Zsqrtd

namespace CNRSIntegration

/-- An empty finite digit word and a single zero digit have the same
    Gaussian-fraction value, at every fractional depth. -/
theorem zeroDigit_replaces_empty (depth : ℕ) :
    CnrsQ2.evalFiniteLaurent depth ([0] : List (Fin 5)) =
      CnrsQ2.evalFiniteLaurent depth ([] : List (Fin 5)) := by
  have hz : CNRSArithmetic.wordValue ([0] : List (Fin 5)) = 0 := by
    simpa using (zeroWord_value 1)
  have he : CNRSArithmetic.wordValue ([] : List (Fin 5)) = 0 := by
    simpa using (zeroWord_value 0)
  unfold CnrsQ2.evalFiniteLaurent
  change
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
      (CNRSArithmetic.wordValue ([0] : List (Fin 5)))) /
      CnrsQ2.betaFrac ^ depth =
    (algebraMap GaussianInt CnrsQ2.GaussianFrac
      (CNRSArithmetic.wordValue ([] : List (Fin 5)))) /
      CnrsQ2.betaFrac ^ depth
  simp [hz, he]

/-- Restore a one-digit representation when a value-preserving numerical
    normalizer has removed every digit. This is a display *nonemptiness*
    condition, not a full canonical spelling theorem. -/
def restoreZeroDigit (ds : List (Fin 5)) : List (Fin 5) :=
  if ds.isEmpty then [0] else ds

theorem restoreZeroDigit_nonempty (ds : List (Fin 5)) :
    restoreZeroDigit ds ≠ [] := by
  cases ds with
  | nil => simp [restoreZeroDigit]
  | cons d tail => simp [restoreZeroDigit]

theorem restoreZeroDigit_value (depth : ℕ) (ds : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent depth (restoreZeroDigit ds) =
      CnrsQ2.evalFiniteLaurent depth ds := by
  cases ds with
  | nil =>
      simpa [restoreZeroDigit] using (zeroDigit_replaces_empty depth)
  | cons d tail => simp [restoreZeroDigit]

/-- Nonempty display representation of the prior numerical normalizer. -/
def normalizeDisplay (depth : ℕ) (ds : List (Fin 5)) :
    ℕ × List (Fin 5) :=
  let p := normalizeWord depth ds
  (p.1, restoreZeroDigit p.2)

theorem normalizeDisplay_nonempty (depth : ℕ) (ds : List (Fin 5)) :
    (normalizeDisplay depth ds).2 ≠ [] := by
  exact restoreZeroDigit_nonempty _

theorem normalizeDisplay_value (depth : ℕ) (ds : List (Fin 5)) :
    CnrsQ2.evalFiniteLaurent (normalizeDisplay depth ds).1
      (normalizeDisplay depth ds).2 =
      CnrsQ2.evalFiniteLaurent depth ds := by
  exact (restoreZeroDigit_value (normalizeWord depth ds).1
    (normalizeWord depth ds).2).trans (normalizeWord_value depth ds)

/-- Exact addition with a nonempty output word, without asserting any
    unproved correspondence with the Python formatter. -/
def addDisplay (a b : FiniteSpelling) : ℕ × List (Fin 5) :=
  let depth := max a.fraction.length b.fraction.length
  normalizeDisplay depth
    (CNRSArithmetic.addWords (padWord a depth) (padWord b depth))

theorem addDisplay_value (a b : FiniteSpelling) :
    CnrsQ2.evalFiniteLaurent (addDisplay a b).1 (addDisplay a b).2 =
      spellingValue a + spellingValue b := by
  exact (normalizeDisplay_value (max a.fraction.length b.fraction.length)
    (CNRSArithmetic.addWords
      (padWord a (max a.fraction.length b.fraction.length))
      (padWord b (max a.fraction.length b.fraction.length)))).trans
        (addFiniteStrings_value a b)

theorem addDisplay_nonempty (a b : FiniteSpelling) :
    (addDisplay a b).2 ≠ [] := by
  exact normalizeDisplay_nonempty _ _

end CNRSIntegration
