import CNRSArithmetic.MSDRankedObstruction
import Mathlib.Tactic

/-!
# A concrete 15-node ranked obstruction, divisor -1, radius 8

This is a *finite, exact* certificate, derived from the previously recorded
CNRS P4 MSD obstruction search. It proves that there is no total online policy
on the integer remainder disk x^2+y^2 <= 64 for divisor -1 and delay 0,
with the canonical five-digit input/output alphabet.

It does not formalize the external geometric confinement lemma that every
finite invariant set must lie in this disk, or other delays/divisors.
-/

namespace CNRSArithmetic

def minusOneInside (r : GaussianRemainder) : Prop :=
  r.1 * r.1 + r.2 * r.2 ≤ (64 : ℤ)

def minusOneDeleted (r : GaussianRemainder) : Prop :=
    r = (-2, 3) ∨
    r = (-3, 3) ∨
    r = (-4, 3) ∨
    r = (-4, 4) ∨
    r = (-5, 3) ∨
    r = (-5, 4) ∨
    r = (-6, 3) ∨
    r = (-6, 4) ∨
    r = (-6, 5) ∨
    r = (6, 0) ∨
    r = (7, 0) ∨
    r = (3, 0) ∨
    r = (4, 0) ∨
    r = (5, 0) ∨
    r = (0, 0)

def minusOneRank (r : GaussianRemainder) : ℕ :=
  if r = (0, 0) then 3 else if (r = (3, 0) ∨ r = (4, 0) ∨ r = (5, 0)) then 2
  else if minusOneDeleted r then 1 else 0

def minusOneAdversary (r : GaussianRemainder) : Fin 5 :=
  if r = (0, 0) then 3 else 0

theorem minusOne_origin_deleted : minusOneDeleted (0, 0) := by
  simp [minusOneDeleted]

theorem minusOne_deleted_in_disk :
    ∀ r, minusOneDeleted r → minusOneInside r := by
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r
  all_goals norm_num [minusOneInside]

/-- Every successor of an eliminated node either leaves the radius-8 disk
    or has strictly smaller elimination rank. All 15 node cases and all
    five output digits are covered by integer arithmetic. -/
theorem minusOne_all_deleted_transitions :
    ∀ r, minusOneDeleted r →
      ∀ d : Fin 5,
        minusOneInside (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) →
          minusOneDeleted (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) ∧
          minusOneRank (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) <
            minusOneRank r := by
  intro r hr d hinside
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r
  all_goals fin_cases d <;>
    norm_num [msdDivisionStep, minusOneInside, minusOneDeleted,
      minusOneRank, minusOneAdversary] at *

/-- No canonical MSD-first online-output policy can remain in the complete
    radius-8 disk for divisor -1, delay zero. This is an exact finite
    special-case theorem, not the general P4 conjecture. -/
theorem minusOne_no_online_policy_disk :
    ¬ HasOnlineRemainderPolicy minusOneInside (msdDivisionStep (-1, 0)) := by
  exact msdDeletionCertificate_noPolicy (-1, 0)
    minusOneInside minusOneDeleted minusOneRank minusOneAdversary
    minusOne_origin_deleted minusOne_deleted_in_disk
    minusOne_all_deleted_transitions

end CNRSArithmetic
