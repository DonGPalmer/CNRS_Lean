import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic

/-!
# CNRS Problem 4: finite ranked-obstruction certificate, specification level

For MSD-first division by a Gaussian integer v at radix -2+i,
the remainder recurrence is r' = (-2+i)r + a - v*d, a,d in {0,...,4}.

A finite pruning computation assigns a *rank* to eliminated remainders and
chooses, at each eliminated remainder, an input digit for which every output
digit either leaves the allowed region or reaches a remainder with lower rank.

The theorem below certifies the logic of such a rank witness without proving
that a particular external Python certificate satisfies the finite hypotheses.
No computation of the greatest invariant subset, whole-divisor classification,
or correctness of a Python implementation is claimed here.
-/

namespace CNRSArithmetic

/-- Coordinates of a Gaussian integer, used to avoid any floating-point
    assumptions in finite-state obstruction proofs. -/
abbrev GaussianRemainder := ℤ × ℤ

/-- Exact MSD-first step for beta=-2+i. -/
def msdDivisionStep (v r : GaussianRemainder) (a d : Fin 5) :
    GaussianRemainder :=
  (-2 * r.1 - r.2 + (a.val : ℤ) - v.1 * (d.val : ℤ),
    r.1 - 2 * r.2 - v.2 * (d.val : ℤ))

/-- An online output policy must be able to preserve the allowable remainder
    set for every input digit at every reachable remainder. -/
def HasOnlineRemainderPolicy {State : Type}
    (inside : State → Prop)
    (advance : State → Fin 5 → Fin 5 → State) : Prop :=
  ∀ s, inside s → ∀ a : Fin 5, ∃ d : Fin 5, inside (advance s a d)

/-- A ranking function with an adversarial input at every allowable state
    excludes every nonempty invariant online-division policy.

    The theorem is independent of the finiteness of `State`; the rank is
    natural-valued and a strict descent cannot continue forever. It is
    applicable to finite pruning/DAG witnesses but does not itself check a
    serialized certificate. -/
theorem rankedObstruction_noOnlinePolicy {State : Type}
    (inside : State → Prop)
    (advance : State → Fin 5 → Fin 5 → State)
    (rank : State → ℕ)
    (adversarialInput : State → Fin 5)
    (hseed : ∃ s : State, inside s)
    (hdecrease : ∀ s, inside s →
      ∀ d : Fin 5, inside (advance s (adversarialInput s) d) →
        rank (advance s (adversarialInput s) d) < rank s) :
    ¬ HasOnlineRemainderPolicy inside advance := by
  intro hpolicy
  have hnone : ∀ n : ℕ, ∀ s : State, rank s = n → ¬ inside s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hins
      obtain ⟨d, hnext⟩ := hpolicy s hins (adversarialInput s)
      have hlt : rank (advance s (adversarialInput s) d) < n := by
        simpa [hs] using hdecrease s hins d hnext
      exact ih (rank (advance s (adversarialInput s) d)) hlt
        (advance s (adversarialInput s) d) rfl hnext
  obtain ⟨s, hs⟩ := hseed
  exact hnone (rank s) s rfl hs

/-- Specialization of the ranked obstruction to the canonical CNRS radix.
    This is a structural certificate theorem, not a proof of a particular
    divisor's state enumeration. -/
theorem msdRankedCertificate_noPolicy
    (v : GaussianRemainder)
    (inside : GaussianRemainder → Prop)
    (rank : GaussianRemainder → ℕ)
    (adversarialInput : GaussianRemainder → Fin 5)
    (h0 : inside (0, 0))
    (hdecrease : ∀ s, inside s →
      ∀ d : Fin 5, inside (msdDivisionStep v s (adversarialInput s) d) →
        rank (msdDivisionStep v s (adversarialInput s) d) < rank s) :
    ¬ HasOnlineRemainderPolicy inside (msdDivisionStep v) := by
  exact rankedObstruction_noOnlinePolicy inside (msdDivisionStep v)
    rank adversarialInput ⟨(0, 0), h0⟩ hdecrease

end CNRSArithmetic
