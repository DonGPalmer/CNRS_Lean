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

/-- A ranked deletion witness is sound even if the *allowable disk* contains
    states that survived pruning.

    `eliminated s` means that a finite pruning certificate has assigned a
    positive deletion rank to `s`. `allowed s` denotes any state within the
    confinement region. At an eliminated state, the adversarial input
    guarantees that each output either leaves the allowable region or leads
    to an eliminated successor of strictly smaller rank.

    If the initial state is eliminated, no deterministic or nondeterministic
    total online policy can stay within the allowable region from every
    allowed state. Unlike the weaker theorem above, this explicitly
    separates *eliminated* states from the entire allowable region. -/
theorem rankedDeletion_fromSeed_noOnlinePolicy {State : Type}
    (allowed eliminated : State → Prop)
    (advance : State → Fin 5 → Fin 5 → State)
    (rank : State → ℕ)
    (adversarialInput : State → Fin 5)
    (seed : State)
    (hseed : eliminated seed)
    (hsub : ∀ s, eliminated s → allowed s)
    (hdecrease : ∀ s, eliminated s →
      ∀ d : Fin 5, allowed (advance s (adversarialInput s) d) →
        eliminated (advance s (adversarialInput s) d) ∧
          rank (advance s (adversarialInput s) d) < rank s) :
    ¬ HasOnlineRemainderPolicy allowed advance := by
  intro hpolicy
  have hnone : ∀ n : ℕ, ∀ s : State, rank s = n → ¬ eliminated s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hdeleted
      obtain ⟨d, hnext⟩ := hpolicy s (hsub s hdeleted) (adversarialInput s)
      obtain ⟨hdeletedNext, hltRaw⟩ := hdecrease s hdeleted d hnext
      have hlt : rank (advance s (adversarialInput s) d) < n := by
        simpa [hs] using hltRaw
      exact ih (rank (advance s (adversarialInput s) d)) hlt
        (advance s (adversarialInput s) d) rfl hdeletedNext
  exact hnone (rank seed) seed rfl hseed

/-- Concrete Gaussian-integer recurrence version, with the origin as seed.
    The only outstanding work for a particular divisor is supplying
    `allowed`, `eliminated`, the rank, and validating all five transitions. -/
theorem msdDeletionCertificate_noPolicy
    (v : GaussianRemainder)
    (allowed eliminated : GaussianRemainder → Prop)
    (rank : GaussianRemainder → ℕ)
    (adversarialInput : GaussianRemainder → Fin 5)
    (hzero : eliminated (0, 0))
    (hsub : ∀ s, eliminated s → allowed s)
    (hdecrease : ∀ s, eliminated s →
      ∀ d : Fin 5, allowed (msdDivisionStep v s (adversarialInput s) d) →
        eliminated (msdDivisionStep v s (adversarialInput s) d) ∧
          rank (msdDivisionStep v s (adversarialInput s) d) < rank s) :
    ¬ HasOnlineRemainderPolicy allowed (msdDivisionStep v) := by
  exact rankedDeletion_fromSeed_noOnlinePolicy allowed eliminated
    (msdDivisionStep v) rank adversarialInput (0, 0) hzero hsub hdecrease


end CNRSArithmetic
