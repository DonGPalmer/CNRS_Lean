import CNRSArithmetic.MSDMinusOneFiniteInvariant
import Mathlib.Tactic

/-!
# CNRS P4: finite-state remainder-machine reduction

A finite state set equipped with a Gaussian remainder for each state, an
initial zero remainder, and a total digit transition preserving the exact
delay-zero divisor-minus-one recurrence would generate a finite controlled-
invariant remainder set containing zero. The proved finite-invariant
obstruction therefore rules out such a machine.

This theorem does NOT formalize that every correct online algorithm must
have such a finite state description, or cover positive delay or other
divisors. The recurrence-preservation condition is an explicit hypothesis.
-/

namespace CNRSArithmetic

/-- A finite-state transition system whose observed remainder obeys the
canonical MSD division recurrence cannot be total on all five input digits,
when the divisor is -1 and there is no delay. -/
theorem minusOne_no_finite_state_remainder_machine
    {Q : Type*} [Fintype Q]
    (remainder : Q → GaussianRemainder)
    (initial : Q)
    (hzero : remainder initial = (0, 0))
    (transition : Q → Fin 5 → Q × Fin 5)
    (htransition : ∀ q a,
      remainder (transition q a).1 =
        msdDivisionStep (-1, 0) (remainder q) a (transition q a).2) :
    False := by
  classical
  let S : Finset GaussianRemainder := Finset.univ.image remainder
  have hz : (0, 0) ∈ S := by
    exact Finset.mem_image.mpr ⟨initial, Finset.mem_univ _, hzero⟩
  have hinv : ∀ r ∈ S, ∀ a : Fin 5,
      ∃ d : Fin 5, msdDivisionStep (-1, 0) r a d ∈ S := by
    intro r hr a
    obtain ⟨q, hqmem, hq⟩ := Finset.mem_image.mp hr
    refine ⟨(transition q a).2, ?_⟩
    have hmem : remainder (transition q a).1 ∈ S :=
      Finset.mem_image.mpr
        ⟨(transition q a).1, Finset.mem_univ _, rfl⟩
    have hstep : msdDivisionStep (-1, 0) r a (transition q a).2 =
        remainder (transition q a).1 := by
      rw [← hq, ← htransition]
    rw [hstep]
    exact hmem
  exact minusOne_no_finite_invariant S hz hinv

end CNRSArithmetic
