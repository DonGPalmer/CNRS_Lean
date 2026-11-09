import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-!
# Branch-state limitation: noncommuting monodromy cannot embed faithfully
  into an additive commuting winding vector

This is a scoped algebraic boundary result. Two transpositions of three
branches do not commute. Consequently a branch-state label into any
commutative additive monoid, if it respects composition, cannot be injective.

The theorem is independent of the analytic continuation of a particular
polynomial family: identifying the continuation generators of
y^3 - 3y + t with these transpositions is a separate analytic obligation.
It does *not* invalidate the canonical one-logarithm CNRS index.
-/

namespace CNRSProblem2

/-- Adjacent exchanges of three sheets. -/
def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- The two generators of the three-sheet permutation action do not commute. -/
theorem threeSheetSwaps_noncommute :
    swap01 * swap12 ≠ swap12 * swap01 := by
  decide

/-- Any additive, composition-respecting label in a commutative target
    necessarily conflates two different three-sheet monodromy operators. -/
theorem abelianLabel_conflates_swaps {A : Type*} [AddCommMonoid A]
    (label : Equiv.Perm (Fin 3) → A)
    (hcomp : ∀ p q, label (p * q) = label p + label q) :
    label (swap01 * swap12) = label (swap12 * swap01) := by
  rw [hcomp, hcomp, add_comm]

/-- No injective additive winding-state representation of the whole
    three-sheet permutation group exists in a commutative additive carrier.
    This applies, in particular, to one or several independent integer
    branch indices under componentwise addition. -/
theorem no_faithful_abelian_branch_label {A : Type*} [AddCommMonoid A]
    (label : Equiv.Perm (Fin 3) → A)
    (hcomp : ∀ p q, label (p * q) = label p + label q) :
    ¬ Function.Injective label := by
  intro hinj
  exact threeSheetSwaps_noncommute
    (hinj (abelianLabel_conflates_swaps label hcomp))

/-- An additive path label cannot determine a surjective noncommuting
    three-sheet monodromy: two loop products have identical labels but
    different induced permutations.  Analytic realization of a particular
    cubic's monodromy remains outside this algebraic theorem. -/
theorem additive_state_does_not_determine_monodromy
    {G A : Type*} [Group G] [AddCommMonoid A]
    (perm : G →* Equiv.Perm (Fin 3))
    (hsurj : Function.Surjective perm)
    (s : G → A)
    (hs : ∀ g h, s (g * h) = s g + s h) :
    ∃ g h, s (g * h) = s (h * g) ∧
      perm (g * h) ≠ perm (h * g) := by
  obtain ⟨g, hg⟩ := hsurj swap01
  obtain ⟨h, hh⟩ := hsurj swap12
  refine ⟨g, h, ?_, ?_⟩
  · rw [hs, hs, add_comm]
  · rw [map_mul, map_mul, hg, hh]
    exact threeSheetSwaps_noncommute

end CNRSProblem2
