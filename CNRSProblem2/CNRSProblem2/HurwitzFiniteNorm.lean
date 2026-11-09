import CNRSProblem2.HurwitzWeightedCertificate
import CNRSProblem2.FiniteHurwitz
import Mathlib.Tactic

/-!
# Finite-support weighted CNRS-H norm

This module connects the factorially normalized pair budget with the
actual finite-support Hurwitz carrier. Work is purely finite; no claim
about arbitrary infinite-series summability or automatic majorants.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- The radius-weighted finite Hurwitz coefficient norm. -/
noncomputable def finiteHurwitzWeightedNorm
    (R : ℝ) (x : FiniteHurwitz ℂ) : ℝ :=
  ∑ n ∈ x.coeff.support, ‖x n‖ * (R ^ n / n.factorial)

/-- Every coefficient of a finite-support Hurwitz series contributes a
nonnegative amount at nonnegative radius. -/
theorem finiteHurwitzWeightedNorm_nonneg
    (R : ℝ) (hR : 0 ≤ R) (x : FiniteHurwitz ℂ) :
    0 ≤ finiteHurwitzWeightedNorm R x := by
  unfold finiteHurwitzWeightedNorm
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (norm_nonneg _) (div_nonneg (pow_nonneg hR _) (by positivity))

/-- The weighted norm of a sum satisfies the triangle inequality. -/
theorem finiteHurwitzWeightedNorm_add_le
    (R : ℝ) (hR : 0 ≤ R) (x y : FiniteHurwitz ℂ) :
    finiteHurwitzWeightedNorm R (x + y) ≤
      finiteHurwitzWeightedNorm R x + finiteHurwitzWeightedNorm R y := by
  classical
  let S : Finset ℕ := x.coeff.support ∪ y.coeff.support
  have hz (z : FiniteHurwitz ℂ)
      (hsub : z.coeff.support ⊆ S) :
      (∑ n ∈ z.coeff.support, ‖z n‖ * (R ^ n / n.factorial)) =
      ∑ n ∈ S, ‖z n‖ * (R ^ n / n.factorial) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hzero : z n = 0 := Finsupp.not_mem_support_iff.mp hnot
    simp [hzero]
  have hx : x.coeff.support ⊆ S := Finset.subset_union_left
  have hy : y.coeff.support ⊆ S := Finset.subset_union_right
  have hxy : (x + y).coeff.support ⊆ S := by
    intro n hn
    by_contra hnot
    have hnx : x n = 0 :=
      Finsupp.not_mem_support_iff.mp (by
        intro h; exact hnot (Finset.mem_union_left _ h))
    have hny : y n = 0 :=
      Finsupp.not_mem_support_iff.mp (by
        intro h; exact hnot (Finset.mem_union_right _ h))
    have hnzero : (x + y) n = 0 := by simp [hnx, hny]
    exact (Finsupp.mem_support_iff.mp hn) hnzero
  unfold finiteHurwitzWeightedNorm
  rw [hz (x + y) hxy, hz x hx, hz y hy, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  rw [FiniteHurwitz.coeff_add]
  have hw : 0 ≤ R ^ n / (n.factorial : ℝ) :=
    div_nonneg (pow_nonneg hR _) (by positivity)
  calc
    ‖x n + y n‖ * (R ^ n / n.factorial) ≤
        (‖x n‖ + ‖y n‖) * (R ^ n / n.factorial) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    _ = ‖x n‖ * (R ^ n / n.factorial) +
        ‖y n‖ * (R ^ n / n.factorial) := by ring

end CNRSProblem2
