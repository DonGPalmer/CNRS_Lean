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
    have hzero : z n = 0 := by
      by_contra hnonzero
      exact hnot (Finsupp.mem_support_iff.mpr hnonzero)
    simp [hzero]
  have hx : x.coeff.support ⊆ S := Finset.subset_union_left
  have hy : y.coeff.support ⊆ S := Finset.subset_union_right
  have hxy : (x + y).coeff.support ⊆ S := by
    intro n hn
    by_contra hnot
    have hnx : x n = 0 := by
      by_contra hnonzero
      exact hnot (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hnonzero))
    have hny : y n = 0 := by
      by_contra hnonzero
      exact hnot (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hnonzero))
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

/-- The factorially weighted norm of a single supported coefficient. -/
theorem finiteHurwitzWeightedNorm_single (R : ℝ) (n : ℕ) (a : ℂ) :
    finiteHurwitzWeightedNorm R (FiniteHurwitz.single n a) =
      ‖a‖ * (R ^ n / n.factorial) := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [finiteHurwitzWeightedNorm, FiniteHurwitz.single]
  · simp [finiteHurwitzWeightedNorm, FiniteHurwitz.single, ha]

/-- A basis Hurwitz product has exactly multiplicative weighted norm:
the binomial factor cancels with the output factorial. -/
theorem finiteHurwitzWeightedNorm_single_mul_single
    (R : ℝ) (i j : ℕ) (a b : ℂ) :
    finiteHurwitzWeightedNorm R
      (FiniteHurwitz.single i a * FiniteHurwitz.single j b) =
    finiteHurwitzWeightedNorm R (FiniteHurwitz.single i a) *
      finiteHurwitzWeightedNorm R (FiniteHurwitz.single j b) := by
  rw [FiniteHurwitz.single_mul_single]
  simp only [finiteHurwitzWeightedNorm_single]
  have hnorm : ‖((i + j).choose i) • (a * b)‖ =
      ((i + j).choose i : ℝ) * (‖a‖ * ‖b‖) := by
    simp [nsmul_eq_mul, norm_mul]
  rw [hnorm]
  calc
    ((i + j).choose i : ℝ) * (‖a‖ * ‖b‖) *
        (R ^ (i + j) / (i + j).factorial) =
      (‖a‖ * ‖b‖) *
        (((i + j).choose i : ℝ) * R ^ (i + j) / (i + j).factorial) := by ring
    _ = (‖a‖ * (R ^ i / i.factorial)) *
          (‖b‖ * (R ^ j / j.factorial)) := by
      rw [hurwitz_factorial_weight]
      ring

/-- Norm of each actual output coefficient is bounded by the full
finite pairwise contribution budget at that degree. This is the first
aggregation estimate needed to lift the pair identity to a global norm. -/
theorem finiteHurwitzCoeffNorm_le_pairSum
    (x y : FiniteHurwitz ℂ) (n : ℕ) :
    ‖(x * y) n‖ ≤
      ∑ i ∈ x.coeff.support, ∑ j ∈ y.coeff.support,
        ‖if i + j = n then
            (i + j).choose i • (x i * y j) else (0 : ℂ)‖ := by
  rw [FiniteHurwitz.coeff_mul_support]
  calc
    ‖∑ i ∈ x.coeff.support, ∑ j ∈ y.coeff.support,
        if i + j = n then (i + j).choose i • (x i * y j)
        else (0 : ℂ)‖ ≤
      ∑ i ∈ x.coeff.support,
        ‖∑ j ∈ y.coeff.support,
          if i + j = n then (i + j).choose i • (x i * y j)
          else (0 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ x.coeff.support, ∑ j ∈ y.coeff.support,
          ‖if i + j = n then
              (i + j).choose i • (x i * y j) else (0 : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _

end CNRSProblem2
