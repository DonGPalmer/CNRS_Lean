import CNRSProblem2.HurwitzFiniteNorm
import Mathlib.Tactic

/-!
Full finite-support weighted Hurwitz product inequality: development candidate.
Finiteness is explicit; no claim that an infinite formal jet is summable.
-/
namespace CNRSProblem2
open scoped BigOperators

theorem finiteHurwitzWeightedNorm_mul_le
    (R : ℝ) (hR : 0 ≤ R) (x y : FiniteHurwitz ℂ) :
    finiteHurwitzWeightedNorm R (x * y) ≤
      finiteHurwitzWeightedNorm R x * finiteHurwitzWeightedNorm R y := by
  classical
  let S : Finset ℕ := x.coeff.support
  let T : Finset ℕ := y.coeff.support
  let U : Finset ℕ := (S.product T).image (fun p => p.1 + p.2)
  have hp (i j : ℕ) (hi : i ∈ S) (hj : j ∈ T) : i + j ∈ U := by
    exact Finset.mem_image.mpr
      ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩, rfl⟩
  have hsub : (x * y).coeff.support ⊆ U := by
    intro n hn
    by_contra hnot
    have hzero : (x * y) n = 0 := by
      rw [FiniteHurwitz.coeff_mul_support]
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i + j ≠ n := by
        intro heq
        exact hnot (heq ▸ hp i j hi hj)
      simp [hij]
    exact (Finsupp.mem_support_iff.mp hn) hzero
  have hweight (n : ℕ) : 0 ≤ R ^ n / (n.factorial : ℝ) :=
    div_nonneg (pow_nonneg hR _) (by positivity)
  have hsum : finiteHurwitzWeightedNorm R (x * y) =
      ∑ n ∈ U, ‖(x * y) n‖ * (R ^ n / n.factorial) := by
    unfold finiteHurwitzWeightedNorm
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hzero : (x * y) n = 0 := by
      by_contra hnonzero
      exact hnot (Finsupp.mem_support_iff.mpr hnonzero)
    simp [hzero]
  have hdist (n : ℕ) :
      (∑ i ∈ S, ∑ j ∈ T,
        ‖if i + j = n then (i + j).choose i • (x i * y j)
          else (0 : ℂ)‖) * (R ^ n / n.factorial) =
      ∑ i ∈ S, ∑ j ∈ T,
        if i + j = n then
          ‖(i + j).choose i • (x i * y j)‖ *
            (R ^ (i + j) / (i + j).factorial) else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i + j = n
    · subst n
      simp
    · simp [h]
  have hswap (g : ℕ → ℕ → ℝ) :
      (∑ n ∈ U, ∑ i ∈ S, ∑ j ∈ T,
          if i + j = n then g i j else 0) =
      ∑ i ∈ S, ∑ j ∈ T, g i j := by
    calc
      _ = ∑ i ∈ S, ∑ n ∈ U, ∑ j ∈ T,
            if i + j = n then g i j else 0 := by rw [Finset.sum_comm]
      _ = ∑ i ∈ S, ∑ j ∈ T, ∑ n ∈ U,
            if i + j = n then g i j else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
      _ = ∑ i ∈ S, ∑ j ∈ T, g i j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp [Finset.sum_ite_eq', hp i j hi hj]
  calc
    finiteHurwitzWeightedNorm R (x * y) =
        ∑ n ∈ U, ‖(x * y) n‖ * (R ^ n / n.factorial) := hsum
    _ ≤ ∑ n ∈ U,
          (∑ i ∈ S, ∑ j ∈ T,
            ‖if i + j = n then (i + j).choose i • (x i * y j)
              else (0 : ℂ)‖) * (R ^ n / n.factorial) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (finiteHurwitzCoeffNorm_le_pairSum x y n) (hweight n)
    _ = ∑ n ∈ U, ∑ i ∈ S, ∑ j ∈ T,
          if i + j = n then
            ‖(i + j).choose i • (x i * y j)‖ *
              (R ^ (i + j) / (i + j).factorial) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hdist n
    _ = ∑ i ∈ S, ∑ j ∈ T,
          ‖(i + j).choose i • (x i * y j)‖ *
            (R ^ (i + j) / (i + j).factorial) := by
      exact hswap (fun i j =>
        ‖(i + j).choose i • (x i * y j)‖ *
          (R ^ (i + j) / (i + j).factorial))
    _ = ∑ i ∈ S, ∑ j ∈ T,
          ‖x i * y j‖ *
            (((i + j).choose i : ℝ) * R ^ (i + j) / (i + j).factorial) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hh : ‖(i + j).choose i • (x i * y j)‖ =
          ((i + j).choose i : ℝ) * ‖x i * y j‖ := by
        simp [nsmul_eq_mul, norm_mul]
      rw [hh]
      ring
    _ = (∑ i ∈ S, ‖x i‖ * (R ^ i / i.factorial)) *
          (∑ j ∈ T, ‖y j‖ * (R ^ j / j.factorial)) :=
      finite_hurwitz_factorial_pair_budget S T x y R
    _ = finiteHurwitzWeightedNorm R x * finiteHurwitzWeightedNorm R y := rfl

end CNRSProblem2
