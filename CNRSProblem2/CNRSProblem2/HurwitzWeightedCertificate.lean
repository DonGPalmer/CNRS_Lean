import CNRSProblem2.HurwitzComplexTail
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# CNRS-H: factorially weighted finite convolution and certified tails

Finite exact building blocks for the analytic certificate. These theorems
do not assert that an arbitrary infinite coefficient stream is summable,
or that a finite exact jet provides a majorant on unobserved coefficients.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- The factorial identity converting Hurwitz binomial convolution into
ordinary Cauchy convolution of normalized coefficients. -/
theorem hurwitz_choose_factorial (i j : ℕ) :
    (i + j).choose i * i.factorial * j.factorial =
      (i + j).factorial := by
  simpa [Nat.add_sub_cancel_left] using
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j))

/-- The sum of all finitely many weighted pairwise products factorizes,
which is the exact finite convolution norm budget before cancellation. -/
theorem finite_weighted_pair_budget (s t : Finset ℕ)
    (a b : ℕ → ℂ) (R : ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, ‖a i * b j‖ * R ^ (i + j)) =
      (∑ i ∈ s, ‖a i‖ * R ^ i) *
      (∑ j ∈ t, ‖b j‖ * R ^ j) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [norm_mul, pow_add]
  ring

/-- A finite tail certificate must receive a bound on the relevant
coefficient majorant; the degree-N prefix alone does not provide one. -/
theorem finite_complex_tail_with_budget
    (c : ℕ → ℂ) (N M : ℕ) (z : ℂ) (B : ℝ)
    (hz : ‖z‖ ≤ 1)
    (hB : (∑ n ∈ Finset.Icc (N + 1) M, ‖c n‖) ≤ B) :
    ‖∑ n ∈ Finset.Icc (N + 1) M, c n * z ^ n‖ ≤
      ‖z‖ ^ (N + 1) * B := by
  calc
    ‖∑ n ∈ Finset.Icc (N + 1) M, c n * z ^ n‖ ≤
        ‖z‖ ^ (N + 1) *
          (∑ n ∈ Finset.Icc (N + 1) M, ‖c n‖) :=
      finite_complex_tail_majorant_z c N M z hz
    _ ≤ ‖z‖ ^ (N + 1) * B :=
      mul_le_mul_of_nonneg_left hB (pow_nonneg (norm_nonneg z) _)

end CNRSProblem2
