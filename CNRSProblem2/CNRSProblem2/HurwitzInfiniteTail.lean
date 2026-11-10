import CNRSProblem2.HurwitzSharpMajorant
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# CNRS-H: actual infinite-series truncation error

Unlike the finite-tail estimates in HurwitzUniformBudget, these theorems
bound the norm of an actual convergent infinite tsum minus its finite
Taylor/Hurwitz partial sum. Summability and the all-order absolute
coefficient budget are derived by the imported certified theorems.
No generic finite jet is assigned a bound for unseen coefficients.

The next layer specializes the abstract error estimate to the exact
canonical RAValue recurrence via HurwitzSharp.betaExactSharpBudget.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- A uniform proof-carrying coefficient budget controls the actual
infinite sum of coefficient norms. -/
theorem UniformCoefficientBudget.tsum_norm_le
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a) :
    (∑' n : ℕ, ‖a n‖) ≤ cert.bound := by
  apply Real.tsum_le_of_sum_range_le (fun n => norm_nonneg (a n))
  intro M
  have hsub : Finset.range M ⊆ Finset.Icc 0 M := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn hnot => norm_nonneg (a n)))
    (cert.all_partial M)

/-- The nonnegative absolute coefficient tail (a genuine infinite tsum)
is bounded by the same all-order certificate. -/
theorem UniformCoefficientBudget.tsum_norm_shift_le
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a) (k : ℕ) :
    (∑' n : ℕ, ‖a (n + k)‖) ≤ cert.bound := by
  have hsplit := (cert.summable_norm a).sum_add_tsum_nat_add k
  have hpre : 0 ≤ ∑ n ∈ Finset.range k, ‖a n‖ := by
    apply Finset.sum_nonneg
    intro n hn
    exact norm_nonneg _
  have htail : (∑' n : ℕ, ‖a (n + k)‖) ≤
      (∑' n : ℕ, ‖a n‖) := by
    linarith
  exact htail.trans (cert.tsum_norm_le a)

/-- ACTUAL INFINITE TAIL: the difference of a convergent complex series
and its degree-N polynomial is bounded uniformly on the unit disk by
the certified all-order budget times |z|^(N+1). -/
theorem UniformCoefficientBudget.infinite_evaluation_tail_le
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a)
    (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(∑' n : ℕ, a n * z ^ n) -
        (∑ n ∈ Finset.range (N + 1), a n * z ^ n)‖ ≤
      ‖z‖ ^ (N + 1) * cert.bound := by
  have hnorm : Summable (fun n : ℕ => ‖a n * z ^ n‖) := by
    refine Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => ?_) (cert.summable_norm a)
    rw [norm_mul, norm_pow]
    have hpow : ‖z‖ ^ n ≤ 1 := by
      simpa using
        (pow_le_pow_of_le_one (norm_nonneg z) hz (Nat.zero_le n))
    calc
      ‖a n‖ * ‖z‖ ^ n ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖a n‖ := by ring
  have hnormShift : Summable (fun n : ℕ =>
      ‖a (n + (N + 1)) * z ^ (n + (N + 1))‖) :=
    (summable_nat_add_iff (N + 1)).mpr hnorm
  have haShift : Summable (fun n : ℕ => ‖a (n + (N + 1))‖) :=
    (summable_nat_add_iff (N + 1)).mpr (cert.summable_norm a)
  have hpoint (n : ℕ) :
      ‖a (n + (N + 1)) * z ^ (n + (N + 1))‖ ≤
        ‖z‖ ^ (N + 1) * ‖a (n + (N + 1))‖ := by
    have hp : ‖z‖ ^ (n + (N + 1)) ≤ ‖z‖ ^ (N + 1) :=
      pow_le_pow_of_le_one (norm_nonneg z) hz (by omega)
    calc
      ‖a (n + (N + 1)) * z ^ (n + (N + 1))‖ =
        ‖a (n + (N + 1))‖ * ‖z‖ ^ (n + (N + 1)) := by
          rw [norm_mul, norm_pow]
      _ ≤ ‖a (n + (N + 1))‖ * ‖z‖ ^ (N + 1) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = ‖z‖ ^ (N + 1) * ‖a (n + (N + 1))‖ := by ring
  have hsplit :
      (∑' n : ℕ, a n * z ^ n) -
          (∑ n ∈ Finset.range (N + 1), a n * z ^ n) =
      ∑' n : ℕ, a (n + (N + 1)) * z ^ (n + (N + 1)) := by
    rw [← (cert.summable_evaluation a z hz).sum_add_tsum_nat_add (N + 1)]
    abel
  calc
    ‖(∑' n : ℕ, a n * z ^ n) -
        (∑ n ∈ Finset.range (N + 1), a n * z ^ n)‖ =
      ‖∑' n : ℕ, a (n + (N + 1)) * z ^ (n + (N + 1))‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖a (n + (N + 1)) * z ^ (n + (N + 1))‖ :=
      norm_tsum_le_tsum_norm hnormShift
    _ ≤ ∑' n : ℕ,
        ‖z‖ ^ (N + 1) * ‖a (n + (N + 1))‖ :=
      hnormShift.tsum_le_tsum hpoint (haShift.mul_left _)
    _ = ‖z‖ ^ (N + 1) *
          (∑' n : ℕ, ‖a (n + (N + 1))‖) :=
      Summable.tsum_mul_left _ haShift
    _ ≤ ‖z‖ ^ (N + 1) * cert.bound :=
      mul_le_mul_of_nonneg_left
        (cert.tsum_norm_shift_le a (N + 1))
        (pow_nonneg (norm_nonneg z) _)

#print axioms UniformCoefficientBudget.tsum_norm_le
#print axioms UniformCoefficientBudget.tsum_norm_shift_le
#print axioms UniformCoefficientBudget.infinite_evaluation_tail_le

end CNRSProblem2
