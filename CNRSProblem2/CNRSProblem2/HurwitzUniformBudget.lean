import CNRSProblem2.HurwitzProductBudget
import CNRSProblem2.HurwitzWeightedCertificate
import Mathlib.Tactic

/-!
# CNRS-H: uniform all-order analytic coefficient-budget interface

An all-index certificate differs from a finite-jet assertion:
the proof must control the normalized absolute coefficient budget on
*every* partial sum, not just the coefficients present in a supplied jet.

This file proves a finite-tail bound that holds simultaneously for all
truncation degrees, conditional on that explicit all-index hypothesis.
The convergence of the resulting infinite series is a separate mathematical
claim and is not asserted by any theorem in this file.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- A uniform coefficient budget across ALL finite partial sums. For a
normalized coefficient family a n := c_n R^n/n!, a certificate of this form
is the precise all-index input required by the analytic tail estimates. -/
structure UniformCoefficientBudget (a : ℕ → ℂ) where
  bound : ℝ
  all_partial : ∀ M : ℕ,
    (∑ n ∈ Finset.Icc 0 M, ‖a n‖) ≤ bound

/-- The sum over degrees N+1,...,M is bounded by the all-index certificate,
independently of the particular choice of M and N. -/
theorem UniformCoefficientBudget.tail_le
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a) (N M : ℕ) :
    (∑ n ∈ Finset.Icc (N + 1) M, ‖a n‖) ≤ cert.bound := by
  have hsub : Finset.Icc (N + 1) M ⊆ Finset.Icc 0 M := by
    intro n hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
  have hsum :
      (∑ n ∈ Finset.Icc (N + 1) M, ‖a n‖) ≤
      (∑ n ∈ Finset.Icc 0 M, ‖a n‖) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    exact norm_nonneg _
  exact le_trans hsum (cert.all_partial M)

/-- Every finite tail at every truncation order is bounded uniformly at
complex evaluation points of norm at most one. The certificate is NOT
constructed from a finite jet; it must be supplied with all_partial. -/
theorem UniformCoefficientBudget.evaluation_tail
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a)
    (N M : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc (N + 1) M, a n * z ^ n‖ ≤
      ‖z‖ ^ (N + 1) * cert.bound := by
  exact finite_complex_tail_with_budget
    a N M z cert.bound hz (cert.tail_le a N M)

/-- A uniform coefficient budget is automatically nonnegative, since the
degree-zero partial sum is the norm of one coefficient. -/
theorem UniformCoefficientBudget.bound_nonneg
    (a : ℕ → ℂ) (cert : UniformCoefficientBudget a) :
    0 ≤ cert.bound := by
  have h := cert.all_partial 0
  have hn : 0 ≤ (∑ n ∈ Finset.Icc 0 0, ‖a n‖) := by
    apply Finset.sum_nonneg
    intro n hn
    exact norm_nonneg _
  exact le_trans hn h

end CNRSProblem2
