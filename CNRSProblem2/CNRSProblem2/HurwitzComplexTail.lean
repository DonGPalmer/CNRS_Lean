import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# CNRS-H: finite complex evaluation bound for an exact majorant

This module bridges a finite nonnegative Hurwitz majorant to the actual norm
of a complex-valued truncated analytic realization.  It is independent of
the pending PR #4 and does not establish infinite-series convergence, an
analytic continuation theorem, or completion of the exact coefficient ring.

For exact Hurwitz coefficients cₙ over R_A embedded in ℂ, the intended
substitution is c n := coefficient_n * R^n / n! and q := r/R.
-/

namespace CNRSProblem2

open scoped BigOperators

private theorem tail_power_le (q : ℝ) (N m : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ^ (N + 1 + m) ≤ q ^ (N + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hexp : N + 1 + (m + 1) = (N + 1 + m) + 1 := by omega
    calc
      q ^ (N + 1 + (m + 1)) =
          q ^ (N + 1 + m) * q := by rw [hexp, pow_succ]
      _ ≤ q ^ (N + 1 + m) * 1 :=
        mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 _)
      _ = q ^ (N + 1 + m) := by ring
      _ ≤ q ^ (N + 1) := ih

/-- Finite truncation of a complex series: its actual absolute error is bounded
by the factorial-weight-compatible coefficient majorant contracted by q^(N+1).
The bound is finite and unconditional except 0 ≤ q ≤ 1. -/
theorem finite_complex_tail_majorant
    (c : ℕ → ℂ) (N M : ℕ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖∑ n ∈ Finset.Icc (N + 1) M, c n * (q : ℂ) ^ n‖ ≤
      q ^ (N + 1) * (∑ n ∈ Finset.Icc (N + 1) M, ‖c n‖) := by
  calc
    ‖∑ n ∈ Finset.Icc (N + 1) M, c n * (q : ℂ) ^ n‖ ≤
        ∑ n ∈ Finset.Icc (N + 1) M, ‖c n * (q : ℂ) ^ n‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc (N + 1) M, ‖c n‖ * q ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_pow]
      simp [Complex.norm_real, abs_of_nonneg hq0]
    _ ≤ q ^ (N + 1) * ∑ n ∈ Finset.Icc (N + 1) M, ‖c n‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hle : N + 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hexp : n = N + 1 + (n - (N + 1)) := by omega
      have hpow : q ^ n ≤ q ^ (N + 1) := by
        rw [hexp]
        exact tail_power_le q N (n - (N + 1)) hq0 hq1
      calc
        ‖c n‖ * q ^ n ≤ ‖c n‖ * q ^ (N + 1) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = q ^ (N + 1) * ‖c n‖ := by ring

end CNRSProblem2
