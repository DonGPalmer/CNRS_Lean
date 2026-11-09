import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
CNRS-H analytic certification: finite tail contraction for a
nonnegative coefficient majorant.

For a formal Hurwitz series, let
  b_n = |c_n| R^n / n!  and  q = r/R, 0 <= r <= R.
The theorem proves the finite-index inequality
  sum_{n=N+1}^M b_n q^n <= q^(N+1) sum_{n=N+1}^M b_n.
It is an algebraic finite-sum kernel for the proposed analytic error
certificate, *not* a convergence theorem or a claim that the exact
localized coefficient ring is analytically complete.
-/

namespace CNRSProblem2

open scoped BigOperators

/-- If 0 <= q <= 1, moving to a later power of q never increases its
    value. This proof avoids any unproved infinite-series assumptions. -/
theorem contraction_power_tail (q : ℝ) (N m : ℕ)
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

/-- Finite contraction bound, suitable for Hurwitz factorial-weighted
    coefficient majorants and independent of any asserted convergence. -/
theorem finite_hurwitz_tail_contraction
    (b : ℕ → ℝ) (N M : ℕ) (q : ℝ)
    (hb : ∀ n, 0 ≤ b n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Finset.Icc (N + 1) M, b n * q ^ n) ≤
      q ^ (N + 1) * (∑ n ∈ Finset.Icc (N + 1) M, b n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hbound : N + 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hexp : n = N + 1 + (n - (N + 1)) := by omega
  have hpow : q ^ n ≤ q ^ (N + 1) := by
    rw [hexp]
    exact contraction_power_tail q N (n - (N + 1)) hq0 hq1
  calc
    b n * q ^ n ≤ b n * q ^ (N + 1) :=
      mul_le_mul_of_nonneg_left hpow (hb n)
    _ = q ^ (N + 1) * b n := by ring

end CNRSProblem2
