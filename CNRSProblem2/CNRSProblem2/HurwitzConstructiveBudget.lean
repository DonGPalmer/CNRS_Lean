import CNRSProblem2.HurwitzFactorialMajorant
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# CNRS-H: a fully constructive all-index analytic certificate

For the recurrence c₀=1, c₁=a,
c_(n+2) = a*c_(n+1) + (n+1)*c_n,
with ‖a‖ ≤ 1, the separate factorial growth theorem implies
‖c_n R^n/n!‖ ≤ R^n. Hence for 0≤R<1 every partial sum of
these normed coefficients is at most (1-R)⁻¹.

The output is the *actual* UniformCoefficientBudget structure;
therefore the existing theorems prove summability of the infinite
normalized complex recurrence series at this radius. This is a
constructive, conservative certificate for a specific recurrence,
not a generic guarantee from an arbitrary finite jet.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- Factorial growth implies the normalized recurrence coefficient at
radius R has absolute value at most the R-geometric term. -/
theorem hurwitzRec_normalized_norm_le_geometric
    (a : ℂ) (ha : ‖a‖ ≤ 1) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ‖hurwitzRecCoeff a n * (R : ℂ)^n /
        (n.factorial : ℂ)‖ ≤ R^n := by
  have hc := hurwitzRecCoeff_norm_factorial a ha n
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hpow : 0 ≤ R^n := pow_nonneg hR _
  have hnorm :
      ‖hurwitzRecCoeff a n * (R : ℂ)^n /
          (n.factorial : ℂ)‖ =
        ‖hurwitzRecCoeff a n‖ * R^n /
          (n.factorial : ℝ) := by
    rw [norm_div, norm_mul, norm_pow]
    simp [Complex.norm_real, abs_of_nonneg hR]
  rw [hnorm]
  calc
    ‖hurwitzRecCoeff a n‖ * R^n / (n.factorial : ℝ) ≤
        (n.factorial : ℝ) * R^n / (n.factorial : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc hpow) hfpos.le
    _ = R^n := by
      field_simp

/-- Actual uniform budget for ALL orders of the complex recurrence,
explicitly constructed from ‖a‖ ≤ 1 and the radius 0≤R<1.

The geometric coefficient bound is proved by recurrence induction;
the series budget is then a proved geometric sum, not an input oracle. -/
noncomputable def hurwitzRec_constructiveBudget
    (a : ℂ) (ha : ‖a‖ ≤ 1)
    (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    UniformCoefficientBudget
      (fun n : ℕ => hurwitzRecCoeff a n * (R : ℂ)^n /
        (n.factorial : ℂ)) where
  bound := (1-R)⁻¹
  all_partial := by
    intro M
    have hgeom : Summable (fun n : ℕ => R ^ n) :=
      summable_geometric_of_lt_one hR hR1
    calc
      (∑ n ∈ Finset.Icc 0 M,
        ‖hurwitzRecCoeff a n * (R : ℂ)^n /
          (n.factorial : ℂ)‖) ≤
          ∑ n ∈ Finset.Icc 0 M, R^n := by
            apply Finset.sum_le_sum
            intro n hn
            exact hurwitzRec_normalized_norm_le_geometric a ha R hR n
      _ ≤ ∑' n : ℕ, R^n :=
        hgeom.sum_le_tsum _ (fun n hn => pow_nonneg hR _)
      _ = (1-R)⁻¹ := tsum_geometric_of_lt_one hR hR1

/-- The actual infinite normalized recurrence series is absolutely
summable for every radius 0 ≤ R < 1, without supplying a separate
majorant. -/
theorem hurwitzRec_summable_at_radius
    (a : ℂ) (ha : ‖a‖ ≤ 1)
    (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    Summable (fun n : ℕ =>
      hurwitzRecCoeff a n * (R : ℂ)^n /
        (n.factorial : ℂ)) :=
  (hurwitzRec_constructiveBudget a ha R hR hR1).summable_coeff _

#print axioms hurwitzRec_constructiveBudget
#print axioms hurwitzRec_summable_at_radius

end CNRSProblem2
