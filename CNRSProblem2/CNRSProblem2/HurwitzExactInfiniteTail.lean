import CNRSProblem2.HurwitzInfiniteTail
import CNRSProblem2.HurwitzSharpMajorant
import Mathlib.Tactic

/-!
# CNRS-H: actual infinite Taylor/Hurwitz error at every finite radius

Given 0 ≤ r < R, |w| ≤ r, and an arbitrary truncation order N,
the exact RAValue β⁻¹ recurrence, transported through its proved
injective map into ℂ, satisfies

  ‖ ∑' n, c_n w^n / n! - ∑_{n=0}^N c_n w^n / n! ‖
    ≤ exp(R / sqrt(5) + R²/2) * (r/R)^(N+1).

This is an actual infinite tsum minus the finite polynomial, not an
unbounded finite-tail surrogate. It is conditional only on the stated
radius inequalities, with all-index majorant derived from the recurrence.
-/

namespace CNRSProblem2.HurwitzSharp

open CNRSProblem2 CNRSProblem2.HurwitzExactBridge
open scoped BigOperators

/-- The analytic value of the canonical exact CNRS-H recurrence, defined
by its convergent complex power series. -/
noncomputable def betaExactAnalyticValue (w : ℂ) : ℂ :=
  ∑' n : ℕ,
    raToC (betaHurwitzCoeff n) * w ^ n / (n.factorial : ℂ)

/-- The degree-N Taylor/Hurwitz polynomial of the same exact coefficients. -/
noncomputable def betaExactTaylorPolynomial (N : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    raToC (betaHurwitzCoeff n) * w ^ n / (n.factorial : ℂ)

/-- Quantitative bound on the actual infinite analytic truncation error,
uniform over the closed disk |w|≤r<R. -/
theorem betaExact_infinite_tail_le
    (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (w : ℂ) (hw : ‖w‖ ≤ r) (N : ℕ) :
    ‖betaExactAnalyticValue w - betaExactTaylorPolynomial N w‖ ≤
      Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) *
        (r / R) ^ (N + 1) := by
  let z : ℂ := w / (R : ℂ)
  let a : ℕ → ℂ := fun n =>
    raToC (betaHurwitzCoeff n) * (R : ℂ) ^ n /
      (n.factorial : ℂ)
  have hRc : (R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hR)
  have hRnorm : ‖(R : ℂ)‖ = R := by
    simp [Complex.norm_real, abs_of_pos hR]
  have hzNorm : ‖z‖ = ‖w‖ / R := by
    dsimp [z]
    rw [norm_div, hRnorm]
  have hz : ‖z‖ ≤ 1 := by
    rw [hzNorm]
    exact (div_le_one hR).mpr (hw.trans hrR.le)
  have hzRatio : ‖z‖ ≤ r / R := by
    rw [hzNorm]
    exact div_le_div_of_nonneg_right hw hR.le
  have hRz : (R : ℂ) * z = w := by
    dsimp [z]
    field_simp [hRc]
  have hterm (n : ℕ) :
      a n * z ^ n =
        raToC (betaHurwitzCoeff n) * w ^ n /
          (n.factorial : ℂ) := by
    have hpow : (R : ℂ) ^ n * z ^ n = w ^ n := by
      rw [← mul_pow, hRz]
    dsimp [a]
    calc
      (raToC (betaHurwitzCoeff n) * (R : ℂ) ^ n /
          (n.factorial : ℂ)) * z ^ n =
        raToC (betaHurwitzCoeff n) *
          ((R : ℂ) ^ n * z ^ n) / (n.factorial : ℂ) := by ring
      _ = raToC (betaHurwitzCoeff n) * w ^ n /
          (n.factorial : ℂ) := by rw [hpow]
  have hcert : UniformCoefficientBudget a :=
    betaExactSharpBudget R hR.le
  have htail :=
    hcert.infinite_evaluation_tail_le a N z hz
  change _ ≤ ‖z‖ ^ (N + 1) *
    Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) at htail
  have htsum :
      (∑' n : ℕ, a n * z ^ n) =
        betaExactAnalyticValue w := by
    unfold betaExactAnalyticValue
    exact tsum_congr hterm
  have hpref :
      (∑ n ∈ Finset.range (N + 1), a n * z ^ n) =
        betaExactTaylorPolynomial N w := by
    unfold betaExactTaylorPolynomial
    exact Finset.sum_congr rfl (fun n hn => hterm n)
  rw [htsum, hpref] at htail
  have hpowers : ‖z‖ ^ (N + 1) ≤ (r / R) ^ (N + 1) :=
    pow_le_pow_left₀ (norm_nonneg z) hzRatio _
  calc
    ‖betaExactAnalyticValue w - betaExactTaylorPolynomial N w‖ ≤
      ‖z‖ ^ (N + 1) *
        Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) := htail
    _ ≤ (r / R) ^ (N + 1) *
        Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hpowers
        (Real.exp_pos _).le
    _ = Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) *
        (r / R) ^ (N + 1) := by ring

#print axioms betaExact_infinite_tail_le

end CNRSProblem2.HurwitzSharp
