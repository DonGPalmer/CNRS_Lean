import CNRSProblem2.HurwitzBlockDecay
import Mathlib.Tactic

/-!
# Uniform factorial growth bound for the exact CNRS-H recurrence

For any complex a with ‖a‖ ≤ 1, the exact second-order Hurwitz
recurrence has ‖c_n‖ ≤ n!. The proof is an induction on two consecutive
state coordinates, not a numerical or finite-order assertion.

The result gives an analytically certified geometric majorant on any
closed radius R < 1 once the normalized coefficients are formed.
-/

namespace CNRSProblem2

/-- An exact all-order factorial bound on both adjacent recurrence
coordinates. -/
theorem hurwitzRecState_norm_factorial (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ∀ n : ℕ,
      ‖(hurwitzRecState a n).1‖ ≤ (n.factorial : ℝ) ∧
      ‖(hurwitzRecState a n).2‖ ≤ ((n + 1).factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      simp [hurwitzRecState, ha]
  | succ n ih =>
      rcases ih with ⟨hfirst, hsecond⟩
      have hbound : 2 * (((n + 1).factorial : ℕ) : ℝ) ≤
          (((n + 2).factorial : ℕ) : ℝ) := by
        have hcast : (2 : ℝ) ≤ (n + 2 : ℝ) := by
          exact_mod_cast (show 2 ≤ n + 2 by omega)
        have hnonneg : 0 ≤ (((n + 1).factorial : ℕ) : ℝ) := by positivity
        have hf : (((n + 2).factorial : ℕ) : ℝ) =
          (n + 2 : ℝ) * (((n + 1).factorial : ℕ) : ℝ) := by
            rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
            push_cast
            ring
        rw [hf]
        exact mul_le_mul_of_nonneg_right hcast hnonneg
      change
        ‖(hurwitzRecState a n).2‖ ≤
            (((n + 1).factorial : ℕ) : ℝ) ∧
        ‖a * (hurwitzRecState a n).2 +
            (↑(n + 1) : ℂ) * (hurwitzRecState a n).1‖ ≤
            (((n + 2).factorial : ℕ) : ℝ)
      constructor
      · exact hsecond
      · have hnorm :
          ‖a * (hurwitzRecState a n).2 +
            (↑(n + 1) : ℂ) * (hurwitzRecState a n).1‖ ≤
              ‖a‖ * ‖(hurwitzRecState a n).2‖ +
                (n + 1 : ℝ) * ‖(hurwitzRecState a n).1‖ := by
            calc
              _ ≤ ‖a * (hurwitzRecState a n).2‖ +
                ‖(↑(n + 1) : ℂ) * (hurwitzRecState a n).1‖ :=
                  norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul, Complex.norm_natCast]
        have ha' : ‖a‖ * ‖(hurwitzRecState a n).2‖ ≤
            (((n + 1).factorial : ℕ) : ℝ) := by
          calc
            _ ≤ 1 * ‖(hurwitzRecState a n).2‖ :=
              mul_le_mul_of_nonneg_right ha (norm_nonneg _)
            _ = ‖(hurwitzRecState a n).2‖ := one_mul _
            _ ≤ _ := hsecond
        have hmul : (n + 1 : ℝ) * ‖(hurwitzRecState a n).1‖ ≤
            (((n + 1).factorial : ℕ) : ℝ) := by
          calc
            _ ≤ (n + 1 : ℝ) * (n.factorial : ℝ) :=
              mul_le_mul_of_nonneg_left hfirst (by positivity)
            _ = (((n + 1).factorial : ℕ) : ℝ) := by
              rw [Nat.factorial_succ]
              push_cast
              ring
        exact hnorm.trans ((add_le_add ha' hmul).trans hbound)

/-- Every coefficient in the complex recurrence obeys a factorial
majorant. This includes any a with norm at most one. -/
theorem hurwitzRecCoeff_norm_factorial (a : ℂ)
    (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖hurwitzRecCoeff a n‖ ≤ (n.factorial : ℝ) :=
  (hurwitzRecState_norm_factorial a ha n).1

#print axioms hurwitzRecCoeff_norm_factorial

end CNRSProblem2
