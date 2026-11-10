import CNRSProblem2.HurwitzClosedForm
import Mathlib.Tactic

/-!
# CNRS-H: normalized formal power series satisfies the recurrence ODE

This module proves the exact coefficient-level equation underlying the
generating function, without presupposing any analytic closed form.
The recurrence holds for every complex parameter, and the canonical
RAValue embedding is a specialization.
-/

namespace CNRSProblem2.HurwitzClosedForm

open CNRSProblem2 PowerSeries

/-- Normalized exact recurrence as a formal series in X. -/
noncomputable def recurrenceSeries (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => hurwitzRecCoeff a n / (n.factorial : ℂ))

@[simp] theorem recurrenceSeries_coeff (a : ℂ) (n : ℕ) :
    PowerSeries.coeff n (recurrenceSeries a) =
      hurwitzRecCoeff a n / (n.factorial : ℂ) := rfl

@[simp] theorem recurrenceSeries_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff (recurrenceSeries a) = 1 := by
  simp [recurrenceSeries, hurwitzRecCoeff]

/-- Normalized (complex) coefficient recurrence corresponding to
Y'=(a+X)Y. -/
theorem normalized_step (a : ℂ) (n : ℕ) :
    ((n : ℂ) + 2) *
      (hurwitzRecCoeff a (n + 2) / ((n + 2).factorial : ℂ)) =
    a * (hurwitzRecCoeff a (n + 1) / ((n + 1).factorial : ℂ)) +
      hurwitzRecCoeff a n / (n.factorial : ℂ) := by
  rw [hurwitzRecCoeff_succ_succ]
  have h1 : ((n + 2).factorial : ℂ) =
      ((n : ℂ) + 2) * ((n + 1).factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h2 : ((n + 1).factorial : ℂ) =
      ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hf : (n.factorial : ℂ) ≠ 0 := by positivity
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by positivity
  rw [h1, h2]
  push_cast
  field_simp
  ring

/-- The exact normalized recurrence satisfies the formal ODE in the
power-series ring. -/
theorem recurrenceSeries_derivative (a : ℂ) :
    PowerSeries.derivative ℂ (recurrenceSeries a) =
      (PowerSeries.C a + PowerSeries.X) * recurrenceSeries a := by
  ext n
  cases n with
  | zero =>
      simp [recurrenceSeries, PowerSeries.coeff_derivative,
        add_mul, PowerSeries.coeff_zero_X_mul]
  | succ n =>
      have hrec := normalized_step a n
      simp only [PowerSeries.coeff_derivative, add_mul,
        PowerSeries.coeff_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, recurrenceSeries_coeff]
      push_cast
      convert hrec using 1 <;> ring

#print axioms normalized_step
#print axioms recurrenceSeries_derivative

end CNRSProblem2.HurwitzClosedForm
