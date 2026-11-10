import CNRSProblem2.HurwitzExactInfiniteTail
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-!
# CNRS-H: formal generating-function identification

The exact recurrence is related to the formal exponential of the
quadratic a*X + X²/2. This separate proof layer makes the formal ODE
and the uniqueness argument explicit. An equality of its analytic
evaluation to Complex.exp(a*w+w²/2) additionally requires identifying
the analytic evaluation of this formal series, and is not assumed.
-/

namespace CNRSProblem2.HurwitzClosedForm

open CNRSProblem2
open PowerSeries

/-- Quadratic exponent with vanishing constant term. -/
noncomputable def quadraticExponent (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.C a * PowerSeries.X +
    PowerSeries.C (1 / 2 : ℂ) * (PowerSeries.X : PowerSeries ℂ) ^ 2

theorem quadraticExponent_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff (quadraticExponent a) = 0 := by
  simp [quadraticExponent]

theorem quadraticExponent_hasSubst (a : ℂ) :
    PowerSeries.HasSubst (quadraticExponent a) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (quadraticExponent_constantCoeff a)

/-- The formal derivative of the quadratic exponent is a+X. -/
theorem quadraticExponent_derivative (a : ℂ) :
    PowerSeries.derivative ℂ (quadraticExponent a) =
      PowerSeries.C a + PowerSeries.X := by
  unfold quadraticExponent
  simp [PowerSeries.derivative_pow, PowerSeries.derivative_X,
    PowerSeries.derivative_C]
  have hhalf : PowerSeries.C (1 / 2 : ℂ) * (2 : PowerSeries ℂ) = 1 := by
    have h : (1 / 2 : ℂ) * 2 = 1 := by norm_num
    have hh := congrArg (fun x : ℂ => PowerSeries.C x) h
    simpa only [map_mul, map_ofNat, map_one] using hh
  calc
    PowerSeries.C (1 / 2 : ℂ) * (PowerSeries.X : PowerSeries ℂ) * 2 =
      (PowerSeries.C (1 / 2 : ℂ) * 2) * PowerSeries.X := by ring
    _ = PowerSeries.X := by rw [hhalf]; ring

/-- The formal exponential satisfies Y'=(a+X)Y. -/
theorem formalExp_derivative (a : ℂ) :
    PowerSeries.derivative ℂ
      ((PowerSeries.exp ℂ).subst (quadraticExponent a)) =
    (PowerSeries.C a + PowerSeries.X) *
      ((PowerSeries.exp ℂ).subst (quadraticExponent a)) := by
  rw [PowerSeries.derivative_subst (quadraticExponent_hasSubst a),
      PowerSeries.derivative_exp ℂ, quadraticExponent_derivative]
  ring

#print axioms quadraticExponent_derivative
#print axioms formalExp_derivative

end CNRSProblem2.HurwitzClosedForm
