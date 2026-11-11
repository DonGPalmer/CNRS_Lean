import CNRSProblem2.HurwitzFormalRecurrence
import Mathlib.Tactic

/-!
# CNRS-H formal generating-function uniqueness

In characteristic zero, a formal series with constant coefficient one
and differential equation Y'=(a+X)Y is unique. Hence the normalized
CNRS-H recurrence series equals the formal exponential obtained by
substituting the quadratic exponent aX+X²/2 into the exponential
power series.

This is a genuine *formal power series identity* over ℂ, independent
of numerical sampling. Evaluation as the complex entire function is
a distinct analytic-bridge statement, not assumed here.
-/

namespace CNRSProblem2.HurwitzClosedForm
open CNRSProblem2 PowerSeries

/-- A formal solution's first coefficient is forced by Y'=(a+X)Y. -/
theorem ode_coeff_one (a : ℂ) (f : PowerSeries ℂ)
    (hf : PowerSeries.derivative ℂ f =
      (PowerSeries.C a + PowerSeries.X) * f) :
    PowerSeries.coeff 1 f = a * PowerSeries.coeff 0 f := by
  have h := congrArg (PowerSeries.coeff 0) hf
  simpa only [PowerSeries.coeff_derivative, add_mul,
      map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_X_mul, Nat.zero_add,
      Nat.cast_one, mul_one, add_zero] using h

/-- Forced two-step relation for all formal solution coefficients. -/
theorem ode_coeff_step (a : ℂ) (f : PowerSeries ℂ)
    (hf : PowerSeries.derivative ℂ f =
      (PowerSeries.C a + PowerSeries.X) * f)
    (n : ℕ) :
    PowerSeries.coeff (n + 2) f * (n + 2 : ℂ) =
      a * PowerSeries.coeff (n + 1) f + PowerSeries.coeff n f := by
  have h := congrArg (PowerSeries.coeff (n + 1)) hf
  simp only [PowerSeries.coeff_derivative, add_mul,
    map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul] at h
  convert h using 1 <;> push_cast <;> ring

/-- Two solutions with the same constant term have equal coefficients. -/
theorem ode_unique (a : ℂ) (f g : PowerSeries ℂ)
    (hf : PowerSeries.derivative ℂ f =
      (PowerSeries.C a + PowerSeries.X) * f)
    (hg : PowerSeries.derivative ℂ g =
      (PowerSeries.C a + PowerSeries.X) * g)
    (hzero : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) :
    f = g := by
  ext n
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
  | one =>
      calc
        PowerSeries.coeff 1 f = a * PowerSeries.coeff 0 f :=
          ode_coeff_one a f hf
        _ = a * PowerSeries.coeff 0 g := by
          have hc : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g := by
            simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
          rw [hc]
        _ = PowerSeries.coeff 1 g := (ode_coeff_one a g hg).symm
  | more n ih0 ih1 =>
      have hne : (n + 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (n + 1))
      apply (mul_right_cancel₀ hne)
      calc
        PowerSeries.coeff (n + 2) f * (n + 2 : ℂ) =
          a * PowerSeries.coeff (n + 1) f +
            PowerSeries.coeff n f := ode_coeff_step a f hf n
        _ = a * PowerSeries.coeff (n + 1) g +
            PowerSeries.coeff n g := by rw [ih0, ih1]
        _ = PowerSeries.coeff (n + 2) g * (n + 2 : ℂ) :=
          (ode_coeff_step a g hg n).symm

/-- The formally substituted exponential has constant coefficient one. -/
theorem formalExp_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff
      ((PowerSeries.exp ℂ).subst (quadraticExponent a)) = 1 := by
  classical
  rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst (quadraticExponent_hasSubst a),
      finsum_eq_single _ 0 (fun d hd => by
        rw [map_pow, quadraticExponent_constantCoeff, zero_pow hd, smul_zero])]
  simp [Algebra.algebraMap_eq_smul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_exp]

/-- Formal identity: recurrence coefficients divided by n! are exactly
the coefficients of exp(aX+X²/2) as a formal power series. -/
theorem recurrenceSeries_eq_formalExp (a : ℂ) :
    recurrenceSeries a =
      (PowerSeries.exp ℂ).subst (quadraticExponent a) :=
  ode_unique a _ _ (recurrenceSeries_derivative a)
    (formalExp_derivative a)
    ((recurrenceSeries_constantCoeff a).trans
      (formalExp_constantCoeff a).symm)

/-- Exact CNRS-H coefficients (under their proved RAValue→ℂ embedding)
are formally identified with the quadratic exponential series. -/
theorem beta_exact_formal_exp :
    PowerSeries.mk
        (fun n : ℕ => CNRSProblem2.HurwitzExactBridge.raToC
          (CNRSProblem2.betaHurwitzCoeff n) / (n.factorial : ℂ)) =
      (PowerSeries.exp ℂ).subst
        (quadraticExponent (((-2 : ℂ) + Complex.I)⁻¹)) := by
  have h := recurrenceSeries_eq_formalExp
    (((-2 : ℂ) + Complex.I)⁻¹)
  simpa only [recurrenceSeries,
      CNRSProblem2.HurwitzExactBridge.raToC_betaHurwitzCoeff] using h

#print axioms ode_unique
#print axioms recurrenceSeries_eq_formalExp
#print axioms beta_exact_formal_exp

end CNRSProblem2.HurwitzClosedForm
