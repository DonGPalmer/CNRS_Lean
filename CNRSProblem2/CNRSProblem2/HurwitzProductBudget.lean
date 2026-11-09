import CNRSProblem2.HurwitzConvolutionNorm
import Mathlib.Tactic

/-!
# CNRS-H: independently justified finite weighted product budgets

A numerical bound is an analytic certificate only if accompanied by proof
that it dominates the actual finite-support weighted norm.  These declarations
compose two such certificates without manufacturing a bound from a finite jet
of an unrelated, potentially infinite series.

This module is stacked on the still-unverified aggregate product norm module;
its own CI must compile that dependency. It asserts no infinite summability.
-/

namespace CNRSProblem2

/-- A finite-support weighted norm bound packaged with its mathematical
justification. It is not an unconstrained user-provided floating-point claim. -/
structure FiniteHurwitzBudget (R : ℝ) (x : FiniteHurwitz ℂ) where
  bound : ℝ
  valid : finiteHurwitzWeightedNorm R x ≤ bound

/-- A certified budget cannot be negative at nonnegative radius. -/
theorem FiniteHurwitzBudget.bound_nonneg
    (R : ℝ) (hR : 0 ≤ R) (x : FiniteHurwitz ℂ)
    (cert : FiniteHurwitzBudget R x) : 0 ≤ cert.bound :=
  le_trans (finiteHurwitzWeightedNorm_nonneg R hR x) cert.valid

/-- Composition of independently justified finite input budgets:
the resulting product bound is proved, not inferred from sample coefficients. -/
def FiniteHurwitzBudget.mul
    (R : ℝ) (hR : 0 ≤ R)
    (x y : FiniteHurwitz ℂ)
    (cx : FiniteHurwitzBudget R x)
    (cy : FiniteHurwitzBudget R y) :
    FiniteHurwitzBudget R (x * y) where
  bound := cx.bound * cy.bound
  valid := by
    calc
      finiteHurwitzWeightedNorm R (x * y) ≤
          finiteHurwitzWeightedNorm R x *
          finiteHurwitzWeightedNorm R y :=
        finiteHurwitzWeightedNorm_mul_le R hR x y
      _ ≤ cx.bound * cy.bound := by
        exact mul_le_mul cx.valid cy.valid
          (finiteHurwitzWeightedNorm_nonneg R hR y)
          (cx.bound_nonneg R hR x)

end CNRSProblem2
