import CNRSProblem2.HurwitzConstructiveBudget
import CNRSProblem2.HurwitzRecurrenceGrowth
import CNRSProblem2.FiniteLaurentValueCodec
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# CNRS-H exact-to-analytic coefficient bridge

Based on the independently compiled 2026-11-09 Formal Methods review
LEAN_PR_Evidence4_20261109.md, section 8 (Rev15). The base map,
beta identity and recurrence naturality were previously compiled in
a pinned Lean environment. This module installs those arguments as
governed development source and constructs an explicit certificate
for the exact canonical recurrence at R = 3/4.

The theorem never treats a generic finite jet as a global majorant.
-/

open CNRSProblem2

namespace CNRSProblem2.HurwitzExactBridge

/-- Fraction field of the Gaussian integers into the complex field,
extending the standard Gaussian-integer embedding. -/
noncomputable def toC : CnrsQ2.GaussianFrac →+* ℂ :=
  IsFractionRing.lift (A := GaussianInt) (g := GaussianInt.toComplex)
    GaussianInt.toComplex_injective

/-- Explicit ring homomorphism of the governed exact coefficient carrier
into the complex analytic coefficient field. -/
noncomputable def raToC : RAValue →+* ℂ :=
  toC.comp finiteLaurentSubring.subtype

/-- The exact radix beta maps to the complex number -2+i. -/
theorem toC_betaFrac :
    toC CnrsQ2.betaFrac = (-2 : ℂ) + Complex.I := by
  unfold toC CnrsQ2.betaFrac
  rw [IsFractionRing.lift_algebraMap]
  have : (CnrsQ2.beta : GaussianInt) = ⟨-2, 1⟩ := rfl
  rw [this, GaussianInt.toComplex_def']
  push_cast
  ring

/-- Every second-order recurrence coefficient is natural under ring maps. -/
theorem hurwitzRecState_map {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (a : A) (n : ℕ) :
    hurwitzRecState (f a) n =
      ((hurwitzRecState a n).1 |> f, (hurwitzRecState a n).2 |> f) := by
  induction n with
  | zero => simp [hurwitzRecState]
  | succ n ih =>
      simp only [hurwitzRecState, ih, map_add, map_mul, map_natCast]

theorem map_hurwitzRecCoeff {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (a : A) (n : ℕ) :
    f (hurwitzRecCoeff a n) = hurwitzRecCoeff (f a) n := by
  unfold hurwitzRecCoeff
  rw [hurwitzRecState_map f a n]

/-- The canonical exact beta inverse maps to the correct complex inverse. -/
theorem raToC_betaInverseExact :
    raToC betaInverseExact = ((-2 : ℂ) + Complex.I)⁻¹ := by
  unfold raToC
  show toC ((1 : CnrsQ2.GaussianFrac) / CnrsQ2.betaFrac) = _
  rw [map_div₀, map_one, toC_betaFrac, one_div]

/-- The complex canonical parameter has small norm, as required by the
already verified constructive factorial coefficient majorant. -/
theorem norm_betaInverse_le :
    ‖((-2 : ℂ) + Complex.I)⁻¹‖ ≤ (1 / 2 : ℝ) := by
  rw [norm_inv]
  have h : (2 : ℝ) ≤ ‖(-2 : ℂ) + Complex.I‖ := by
    have := Complex.abs_re_le_norm ((-2 : ℂ) + Complex.I)
    simpa using this
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

/-- Exact recurrence and complex recurrence agree at every order. -/
theorem raToC_betaHurwitzCoeff (n : ℕ) :
    raToC (betaHurwitzCoeff n) =
      hurwitzRecCoeff (((-2 : ℂ) + Complex.I)⁻¹) n := by
  unfold betaHurwitzCoeff exactHurwitzRecCoeff
  rw [map_hurwitzRecCoeff, raToC_betaInverseExact]

/-- End-to-end explicit all-order certificate for the canonical exact CNRS
recurrence, evaluated at radius 3/4, with rigorous budget 4. -/
noncomputable def betaExactBudget :
    UniformCoefficientBudget
      (fun n : ℕ => raToC (betaHurwitzCoeff n) *
        ((3 / 4 : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) where
  bound := 4
  all_partial := by
    intro M
    have ha : ‖((-2 : ℂ) + Complex.I)⁻¹‖ ≤ 1 :=
      (norm_betaInverse_le).trans (by norm_num)
    have hcert :=
      (hurwitzRec_constructiveBudget
        (((-2 : ℂ) + Complex.I)⁻¹) ha
        (3 / 4 : ℝ) (by norm_num) (by norm_num)).all_partial M
    have hbound : (1 - (3 / 4 : ℝ))⁻¹ = 4 := by norm_num
    rw [hbound] at hcert
    simpa only [raToC_betaHurwitzCoeff] using hcert

/-- Infinite series of the exact coefficient sequence is certified to
converge after its algebraic realization in the complex field. -/
theorem betaExactSummable :
    Summable (fun n : ℕ => raToC (betaHurwitzCoeff n) *
      ((3 / 4 : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) :=
  betaExactBudget.summable_coeff _

#print axioms toC_betaFrac
#print axioms raToC_betaInverseExact
#print axioms raToC_betaHurwitzCoeff
#print axioms betaExactBudget
#print axioms betaExactSummable

end CNRSProblem2.HurwitzExactBridge
