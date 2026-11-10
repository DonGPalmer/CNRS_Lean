import CNRSProblem2.HurwitzBudgetBridge
import Mathlib.Tactic

/-!
# CNRS-H: exact recurrence carrier and coefficientwise growth

The recurrence c₀=1, c₁=a, c_(n+2)=a c_(n+1)+(n+1)c_n
is defined over any semiring, hence also over the exact CNRS-A coefficient
ring RAValue. No floating-point oracle or truncation length enters its
definition.

A companion comparison theorem controls the complex recurrence by a
nonnegative real recurrence with parameter ‖a‖. The final all-index
summation of that majorant (exponential generating function) is not proved
by this module.
-/

namespace CNRSProblem2

/-- Adjacent values of a second-order Hurwitz coefficient recurrence. -/
def hurwitzRecState {A : Type*} [Semiring A] (a : A) : ℕ → A × A
  | 0 => (1, a)
  | n + 1 =>
      let p := hurwitzRecState a n
      (p.2, a * p.2 + (↑(n + 1) : A) * p.1)

/-- Exact coefficient at any order; available over RAValue. -/
def hurwitzRecCoeff {A : Type*} [Semiring A] (a : A) (n : ℕ) : A :=
  (hurwitzRecState a n).1

@[simp] theorem hurwitzRecCoeff_zero {A : Type*} [Semiring A] (a : A) :
    hurwitzRecCoeff a 0 = 1 := rfl

@[simp] theorem hurwitzRecCoeff_one {A : Type*} [Semiring A] (a : A) :
    hurwitzRecCoeff a 1 = a := by
  simp [hurwitzRecCoeff, hurwitzRecState]

/-- Exact recurrence over any coefficient semiring, including RAValue. -/
theorem hurwitzRecCoeff_succ_succ {A : Type*} [Semiring A]
    (a : A) (n : ℕ) :
    hurwitzRecCoeff a (n + 2) =
      a * hurwitzRecCoeff a (n + 1) +
        (↑(n + 1) : A) * hurwitzRecCoeff a n := by
  rfl

/-- Exact CNRS-A recurrence coefficients without any complex conversion.
The parameter may in particular be the exact value β⁻¹. -/
noncomputable def exactHurwitzRecCoeff (a : RAValue) (n : ℕ) : RAValue :=
  hurwitzRecCoeff a n

/-- The canonical exact CNRS coefficient β⁻¹ belongs to R_A by the
finite Laurent localization definition. No approximate complex value enters. -/
noncomputable def betaInverseExact : RAValue :=
  ⟨(1 : CnrsQ2.GaussianFrac) / CnrsQ2.betaFrac,
    ⟨(1 : GaussianInt), 1, by simp⟩⟩

/-- The canonical second-order CNRS-H example, as an exact R_A sequence. -/
noncomputable def betaHurwitzCoeff (n : ℕ) : RAValue :=
  exactHurwitzRecCoeff betaInverseExact n

@[simp] theorem betaHurwitzCoeff_zero : betaHurwitzCoeff 0 = 1 := rfl

@[simp] theorem betaHurwitzCoeff_one :
    betaHurwitzCoeff 1 = betaInverseExact := by
  simp [betaHurwitzCoeff, exactHurwitzRecCoeff]

/-- The exact CNRS-H recurrence with β⁻¹, valid at every order. -/
theorem betaHurwitzCoeff_recurrence (n : ℕ) :
    betaHurwitzCoeff (n + 2) =
      betaInverseExact * betaHurwitzCoeff (n + 1) +
        (↑(n + 1) : RAValue) * betaHurwitzCoeff n := by
  exact hurwitzRecCoeff_succ_succ betaInverseExact n

/-- For complex coefficients, every recurrence value is dominated by
the companion nonnegative real recurrence. -/
theorem hurwitzRecCoeff_norm_majorized (a : ℂ) (n : ℕ) :
    ‖hurwitzRecCoeff a n‖ ≤ hurwitzRecCoeff (‖a‖ : ℝ) n := by
  have hstate : ∀ n : ℕ,
      ‖(hurwitzRecState a n).1‖ ≤
        (hurwitzRecState (‖a‖ : ℝ) n).1 ∧
      ‖(hurwitzRecState a n).2‖ ≤
        (hurwitzRecState (‖a‖ : ℝ) n).2 ∧
      0 ≤ (hurwitzRecState (‖a‖ : ℝ) n).1 ∧
      0 ≤ (hurwitzRecState (‖a‖ : ℝ) n).2 := by
    intro n
    induction n with
    | zero =>
        simp [hurwitzRecState, norm_nonneg]
    | succ n ih =>
        rcases ih with ⟨h1, h2, hn1, hn2⟩
        have hc : hurwitzRecState a (n + 1) =
            ((hurwitzRecState a n).2,
             a * (hurwitzRecState a n).2 +
               (↑(n + 1) : ℂ) * (hurwitzRecState a n).1) := rfl
        have hr : hurwitzRecState (‖a‖ : ℝ) (n + 1) =
            ((hurwitzRecState (‖a‖ : ℝ) n).2,
             ‖a‖ * (hurwitzRecState (‖a‖ : ℝ) n).2 +
               (↑(n + 1) : ℝ) *
                 (hurwitzRecState (‖a‖ : ℝ) n).1) := rfl
        rw [hc, hr]
        refine ⟨h2, ?_, hn2, ?_⟩
        · calc
            ‖a * (hurwitzRecState a n).2 +
                (↑(n + 1) : ℂ) * (hurwitzRecState a n).1‖ ≤
              ‖a‖ * ‖(hurwitzRecState a n).2‖ +
                (↑(n + 1) : ℝ) * ‖(hurwitzRecState a n).1‖ := by
                  calc
                    _ ≤ ‖a * (hurwitzRecState a n).2‖ +
                        ‖(↑(n + 1) : ℂ) *
                          (hurwitzRecState a n).1‖ :=
                      norm_add_le _ _
                    _ = _ := by
                        simp only [norm_mul]
                        rw [Complex.norm_natCast]
            _ ≤ ‖a‖ * (hurwitzRecState (‖a‖ : ℝ) n).2 +
                (↑(n + 1) : ℝ) *
                  (hurwitzRecState (‖a‖ : ℝ) n).1 := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left h2 (norm_nonneg a))
                      (mul_le_mul_of_nonneg_left h1 (by positivity))
        · exact add_nonneg (mul_nonneg (norm_nonneg _) hn2)
            (mul_nonneg (by positivity) hn1)
  exact (hstate n).1

#print axioms hurwitzRecCoeff_succ_succ
#print axioms hurwitzRecCoeff_norm_majorized

end CNRSProblem2
