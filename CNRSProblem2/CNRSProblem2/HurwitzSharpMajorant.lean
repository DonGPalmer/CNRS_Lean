import CNRSProblem2.HurwitzExactComplexBridge
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# CNRS-H: independently checked sharp exponential majorant

Adapted verbatim in its proof bodies from the independent Lean companion
P18_sharp.lean, filed in SSC Formal Methods audit evidence
/_SSC/25_Formal Methods/95_Audit/LEAN_PR_Evidence5_20261110.md
(section 6), reviewed in LEAN_PR_Review5_20261110.md. Compiler environment:
Lean 4.33.0; pinned Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Only the module heading and namespace were adapted for the governed repository.

Sharp exponential majorant for the Hurwitz recurrence
  c_0 = 1, c_1 = a, c_(n+2) = a c_(n+1) + (n+1) c_n,
at EVERY radius R >= 0:

  sum_{n <= M} || c_n(a) R^n / n! ||  <=  exp(||a|| R + R^2/2)   for all M.

The proof is by differential inequality (no Cauchy product, no closed form):
with e_n = c_n(r)/n!  (r = ||a||) and S_M(x) = sum_{n<M} e_n x^n one has
  (n+2) e_(n+2) = r e_(n+1) + e_n,   S_(M+2)'(x) = r S_(M+1)(x) + x S_M(x),
hence for x >= 0 the quotient S_(M+2)(x) / exp(r x + x^2/2) is antitone, and
equals 1 at x = 0.
-/

open CNRSProblem2 CNRSProblem2.HurwitzExactBridge

namespace CNRSProblem2.HurwitzSharp

/-! ## Nonnegative real recurrence -/

theorem recState_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ (hurwitzRecState r n).1 ∧ 0 ≤ (hurwitzRecState r n).2 := by
  induction n with
  | zero => simp [hurwitzRecState, hr]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      show 0 ≤ r * (hurwitzRecState r n).2 +
        ((n + 1 : ℕ) : ℝ) * (hurwitzRecState r n).1
      exact add_nonneg (mul_nonneg hr h2) (mul_nonneg (by positivity) h1)

theorem rec_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ hurwitzRecCoeff r n :=
  (recState_nonneg hr n).1

/-- Normalized real coefficient c_n(r)/n!. -/
noncomputable def e (r : ℝ) (n : ℕ) : ℝ :=
  hurwitzRecCoeff r n / (n.factorial : ℝ)

theorem e_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ e r n :=
  div_nonneg (rec_nonneg hr n) (by positivity)

theorem e_zero (r : ℝ) : e r 0 = 1 := by simp [e]

theorem e_one (r : ℝ) : e r 1 = r := by simp [e]

/-- The normalized recurrence: (n+2) e_(n+2) = r e_(n+1) + e_n. -/
theorem e_rec (r : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * e r (n + 2) = r * e r (n + 1) + e r n := by
  unfold e
  rw [hurwitzRecCoeff_succ_succ]
  have h1 : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [h1, h2]
  push_cast
  field_simp

/-! ## Partial sums and their derivative -/

noncomputable def S (r : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, e r n * x ^ n

theorem S_succ (r : ℝ) (M : ℕ) (x : ℝ) :
    S r (M + 1) x = S r M x + e r M * x ^ M := by
  simp only [S]
  rw [Finset.sum_range_succ]

theorem S_nonneg {r : ℝ} (hr : 0 ≤ r) (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ S r M x := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (e_nonneg hr n) (pow_nonneg hx n)

theorem S_le_succ {r : ℝ} (hr : 0 ≤ r) (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    S r M x ≤ S r (M + 1) x := by
  rw [S_succ]
  have : 0 ≤ e r M * x ^ M := mul_nonneg (e_nonneg hr M) (pow_nonneg hx M)
  linarith

theorem S_mono {r : ℝ} (hr : 0 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun M => S r M x) :=
  monotone_nat_of_le_succ (fun M => S_le_succ hr M hx)

theorem S_succ_at_zero (r : ℝ) (M : ℕ) : S r (M + 1) 0 = 1 := by
  induction M with
  | zero => simp [S, e_zero]
  | succ M ih =>
      rw [S_succ, ih]
      simp

theorem S_hasDerivAt (r : ℝ) (M : ℕ) (x : ℝ) :
    HasDerivAt (fun y => S r (M + 2) y)
      (r * S r (M + 1) x + x * S r M x) x := by
  induction M with
  | zero =>
      have hfun : (fun y => S r (0 + 2) y) = fun y => 1 + r * y := by
        funext y
        simp [S, Finset.sum_range_succ, e_zero, e_one]
      rw [hfun]
      have h := ((hasDerivAt_id' (x := x)).const_mul r).const_add 1
      refine h.congr_deriv ?_
      simp [S, e_zero]
  | succ M ih =>
      have hfun : (fun y => S r (M + 1 + 2) y) =
          fun y => S r (M + 2) y + e r (M + 2) * y ^ (M + 2) := by
        funext y
        exact S_succ r (M + 2) y
      rw [hfun]
      have hp := (hasDerivAt_pow (M + 2) x).const_mul (e r (M + 2))
      have h : HasDerivAt
          (fun y => S r (M + 2) y + e r (M + 2) * y ^ (M + 2))
          (r * S r (M + 1) x + x * S r M x +
            e r (M + 2) * (((M + 2 : ℕ) : ℝ) * x ^ (M + 2 - 1))) x :=
        ih.add hp
      refine h.congr_deriv ?_
      have hrec := e_rec r M
      have hS1 : S r (M + 1 + 1) x =
          S r (M + 1) x + e r (M + 1) * x ^ (M + 1) := S_succ r (M + 1) x
      have hS0 : S r (M + 1) x = S r M x + e r M * x ^ M := S_succ r M x
      have hpow : (M + 2 - 1 : ℕ) = M + 1 := rfl
      rw [hS1, hS0, hpow]
      push_cast
      linear_combination (x ^ (M + 1)) * hrec

/-! ## The differential-inequality step -/

theorem S_two_le_exp {r : ℝ} (hr : 0 ≤ r) (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    S r (M + 2) x ≤ Real.exp (r * x + x ^ 2 / 2) := by
  let Φ : ℝ → ℝ := fun y => Real.exp (-(r * y + y ^ 2 / 2)) * S r (M + 2) y
  have hexp : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-(r * y + y ^ 2 / 2)))
      (Real.exp (-(r * y + y ^ 2 / 2)) * (-(r + y))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => r * y + y ^ 2 / 2) (r + y) y := by
      have := ((hasDerivAt_id' (x := y)).const_mul r).add
        ((hasDerivAt_pow 2 y).div_const 2)
      refine this.congr_deriv ?_
      norm_num
    exact h1.neg.exp
  have hΦ : ∀ y : ℝ, HasDerivAt Φ
      (Real.exp (-(r * y + y ^ 2 / 2)) *
        ((r * S r (M + 1) y + y * S r M y) - (r + y) * S r (M + 2) y)) y := by
    intro y
    have := (hexp y).mul (S_hasDerivAt r M y)
    refine this.congr_deriv ?_
    ring
  have hanti : AntitoneOn Φ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun y _ => (hΦ y).continuousAt.continuousWithinAt
    · exact fun y _ => (hΦ y).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 < y := by simpa using hy
      rw [(hΦ y).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have h1 : S r M y ≤ S r (M + 2) y := S_mono hr hy0.le (by omega)
      have h2 : S r (M + 1) y ≤ S r (M + 2) y := S_mono hr hy0.le (by omega)
      nlinarith [mul_le_mul_of_nonneg_left h1 hy0.le,
                 mul_le_mul_of_nonneg_left h2 hr]
  have hle : Φ x ≤ Φ 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hΦ0 : Φ 0 = 1 := by
    simp only [Φ]
    rw [show (M + 2 : ℕ) = (M + 1) + 1 from rfl, S_succ_at_zero]
    simp
  rw [hΦ0] at hle
  simp only [Φ] at hle
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one] at hle
  exact hle

/-- All partial sums of the normalized majorant series are below the
exponential, at every radius x >= 0. -/
theorem S_le_exp {r : ℝ} (hr : 0 ≤ r) (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    S r M x ≤ Real.exp (r * x + x ^ 2 / 2) :=
  (S_mono hr hx (by omega : M ≤ M + 2)).trans (S_two_le_exp hr M hx)

/-! ## Complex-parameter budget at every radius -/

theorem norm_term (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ‖hurwitzRecCoeff a n * (R : ℂ) ^ n / (n.factorial : ℂ)‖ =
      ‖hurwitzRecCoeff a n‖ * R ^ n / (n.factorial : ℝ) := by
  rw [norm_div, norm_mul, norm_pow]
  simp [Complex.norm_real, abs_of_nonneg hR]

theorem term_le_e (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ‖hurwitzRecCoeff a n * (R : ℂ) ^ n / (n.factorial : ℂ)‖ ≤
      e ‖a‖ n * R ^ n := by
  rw [norm_term a hR n]
  unfold e
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hurwitzRecCoeff_norm_majorized a n) (pow_nonneg hR n))
    hf.le

theorem Icc_sum_eq_S (r R : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 0 M, e r n * R ^ n = S r (M + 1) R := by
  have : Finset.Icc 0 M = Finset.range (M + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [this]; rfl

/-- Sharp all-radius budget for the complex recurrence with parameter a. -/
noncomputable def hurwitzRec_sharpBudget (a : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    UniformCoefficientBudget
      (fun n : ℕ => hurwitzRecCoeff a n * (R : ℂ) ^ n / (n.factorial : ℂ)) where
  bound := Real.exp (‖a‖ * R + R ^ 2 / 2)
  all_partial := by
    intro M
    calc
      (∑ n ∈ Finset.Icc 0 M,
          ‖hurwitzRecCoeff a n * (R : ℂ) ^ n / (n.factorial : ℂ)‖)
          ≤ ∑ n ∈ Finset.Icc 0 M, e ‖a‖ n * R ^ n :=
            Finset.sum_le_sum (fun n _ => term_le_e a hR n)
      _ = S ‖a‖ (M + 1) R := Icc_sum_eq_S _ _ M
      _ ≤ Real.exp (‖a‖ * R + R ^ 2 / 2) := S_le_exp (norm_nonneg a) (M + 1) hR

/-! ## The canonical exact recurrence, via the PR #18 embedding -/

theorem norm_beta_ne : ‖(-2 : ℂ) + Complex.I‖ = Real.sqrt 5 := by
  have h : ‖(-2 : ℂ) + Complex.I‖ ^ 2 = 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem norm_betaInv : ‖((-2 : ℂ) + Complex.I)⁻¹‖ = (Real.sqrt 5)⁻¹ := by
  rw [norm_inv, norm_beta_ne]

/-- HEADLINE.  For every radius R >= 0, an all-index
`UniformCoefficientBudget` for the exact canonical CNRS-H recurrence
(RAValue coefficients, transported by the PR #18 embedding `raToC`),
with the exponential bound exp(R/sqrt 5 + R^2/2). -/
noncomputable def betaExactSharpBudget (R : ℝ) (hR : 0 ≤ R) :
    UniformCoefficientBudget
      (fun n : ℕ => raToC (betaHurwitzCoeff n) * ((R : ℝ) : ℂ) ^ n /
        (n.factorial : ℂ)) where
  bound := Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2)
  all_partial := by
    intro M
    have h := (hurwitzRec_sharpBudget (((-2 : ℂ) + Complex.I)⁻¹) R hR).all_partial M
    change _ ≤ Real.exp (‖((-2 : ℂ) + Complex.I)⁻¹‖ * R + R ^ 2 / 2) at h
    rw [norm_betaInv] at h
    simpa only [raToC_betaHurwitzCoeff] using h

theorem betaExactSharpSummable (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => raToC (betaHurwitzCoeff n) * ((R : ℝ) : ℂ) ^ n /
      (n.factorial : ℂ)) :=
  (betaExactSharpBudget R hR).summable_coeff _

/-- The sum of norms is bounded by the exponential (tsum form). -/
theorem betaExactSharp_tsum_le (R : ℝ) (hR : 0 ≤ R) :
    ∑' n : ℕ, ‖raToC (betaHurwitzCoeff n) * ((R : ℝ) : ℂ) ^ n /
        (n.factorial : ℂ)‖ ≤
      Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) := by
  refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) (fun N => ?_)
  have hsub : Finset.range N ⊆ Finset.Icc 0 N := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _))
    ((betaExactSharpBudget R hR).all_partial N)

/-- At the radius used in PR #18 (R = 3/4) the sharp bound is below 3,
whereas the PR #18 certificate has bound 4. -/
theorem betaExactSharp_at_three_quarters_lt_three :
    (betaExactSharpBudget (3 / 4) (by norm_num)).bound < 3 := by
  show Real.exp ((Real.sqrt 5)⁻¹ * (3 / 4) + (3 / 4) ^ 2 / 2) < 3
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hinv : (Real.sqrt 5)⁻¹ < 1 / 2 := by
    rw [one_div]; exact inv_strictAnti₀ (by norm_num) h5
  have hx : (Real.sqrt 5)⁻¹ * (3 / 4) + (3 / 4) ^ 2 / 2 ≤ 1 := by nlinarith
  calc Real.exp ((Real.sqrt 5)⁻¹ * (3 / 4) + (3 / 4) ^ 2 / 2)
      ≤ Real.exp 1 := Real.exp_le_exp.mpr hx
    _ < 3 := lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)

#print axioms recState_nonneg
#print axioms e_rec
#print axioms S_hasDerivAt
#print axioms S_two_le_exp
#print axioms S_le_exp
#print axioms hurwitzRec_sharpBudget
#print axioms betaExactSharpBudget
#print axioms betaExactSharpSummable
#print axioms betaExactSharp_tsum_le
#print axioms norm_betaInv
#print axioms betaExactSharp_at_three_quarters_lt_three

#check @betaExactSharpBudget
#check @hurwitzRec_sharpBudget
#check @betaExactSharpSummable
#check @betaExactSharp_tsum_le
#check @S_le_exp

end CNRSProblem2.HurwitzSharp
