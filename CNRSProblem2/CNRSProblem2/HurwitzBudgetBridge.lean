import CNRSProblem2.HurwitzUniformBudget
import CNRSProblem2.HurwitzFiniteNorm
import Mathlib.Tactic

/-!
# Certified all-index budget for finite-support CNRS-H values

This module adapts two companion Lean checks recorded in the independent
2026-11-09 Formal Methods audit
LEAN_PR_Evidence3_20261109.md, section 7.
The earlier auditor independently compiled the propositions; the present
branch integrates them under stable names and builds them in the project.

A finite Hurwitz value has zero coefficients beyond its support, so its
weighted finite norm supplies a genuine all-index budget for the resulting
finitely supported normalized sequence. This does NOT certify the tail of
an arbitrary infinite sequence agreeing with its finite prefix.
-/

namespace CNRSProblem2
open scoped BigOperators

/-- Existence of a uniform finite-partial-sum budget is equivalent to
absolute summability. The structure's value is carrying an explicit
quantitative bound and its verification, not discovering summability. -/
theorem uniformBudget_nonempty_iff (a : ℕ → ℂ) :
    Nonempty (UniformCoefficientBudget a) ↔
      Summable (fun n : ℕ => ‖a n‖) := by
  constructor
  · rintro ⟨cert⟩
    exact cert.summable_norm a
  · intro h
    exact ⟨⟨∑' n, ‖a n‖,
      fun M => h.sum_le_tsum _ (fun n _ => norm_nonneg _)⟩⟩

/-- The genuine finite-support weighted norm is an all-index budget for
the same finite series regarded as a sequence with zero coefficients outside
its support. In particular this is not a majorant for any other infinite
series merely sharing the same finite prefix. -/
noncomputable def uniformBudgetOfFinite
    (x : FiniteHurwitz ℂ) (R : ℝ) (hR : 0 ≤ R) :
    UniformCoefficientBudget
      (fun n : ℕ => x n * (R : ℂ) ^ n / (n.factorial : ℂ)) where
  bound := finiteHurwitzWeightedNorm R x
  all_partial := by
    classical
    intro M
    have hw : ∀ m : ℕ, 0 ≤ R ^ m / (m.factorial : ℝ) := fun m =>
      div_nonneg (pow_nonneg hR _) (by positivity)
    have hterm : ∀ n : ℕ,
        ‖x n * (R : ℂ) ^ n / (n.factorial : ℂ)‖ =
          ‖x n‖ * (R ^ n / n.factorial) := by
      intro n
      rw [norm_div, norm_mul, norm_pow]
      simp [abs_of_nonneg hR]
      ring
    have hzero : ∀ n ∈ Finset.Icc 0 M,
        ‖x n‖ * (R ^ n / n.factorial) ≠ 0 →
          n ∈ x.coeff.support := by
      intro n _ hne
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hne
      have : x n = 0 := h0
      simp [this]
    calc
      (∑ n ∈ Finset.Icc 0 M,
        ‖x n * (R : ℂ) ^ n / (n.factorial : ℂ)‖) =
          ∑ n ∈ Finset.Icc 0 M,
            ‖x n‖ * (R ^ n / n.factorial) :=
        Finset.sum_congr rfl (fun n _ => hterm n)
      _ = ∑ n ∈ (Finset.Icc 0 M).filter
            (fun n => n ∈ x.coeff.support),
            ‖x n‖ * (R ^ n / n.factorial) :=
        (Finset.sum_filter_of_ne hzero).symm
      _ ≤ ∑ n ∈ x.coeff.support,
            ‖x n‖ * (R ^ n / n.factorial) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => (Finset.mem_filter.mp hn).2)
          (fun m _ _ => mul_nonneg (norm_nonneg _) (hw m))
      _ = finiteHurwitzWeightedNorm R x := by
        unfold finiteHurwitzWeightedNorm
        rfl

#print axioms uniformBudget_nonempty_iff
#print axioms uniformBudgetOfFinite

end CNRSProblem2
