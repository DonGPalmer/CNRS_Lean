import CNRSProblem2.HurwitzRecurrenceGrowth
import Mathlib.Tactic

/-!
# CNRS-H: two-step geometric decay from a certified recurrence contraction

If nonnegative coefficient magnitudes b satisfy
b(n+2) ≤ q * max (b(n+1)) (b n)
beyond a proved starting index N and 0 ≤ q ≤ 1, then the largest
coefficient in consecutive two-step blocks is bounded by q^k
times the initial block's maximum.

For the canonical exact recurrence the intended coefficient family is
b n = ‖c_n‖ R^n / n!. The differential inequality and the final
geometric-series tail bound are separate proof obligations, not assumed
to follow from numerical sampling.
-/

namespace CNRSProblem2

/-- A two-step contraction yields uniform geometric decay of paired terms.
No analytic series or infinite summation is assumed. -/
theorem twoStepBlockDecay
    (b : ℕ → ℝ) (N : ℕ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hb : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, N ≤ n →
      b (n + 2) ≤ q * max (b (n + 1)) (b n)) :
    ∀ k : ℕ,
      max (b (N + 2 * k + 1)) (b (N + 2 * k)) ≤
        q ^ k * max (b (N + 1)) (b N) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let idx : ℕ := N + 2 * k
      let M : ℝ := max (b (idx + 1)) (b idx)
      have hM : 0 ≤ M := by
        exact (hb (idx + 1)).trans (le_max_left _ _)
      have hqM : q * M ≤ M := by
        calc
          q * M ≤ 1 * M := mul_le_mul_of_nonneg_right hq1 hM
          _ = M := one_mul _
      have hnext1 : b (idx + 2) ≤ q * M := by
        exact hstep idx (by dsimp [idx]; omega)
      have hnext2 : b (idx + 3) ≤ q * M := by
        calc
          b (idx + 3) ≤ q * max (b (idx + 2)) (b (idx + 1)) := by
            convert hstep (idx + 1) (by dsimp [idx]; omega) using 1 <;> omega
          _ ≤ q * M := by
            apply mul_le_mul_of_nonneg_left _ hq0
            exact max_le (hnext1.trans hqM) (le_max_left _ _)
      have hstepblock :
          max (b (N + 2 * (k + 1) + 1))
              (b (N + 2 * (k + 1))) ≤ q * M := by
        have h1 : N + 2 * (k + 1) + 1 = idx + 3 := by
          dsimp [idx]
          omega
        have h2 : N + 2 * (k + 1) = idx + 2 := by
          dsimp [idx]
          omega
        rw [h1, h2]
        exact max_le hnext2 hnext1
      have hm_eq :
          M = max (b (N + 2 * k + 1)) (b (N + 2 * k)) := by
        rfl
      calc
        max (b (N + 2 * (k + 1) + 1))
            (b (N + 2 * (k + 1))) ≤ q * M := hstepblock
        _ ≤ q * (q ^ k * max (b (N + 1)) (b N)) := by
          exact mul_le_mul_of_nonneg_left (hm_eq ▸ ih) hq0
        _ = q ^ (k + 1) * max (b (N + 1)) (b N) := by
          rw [pow_succ]
          ring

#print axioms twoStepBlockDecay

end CNRSProblem2
