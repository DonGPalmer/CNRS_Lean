import CNRSProblem2.HurwitzExactInfiniteTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# CNRS-H: proof-carrying adaptive truncation order

For a closed evaluation disk of radius 0 ≤ r < R and tolerance ε > 0,
the sharp analytic majorant constructs a finite Taylor/Hurwitz degree N
whose error is proved below ε, uniformly on the disk.

The existence of N uses geometric decay; the chosen degree uses
classical choice over reals. This is a mathematical certificate and
specification for a subsequent executable rational-interval algorithm,
not a claim that Lean's noncomputable real exp is a runnable numerical
order selector.
-/

namespace CNRSProblem2.HurwitzSharp

/-- Quantitative error envelope for the canonical exact recurrence. -/
noncomputable def sharpTailEnvelope (R r : ℝ) (N : ℕ) : ℝ :=
  Real.exp ((Real.sqrt 5)⁻¹ * R + R ^ 2 / 2) * (r / R) ^ (N + 1)

/-- Strict positive-tolerance termination: geometric decay of the
proved error envelope gives a finite order for every ε > 0. -/
theorem exists_certifiedOrder (R r ε : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε) :
    ∃ N : ℕ, sharpTailEnvelope R r N < ε := by
  have hq0 : 0 ≤ r / R := div_nonneg hr hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  have hpow : Tendsto (fun n : ℕ => (r / R) ^ (n + 1))
      Filter.atTop (nhds (0 : ℝ)) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (tendsto_add_atTop_nat 1)
  have hlim :
      Tendsto (fun N : ℕ => sharpTailEnvelope R r N)
        Filter.atTop (nhds (0 : ℝ)) := by
    convert (tendsto_const_nhds.mul hpow) using 1
    · ext n
      rfl
    · simp
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 ε hε).exists
  exact ⟨N, hN⟩

/-- A mathematically selected (noncomputable) certified order. -/
noncomputable def certifiedOrder (R r ε : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε) : ℕ :=
  Classical.choose (exists_certifiedOrder R r ε hR hr hrR hε)

/-- The selected order has the requested strictly positive tolerance. -/
theorem certifiedOrder_envelope_lt (R r ε : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε) :
    sharpTailEnvelope R r
      (certifiedOrder R r ε hR hr hrR hε) < ε :=
  Classical.choose_spec (exists_certifiedOrder R r ε hR hr hrR hε)

/-- Certified uniform error for the adaptive polynomial on |w| ≤ r. -/
theorem certifiedOrder_error_lt (R r ε : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    ‖betaExactAnalyticValue w -
      betaExactTaylorPolynomial (certifiedOrder R r ε hR hr hrR hε) w‖ < ε := by
  exact lt_of_le_of_lt
    (betaExact_infinite_tail_le R r hR hr hrR w hw
      (certifiedOrder R r ε hR hr hrR hε))
    (certifiedOrder_envelope_lt R r ε hR hr hrR hε)

/-- Any supplied candidate N with a certified numerical envelope
satisfies the requested error tolerance, without requiring choice. -/
theorem verifiedProvidedOrder (R r ε : ℝ) (N : ℕ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hbound : sharpTailEnvelope R r N ≤ ε)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    ‖betaExactAnalyticValue w - betaExactTaylorPolynomial N w‖ ≤ ε :=
  (betaExact_infinite_tail_le R r hR hr hrR w hw N).trans hbound

#print axioms exists_certifiedOrder
#print axioms certifiedOrder_error_lt
#print axioms verifiedProvidedOrder

end CNRSProblem2.HurwitzSharp
