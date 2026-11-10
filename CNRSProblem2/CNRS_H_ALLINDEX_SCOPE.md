# CNRS-H all-index coefficient and analytic-certification scope

**Updated 10 November 2026. Status: POST-v1.0.3 DEVELOPMENT IN MAIN; not a new released or published formal edition.**

## Verified integrated claims

The post-v1.0.3 development through GitHub PRs #10–#19 is integrated
on `main` at commit `1747ec457731dabeee553ffb68593ae41668c080`.
All six Lean projects and source proof hygiene passed final integrated
CI run `42871566570`. Independent audit Review 6 and Evidence 6 are filed
under `/_SSC/25_Formal Methods/95_Audit/`.

1. **Finite weighted Hurwitz algebra.** `HurwitzFiniteNorm`,
   `HurwitzConvolutionNorm`, `HurwitzProductBudget` and
   `HurwitzNormAxiomAudit` prove weighted finite-support product inequalities
   and proof-carrying finite product budgets. The weight at radius zero
   is a seminorm, not a positive definite norm.
2. **All-order interface.** `HurwitzUniformBudget` defines
   `UniformCoefficientBudget`; it bounds every finite partial sum and
   proves absolute summability. It does **not** generate a bound from an
   arbitrary finite jet.
3. **Exact canonical recurrence and embedding.** `HurwitzRecurrenceGrowth`
   defines `betaHurwitzCoeff n : RAValue` with
   `c₀=1`, `c₁=β⁻¹`, `c_(n+2)=β⁻¹ c_(n+1)+(n+1)c_n`,
   where `β=-2+i`. `HurwitzExactComplexBridge` proves an injective
   ring map `raToC : RAValue →+* ℂ`, `raToC β⁻¹=(-2-i)/5`, and
   coefficient-by-coefficient correspondence.
4. **Constructed all-radius majorant.** `HurwitzSharpMajorant` constructs,
   for **every real R ≥ 0**, an actual `UniformCoefficientBudget` for the
   mapped exact recurrence with bound
   `Real.exp ((Real.sqrt 5)⁻¹ * R + R^2 / 2)`.
   The general complex recurrence theorem works for any `a : ℂ`
   with bound `exp (‖a‖ R + R²/2)`. Summability and a bound on the
   infinite sum of norms are verified.
5. **Actual infinite-series error.** `HurwitzInfiniteTail` proves a bound
   on the **convergent infinite sum minus its finite degree-N polynomial**.
   `HurwitzExactInfiniteTail.betaExact_infinite_tail_le` specializes this
   to the exact canonical `RAValue` recurrence: for `0 ≤ r < R`,
   `R > 0`, and `‖w‖ ≤ r`,
   ```
   ‖F(w) - P_N(w)‖ ≤
     exp(R/√5 + R²/2) * (r/R)^(N+1).
   ```
   Its evaluated entire series is convergent at each finite complex point;
   this follows from the all-radius certificates, although the dedicated
   public convergence alias had not been exported as of this record.
6. **Proof scope.** Review 6 independently re-derived the actual infinite
   tail theorem in a separate Lean environment. The selected new
   analytic declarations print only `propext`, `Classical.choice`,
   `Quot.sound`. Some older, unrelated formal layers retain
   separately disclosed `native_decide` dependencies.

## Remaining scientific and implementation gates

- Prove in Lean the **closed-form equality**
  `F(w) = Complex.exp (w/β + w²/2)`. This classical identity is
  mathematically established by the recurrence but **not yet a Lean theorem**
  at integrated commit `1747ec4`.
- Construct a certified adaptive order-selection interface accepting
  `r`, `R`, and tolerance `ε>0`, returning a finite degree and
  a Lean-proved remainder bound; optionally derive and certify an
  optimal or near-optimal choice of `R`.
- Connect exact coefficient computation and error certificates to
  the CNRS Python Toolkit by a separately tested refinement interface.
- Refresh the public README and theorem-to-paper ledger to distinguish
  the integrated development claims from the immutable v1.0.3 release.
  Governed Dropbox records and release artifacts require their own
  controlled update; this scope file alone changes no release.
- Formalize broader classes of infinite Hurwitz/CNRS-H systems, general
  analytic continuation, and any claims not implied by the specific
  canonical recurrence only after specifying their additional hypotheses.

**Publication boundary:** the main-branch integration is not a new
GitHub release, Toolkit vendoring update, canonical manuscript, DOI or
Zenodo deposit. The complete series claims above concern the specified
recurrence and its complex image; do not infer analytic certification
from a finite coefficient prefix or for arbitrary formal CNRS-H values.
