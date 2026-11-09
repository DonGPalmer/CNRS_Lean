# CNRS-H all-index coefficient-budget gate — draft

**Date:** 2026-11-09. **Status:** DEVELOPMENT CANDIDATE; not a new released, published or adopted formal edition.

## Exact theorems

The imported CNRS-H finite multiplication and certificate results (PR #10 and PR #11) are integrated into `main` at commits `f6c288f8017617b0f3574d8e42fae211a7f329c4` and `5ab26b5400a8738f0ede9e81ea00f76037d44048`. These prove finite-support weighted convolution submultiplicativity and justified finite product budgets.

This branch adds `UniformCoefficientBudget a`: a real number `bound` and an all-order theorem `∀ M, ∑ n ∈ Icc 0 M, ‖a n‖ ≤ bound`.

From this, Lean proves:
- `tail_le`: every finite coefficient tail is bounded by that same certificate.
- `evaluation_tail`: every finite complex evaluation tail at `‖z‖ ≤ 1` is at most `‖z‖^(N+1) * bound`.
- `summable_norm`: the series of absolute normalized coefficient values is summable.
- `summable_coeff`: the normalized complex coefficient series is summable.
- `summable_evaluation`: the normalized complex evaluation series is summable on the closed unit disk.

The all-order coefficient budget is a **proof obligation**, not supplied by an arbitrary finite jet. For a physical radius `R>0`, the intended input is normalized coefficients `a_n = c_n R^n/n!`; evaluation on `|w|≤R` corresponds to `z=w/R`.

## Remaining scientific and implementation gates

1. Prove the all-index budget *for a specific exact CNRS recurrence*, such as `c_(n+1) = β^-1 c_n + n c_(n-1)`, with `β=-2+i`, generating function `exp(z/β+z²/2)`, and independently derived bound `exp(R/√5 + R²/2)`.
2. Establish the explicit morphism/embedding from the programme's exact `RAValue` finite-Laurent carrier to complex coefficient values and show the coefficient/operation correspondence.
3. Derive a norm estimate for the **actual infinite tail** (rather than only all finite tails) from the now-formal summability theorem, with (R>0) and radius ratio controls.
4. Audit the formal statements and their `#print axioms` output at the final source head; no `sorry`/ `admit` introduced.
5. Integrate only under separate governed review and author approval; do not update formal release, Toolkit bundle, canonical papers or Zenodo record based solely on this candidate.
