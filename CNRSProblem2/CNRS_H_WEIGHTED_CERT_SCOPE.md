# CNRS-H weighted certification — development proof boundary

This file records the scope of the draft PR #10 and is not a release certificate.

## Independently CI-confirmed

- Original factorial/binomial identity, finite weighted pair-budget identity, and finite complex-tail bound with an explicitly supplied coefficient budget — GitHub Actions run 42664946290.
- `finiteHurwitzWeightedNorm_nonneg`, `finiteHurwitzWeightedNorm_add_le`, `finiteHurwitzWeightedNorm_single`, `finiteHurwitzWeightedNorm_single_mul_single`, and `finiteHurwitzCoeffNorm_le_pairSum`, integrated with the actual `FiniteHurwitz ℂ` carrier — green Actions run 42670833038 at commit `147d8be1979fcc6ab59ab732fb670b655cc38c85`.

## Pending formal proof gate

- `finiteHurwitzWeightedNorm_mul_le`, in `HurwitzConvolutionNorm.lean`, attempts to combine:
  1. product support contained in the set of input-support degree sums;
  2. a coefficientwise finite triangle inequality;
  3. finite summation rearrangement over output degrees and input pairs;
  4. factorial/binomial pair-budget factorization.
- Workflow run 42671236266 for full theorem head `8f0e62cbd6b852cdd590f708cbc1e863d6215b5f` ended **failure with zero jobs**. No Lean compiler diagnosis exists from that run, so the theorem is **unverified** until an actual compiling CI job succeeds.
- A mathematical paper proof and 1,000 finite exact Gaussian-rational computational trials are independent support, not a replacement for Lean checking.

## Explicit exclusions

This PR does not prove weighted summability of arbitrary infinite CNRS-H coefficient sequences, a Banach completion of the exact coefficient ring, a global majorant from a finite jet alone, Python runtime refinement, or a publicly adopted Lean release. The concrete analytic example `exp(z/β+z²/2)` has a separate mathematically proved all-index majorant but has not yet been formalized in Lean.


## November 9 CI startup diagnosis and norm scope

- The initial 18:05 UTC run **42670833038** created seven jobs and all passed at commit `147d8be1979fcc6ab59ab732fb670b655cc38c85`. It predates the full norm aggregation theorem.
- Subsequent 18:07–18:14 UTC runs **42671236266**, **42671691509**, and **42672229420** all concluded failure with **zero jobs created** (verified by the workflow-run jobs API). They contain no compiler output. The latter run belongs to stacked PR #11.
- The repository workflow file still declares a six-project Lean matrix and a source-hygiene job. Github reports no Lean compilation for the latest aggregate theorem. Do not classify this as a mathematical/proof failure or as a passing build. Re-run was rejected with `403 This workflow run cannot be retried`.
- At radius `R = 0`, the weighted expression reduces to `‖x 0‖` and is only a seminorm; for a positive-definite norm require `R > 0`. The proved inequalities are meaningful for `R ≥ 0`.


## Governance

No automatic merge, tag, release, Zenodo change, or modification of the live Dropbox Formal Methods status is implied. Keep the draft and require CI with actual Lean build jobs plus independent review before integration.
