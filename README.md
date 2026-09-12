# CNRS Lean — Formal Verification for the CNRS Programme

Lean 4 formalization of the finite-kernel mathematics underlying the
**Complex Numeric Representational System (CNRS)**, a positional number
system in base $z_0 = -2+i$ developed as part of the
[Scale Space–CNRS research programme](https://www.ss-cnrs.nul1.com).
Independent researcher: Donald G. Palmer
([ORCID 0000-0003-4335-5533](https://orcid.org/0000-0003-4335-5533)).

This repository is a curated export of a verified, immutable release. It is
not a live mirror of the private CI/development repository — see
[Provenance](#provenance) below for exactly what that does and does not mean
for trusting the claims here.

## Environment

- **Lean**: `leanprover/lean4:v4.33.0`
- **Mathlib**: pinned at commit `db584cd6d46c92f209a44c0f1c829460d327499d`
  (tag `v4.33.0`)

Every project's `lean-toolchain` and `lake-manifest.json` pin these exactly;
nothing here has been re-pinned or edited for this export.

## The six projects, and how they depend on each other

Dependencies are real `lakefile.toml` requirements (relative sibling paths),
not just a narrative ordering — build them in this order:

| Project | Depends on | What it is |
|---|---|---|
| `CNRSCore` | — (Mathlib only) | Finite Gaussian-integer foundation: `z_0 = -2+i`, its norm, irreducibility/primality, `IsDedekindDomain GaussianInt`. |
| `CnrsQ2` | `CNRSCore` | The $\beta$-adic completion result: an injective, dense-range ring homomorphism $\mathbb Z[i]\to\mathbb Z_5$ carrying $z_0$ to a uniformizer — the concrete form of $K_\beta\cong\mathbb Q_5$. |
| `CNRSArithmetic` | `CNRSCore` | Exact addition (carry-set machinery), fixed-multiplier machinery, division termination/cycle classification, and a finite-automaton **impossibility theorem** for unrestricted online multiplication. |
| `CNRSIntegration` | `CNRSArithmetic`, `CnrsQ2` | The addition–carrier bridge connecting the two prior results. |
| `CNRSProblem1` | — (Mathlib only) | Negative-base (CNS) results through the negabinary endpoint normalization. The only one of the six with **zero** `native_decide` dependence — see [Axiom footprint](#axiom-footprint). |
| `CNRSProblem2` | `CnrsQ2` | The largest project: branch cover, canonical lifted logarithm, serialization, finite Laurent/Hurwitz algebra, branch transport and relative normalization, culminating in a finite-support Hurwitz antiderivative (P2-L10). Ten governed layers, P2-L1 through P2-L10; see [`CNRSProblem2/README.md`](CNRSProblem2/README.md) for the exact boundary of each layer. |

## What is proved and how it maps to the papers

This table is the authoritative theorem↔paper correspondence, reproduced
from the programme's own tracking register
([`CNRS_LEAN_THEOREM_TO_PAPER_LEDGER.csv`](CNRS_LEAN_THEOREM_TO_PAPER_LEDGER.csv),
included in this repo). Read the **scope note** column as carefully as the
status column — several of these are deliberately partial results, not full
statements of the informal paper's claims.

| Paper | Lean project(s) | Status | Scope |
|---|---|---|---|
| CNRS Problem 1 | `CNRSProblem1` | Proved | P1-L1–L7; excludes a general Pisot theorem |
| CNRS Problem 2, Layers | `CNRSCore`, `CnrsQ2`, `CNRSProblem2` | Proved, finite scope | Finite carrier and explicit branch data; no arbitrary infinite serialization |
| CNRS Problem 2, Capstone | `CNRSProblem2` | Proved, finite scope | P2-L1–L10; no analytic continuation or path reconstruction |
| CNRS Problem 3 | `CNRSArithmetic`, `CNRSIntegration` | Partially proved | Addition and certified division outcomes proved; unrestricted online multiplication proved **impossible** in the governed model; streaming division is open |
| CNRS Problem 4 | `CNRSCore`, `CNRSArithmetic`, `CNRSProblem1` | Partially proved | Finite operational kernel only; no general complex-representation completeness theorem |

**What is explicitly *not* claimed**, programme-wide: arbitrary infinite-series
serialization, analytic continuation or path reconstruction, unequal-branch
arithmetic, unrestricted streaming multiplication or division, or a general
representation theorem for all complex numbers. `CNRSProblem2`'s own
per-layer `*_THEOREM_BOUNDARY_FROZEN.md` files state each layer's exact
scope and exclusions in full — read those, not just this summary, before
relying on a specific result.

**On P2-L10 specifically**: P2-L10 is included in the independently audited,
governed GREEN consolidated capstone identified in [Provenance](#provenance).
It proves the finite-support Hurwitz antiderivative within the frozen boundary
stated by the project; it does not establish arbitrary infinite
serialization, analytic continuation, or path reconstruction. Build the
included source and inspect its theorem boundaries using the instructions
below rather than extending the result beyond that certified scope.

## Axiom footprint

"Zero `sorry`" is necessary but not sufficient — `native_decide` can also
carry semantic risk if misused. Every project's exact footprint, disclosed
per project rather than asserted in aggregate:

| Project | `native_decide` axioms | Traced to |
|---|---|---|
| `CNRSCore` | 80 | `nextQuotient3_height_lt` (a termination lemma closing finitely many small-integer case splits) |
| `CnrsQ2` | 37, independent of Core's | `gaussianIterate_five_eq_zero_of_norm_lt_eleven` |
| `CNRSArithmetic` | 81 (80 inherited + 1 local) | Phase F capstone (the online-multiplication impossibility theorem) |
| `CNRSIntegration` | 2–4 per theorem | Inherited from `CNRSArithmetic`'s carry-set lemmas |
| `CNRSProblem1` | **0** | — |
| `CNRSProblem2` | 80, inherited | `CNRSCore`, via the L9/L10 codec layers |

All `native_decide` uses here close finitely many concrete small-integer
case splits (bounded decision procedures), not open-ended semantic content —
but don't take that characterization on faith either; `#print axioms` on any
theorem below will show you exactly what it depends on.

## Building and checking this yourself

```bash
# from inside any one project directory, in the dependency order above:
lake exe cache get   # if using Mathlib's binary cache
lake build
```

To check a specific result carries no `sorry` and inspect its exact axiom
dependencies:

```bash
lake env lean --run <<'EOF'
#print axioms CNRSProblem2.<theorem_name>
EOF
```

or open the file in the Lean 4 VS Code extension and hover/`#print axioms`
directly. A source-level grep is also a legitimate, fast first check:

```bash
grep -rn "sorry\|admit" --include="*.lean" .
```

(This should return nothing. If it does, that's a real finding — please
open an issue.)

## Provenance

This repository was exported from an immutable, internally-verified
consolidated release, not pushed directly from the private development
repository (`SSC_Formal_Methods_CI`), which remains private. What that
means concretely:

Machine-readable release identity is recorded in [`PROVENANCE.json`](PROVENANCE.json),
and [`SHA256SUMS.txt`](SHA256SUMS.txt) inventories every file in the six
certified project trees.

- **Independently verifiable from this repo alone**: that the source
  compiles under the pinned Lean/Mathlib versions above, that it is
  genuinely free of `sorry`/`admit`/added `axiom`, and the exact
  `native_decide` footprint per theorem — all via the commands above, or
  via this repo's own CI (see the Actions tab).
- **Not independently verifiable from this repo**: the specific commit
  history and CI run identities in the private development repository that
  produced this release. Where those are cited (e.g. in
  `CNRSProblem2/README.md`), treat them as self-reported by the programme,
  not as something this public repository lets you re-check directly.

This distinction is deliberate, not an oversight — see `CONTRIBUTING`-level
programme discipline: claims get checked against what's actually
reproducible, not repeated because an earlier document said so.

## Relationship to the CNRS Scientific Toolkit

The [CNRS Scientific Toolkit](https://github.com/DonGPalmer/CNRS_Scientific_Toolkit)
is the Python research-software implementation of CNRS arithmetic. Its
v0.13.0 release vendors this exact same certified snapshot under
`formal/lean/` (same artifact SHA-256:
`840ffee8a9a1183292ef8c952fe81199b1d916ea0fd0e688602f19559a375c21`) so that
Toolkit users have the formal guarantees bundled alongside the software they
are using — Python itself remains independently implemented, not
Lean-extracted. This repository is the dedicated counterpart: a permanent,
directly-citable home for the formalization on its own terms, versioned
independently of the Toolkit's own release cadence.

## Citing this work

See [`CITATION.cff`](CITATION.cff), or GitHub's "Cite this repository"
button. The Zenodo concept DOI for all versions is
[`10.5281/zenodo.22726349`](https://doi.org/10.5281/zenodo.22726349).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Chosen
to match [Mathlib's own license](https://github.com/leanprover-community/mathlib4),
which every project here depends on directly.
