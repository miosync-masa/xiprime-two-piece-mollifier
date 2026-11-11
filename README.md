# Two-piece mollification of xi prime

Published software snapshot: [v0.2.0 — The PRZZ axiom is gone: 88.45% from explicit Weil and Deshouillers–Iwaniec hypotheses](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0).
Version DOI: [10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).
Pinned release commit: `8fbfbe376d879274c5be7e2f655551c967dfdf99`.
The current manuscript's bibliography and submission-metadata revision postdates
this frozen archive; the tag and archived PDF are not overwritten.

> **Main theorem and external input, in three lines.**
> 1. `XiPrime8845.WuProportion.ratio_eventually_gt`: for every sufficiently large real `X`, `0.8845 < N0 0 X / Ncount 0 X`, where `N0` counts critical-line zeros of ξ′ with multiplicity and `Ncount` all zeros of ξ′ (AF's `Zeta23.XiPrime` counts).
> 2. The theorem now takes `hWeil : WeilIncomplete` and `hDI : DeshouillersIwaniecLemma1` explicitly. These deep estimates are hypotheses, not proved here.
> 3. The former PRZZ witness axiom is replaced by a theorem in `PRZZProvedInput`, via the height-uniform `PRZZFamilyMomentOptimal` and `PRZZWitnessBridge`. No local analytic axiom is declared.
>
> **v0.1.0 erratum:** the general-profile input was first replaced by a density-oriented witness input; that witness estimate is now proved from explicit Weil/DI hypotheses. The finite witness main term is exactly invariant under the shift exchange; the certified numerical intervals are unchanged. See [STATUS](docs/STATUS.md#v010-erratum-shift-placement-7-november-2026). The reading aids below now use the current source-checked Weil/DI dependency audit.
>
> Reading aids (generated from `import` lines and compiler output by `tools/generate_readability_docs.py`): [dependency graph](docs/dependency-graph.md) · [module table](docs/modules.md) · [paper ↔ Lean correspondence](docs/paper-correspondence.md) · [trust base](docs/trust-base.md).

An explicit Conrey–Feng two-component mollifier giving a **strictly greater than 88.45%** asymptotic lower bound for zeros of the derivative of the Riemann xi-function on the critical line, **counted with multiplicity**, under the explicit Weil and DI hypotheses.

This repository contains a proof draft for specialist review, a reproducible finite numerical certificate, and a Lean derivation of the zero-proportion conclusion. `WuProportion.strict_proportion` proves a fixed margin: there exists `b > 0.8845` such that `b * Ncount 0 X ≤ N0 0 X` for every sufficiently large real `X`. Its two analytic premises are explicit Weil/DI specifications. The public witness estimate is now derived rather than postulated; Weil and DI themselves are not proved here. No simplicity, localized PRZZ, or counting-gate assumption is added.

The [current local clean record](checks/clean-verification-2026-11-10-local.json) freshly compiles **all 778 local modules**, with **zero reused local outputs**, and checks **4,405 axiom audits**. The headline import closure contains 730 modules. The linked [AF clean record](checks/clean-verification-2026-11-10-af.json) freshly builds **all 101 required AF modules** in an isolated pinned worktree, with no old AF outputs; only fixed Mathlib/package caches are reused. Compile times were 190.253 seconds (AF) and 2,939.546 seconds (local, six worker slots), about 52 minutes 10 seconds combined. The [earlier interface-switch record](checks/weil-di-proportion-verification.json), with one fresh module and 777 reused outputs, is retained unchanged as history. The [witness-only record](checks/witness-only-proportion-verification.json), [five-module record](checks/wu-proportion-verification.json) and [earlier final audit](checks/wu-proportion-final-audit.json) describe their former interfaces. The numerical certificate alone still proves only a finite inequality.

[日本語の案内](README.ja.md) · [Manuscript PDF](paper/manuscript.pdf) · [LaTeX source](paper/manuscript.tex) · [Expert audit questions](paper/README.md#questions-requiring-analytic-review)

The manuscript and PDF were revised together on 10 November 2026 for the current conditional Weil/DI proof. Both input specifications, their quantifiers, the 49-pair family bridge and the actual counting convention are explicit. See the [render record](checks/manuscript-render-verification.json). Numerical intervals are unchanged; only the manuscript provenance hash in the certificate is refreshed.

**Pre-erratum 7 November clean verification:** the [698-module local record](checks/clean-project-verification-2026-11-07.json) and [101-module AF record](checks/clean-af-verification-2026-11-07.json) remain unchanged historical records. They do not certify the subsequent witness-only or current Weil/DI interface changes.

## For reviewers

The two inputs are established estimates in the literature, not new conjectures.
“Conditional” describes the formal boundary: their proofs are not formalized
here. The manuscript derives the incomplete estimate from the composite-modulus
Kloosterman bound by completion and identifies the DI source lemma.
Independent review of the exact Lean specifications remains distinct.

Start with the [review guide](docs/REVIEW_GUIDE.md): exact conditional claim,
reading order, evidence levels and remaining independent-review questions.
The authoritative statement is the Lean theorem. The revised TeX and PDF
now narrate that conditional proof, including the shift-placement erratum.
The [paper correspondence table](docs/paper-correspondence.md) identifies
two hypothesis definitions and the principal theorem contracts, and keeps
the independent Python interval separate. This is not completed human review.

## Cite the released software

MASAMICHI IIZUMI (2026), *miosync-masa/xiprime-two-piece-mollifier:
v0.2.0 — The PRZZ axiom is gone: 88.45% from explicit Weil and
Deshouillers–Iwaniec hypotheses*. Zenodo.
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).
For reproduction, use the release tag/commit above and its
[review guide](https://github.com/miosync-masa/xiprime-two-piece-mollifier/blob/v0.2.0/docs/REVIEW_GUIDE.md).
The current manuscript contains author/contact information, MSC/keywords,
data/code availability, funding and competing-interest declarations,
AF acknowledgements, and disclosure of Claude and ChatGPT/Codex assistance.


## Final theorem and axiom audit

The complete compiler output for `#print axioms ratio_eventually_gt` is:

```text
'XiPrime8845.WuProportion.ratio_eventually_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no nonstandard axiom or `sorryAx`. This is a conditional theorem: `WeilIncomplete` and `DeshouillersIwaniecLemma1` occur as explicit arguments, so a standard-only axiom list does not prove these deep inputs. The proof has a fixed margin above 0.8845 for all sufficiently large real heights, with multiplicity. See the [release notes](docs/RELEASE_NOTES.md) for the completed counting connections and precise verification scope, and the [theorem source](lean/WuProportion.lean) for both the fixed-margin and quotient statements.

## Original moment estimate: 7 November 2026

[`PRZZMomentOptimal.moment_bound`](lean/PRZZMomentOptimal.lean) now connects the actual zeta moment to `PRZZCoupledAFE.diagonalMain`, with error

$$C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

Weil's incomplete-sum bound and DI Lemma 1 remain explicit hypotheses. For fixed coefficient labels, a smooth monotone plateau seed and a smooth time cutoff supported in `[1,2]`, the constant is uniform for sufficiently large heights, `1 ≤ N ≤ T^(4/7)`, `N+1 ≤ T`, and bounded logarithmically scaled shifts separated by `r ≤ ‖A+B‖`, with `r > 0`. The actual paired Fourier tail is evaluated; no tail-budget premise remains in this theorem. See [current proof status](docs/STATUS.md#original-moment-estimate-7-november-2026).

The original fixed-label theorem alone did not replace the public input. The new [`PRZZFamilyMomentOptimal`](lean/PRZZFamilyMomentOptimal.lean) handles the height-dependent seven-vector family, and [`PRZZWitnessBridge.witness_estimate`](lean/PRZZWitnessBridge.lean) identifies the public integral and density-oriented main term for every `0 < theta < 4/7`. [`PRZZProvedInput`](lean/PRZZProvedInput.lean) supplies the proved replacement to the counting chain. No unconditional zero-proportion or simplicity claim is added.

## Historical PRZZ input decomposition: 2 November 2026

[`PRZZActiveRows.literal_absorbed`](lean/PRZZActiveRows.lean) now bounds the original literal A-star, after removing empty original rows and retaining each nonempty row's outer mass:

$$
|A^*|\le C T^{\delta+\gamma}\frac{\lambda}{d}
\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)
\int_{\mathbb R}(1+|t|)|\mathrm{mellin}\Phi(it)|\,dt.
$$

Weil's incomplete-sum estimate and DI Lemma 1 are explicit `Prop` hypotheses, not new axioms. The theorem supplies the three arithmetic cases, allocation sum and dyadic absorption; source frequency/scale conditions, shift separation and a strict loss-exponent margin remain explicit. Constants are uniform in the subsequently quantified height and row data, with the cutoff functions fixed beforehand. See [proof status](docs/STATUS.md#przz-decomposition-milestone-2-november-2026) for the conditions and verification scope.

This historical arithmetic A-star milestone was not a replacement for the PRZZ axiom. Its then-unfinished AFE, truncation and actual-kernel connections have since been developed through the original-moment theorem above, within that theorem's explicit scope.

## What is checked

| Component | Current status |
| --- | --- |
| Fixed witness and finite-functional inequality | Lean proof without numerical premises; independent Python interval calculation with saved output |
| Four K2 kernel identities, dual involution, witness identities and length margins | Lean proofs, compiled against the pinned environment |
| Uniform coefficient bound, Subpower and normalized PRZZ error envelope | Lean proofs without an external analytic axiom |
| Truncated inverse integrals and shift-jet identities | Lean proofs, now connected to finite beta-coefficient sums |
| Beta-integral coefficients and four K2 coefficient sums | Lean proofs |
| Quotient derivatives, W matrix and positive-side dual op | Lean proofs for smooth separable factors, including swapped dual and contracted profile symmetry |
| Inverse/outer integral differentiation and exact K2 evaluator | Lean proofs for the untruncated functional, including integrated contracted cross-term reduction |
| Taylor truncation error through the full K2 functional | Lean enclosure theorem |
| Finite beta-coefficient evaluator, cached W contraction and cross symmetry | Lean equality with the Taylor-polynomial integrals and an inherited error bound |
| Fixed target/dual exponential bounds and aggregate Taylor error <= 10^-6 | Lean proofs |
| Executable rational evaluator and fixed finite gate | Kernel-checked rational bounds; `FixedCertificate.fixed_functional_gate` has no numerical premise or external analytic axiom |
| PRZZ shifted-moment input | Witness estimate proved from explicit Weil/DI hypotheses; no local analytic axiom |
| Actual normalized PRZZ residual on a fixed bidisc | Uniform convergence and arbitrary finite mixed-derivative convergence to zero, under explicit Weil/DI hypotheses |
| Regularity of the actual zeta integral and gcd main term | Joint complex smoothness proved for T > 1 and negative real parts of both shifts; Cauchy regularity premises discharged |
| Literal arithmetic gcd main term and moments | All four 00/02/20/22 limits, zeta/height composition, Cauchy jets and concrete zeta-derivative moments connected |
| Logarithmic numerical budget | Lean proof of `1 - log(1.128201)/R > 0.8845`; not a zero-counting theorem |
| Actual Wu counting and all-height proportion | `WuProportion.strict_proportion` and `ratio_eventually_gt`; explicit Weil/DI arguments, standard-only axiom audits |
| New simple-zero bound or publication-priority claim | Not claimed |

The candidate uses $R=1.04440033$, $\theta=4/7-10^{-6}$, and the unrestricted Dirichlet convolution $\mu*\Lambda*\Lambda$. The unchanged Python calculation encloses

$$
1.12818163807203565629105<M<1.12818163807203565629124
<\exp\{R(1-0.8845)\}.
$$

The Lean certificate uses a separate, coarser enclosure: the real part of the differentiated K2 functional is at most **1.128201**, while the target exponential is greater than **1.1282054105**. The counting transfer uses the slightly larger cap **1.128202**. The finite certificate is one component of the subsequent arithmetic, moment and counting proofs, not a replacement for them.

## Reproduce the finite certificate

Python 3.10 or later is required. From this directory:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python tools/verify_release.py
```

The last command checks the distribution hashes, reruns the original verifier, and compares its JSON output byte-for-byte with the saved certificate. After the dependency is installed, verification needs no network access, private research checkout, zero tables or CUE data.

For optional Lean checks and manuscript rebuilding, see [reproduction instructions](docs/REPRODUCIBILITY.md).

## Repository layout

```text
paper/       Revised conditional manuscript/PDF, standalone numerical bundle
lean/        Lean modules and pinned dependency information
tools/       Portable package and Lean verification commands
checks/      Captured packaging and Lean verification output
docs/        Proof status and reproduction instructions
.github/     Numerical-verification workflow
```

The numerical algorithms, fixed witness and interval results are unchanged. The TeX erratum, its certificate provenance hash, paper README and manifests have been revised; the paper bundle as a whole is therefore **not** byte-identical to the initial draft. [Provenance](provenance.json) retains historical snapshots; current file integrity is specified by the manifests. No upstream AF or mathlib source tree is vendored.

## Supplementary development records

[Proof-status milestones](docs/STATUS.md), [release notes](docs/RELEASE_NOTES.md)
and the [development ledger](docs/history.md) are retained as supplementary
history. They are not prerequisites for the [review route](docs/REVIEW_GUIDE.md)
or the [reproduction instructions](docs/REPRODUCIBILITY.md). Historical tags
and compiler records remain unchanged.

## Proof boundaries

See [proof status](docs/STATUS.md) before interpreting a passing test. In particular, the actual moment, density-oriented gcd/lcm main term and finite Mellin-pole functional are separate objects connected by proved theorems. The remaining external hypotheses are the exact Weil/DI propositions in `PRZZKloostermanInputs`, not a PRZZ axiom. Independent review must check these specifications and the interpretation of the final statement.

## Copyright and license

Copyright (c) 2026 MASAMICHI IIZUMI

Licensed under the [MIT License](LICENSE.md).

## References

- X. Wu, *Distinct zeros of the Riemann zeta-function*, Q. J. Math. **66** (2015), 759–771, [doi:10.1093/qmath/hav014](https://doi.org/10.1093/qmath/hav014). The inspected argument is [arXiv:1206.3737v2](https://arxiv.org/pdf/1206.3737v2), Section 3.
- K. Pratt, N. Robles, A. Zaharescu and D. Zeindler, *More than five-twelfths of the zeros of ζ are on the critical line*, Res. Math. Sci. **7** (2020), Article 2, [doi:10.1007/s40687-019-0199-8](https://doi.org/10.1007/s40687-019-0199-8). The theorem/page references use [arXiv:1802.10521v3](https://arxiv.org/pdf/1802.10521v3), Theorem 4.1 and the main-term analysis.
- L. Alpöge and R. Furman, [arXiv:2608.13637v2](https://arxiv.org/html/2608.13637v2), and the pinned [AF Lean library](https://github.com/anthropics/formal-math/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510).

The manuscript and audit guide give the detailed source roles and literature-search limitations.
