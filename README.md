# Two-piece mollification of xi prime

An explicit Conrey–Feng two-component mollifier giving a **strictly greater than 88.45%** asymptotic lower bound for zeros of the derivative of the Riemann xi-function on the critical line, **counted with multiplicity**, conditional on the stated PRZZ input.

This repository contains a proof draft for specialist review, a reproducible finite numerical certificate, and a Lean derivation of the zero-proportion conclusion. `WuProportion.strict_proportion` proves a fixed margin: there exists `b > 0.8845` such that `b * Ncount 0 X ≤ N0 0 X` for every sufficiently large real `X`. Its printed dependencies are the three standard axioms and the existing `PRZZ.przz41_case3_K2_profiles` input; the PRZZ input itself is not proved here. No simplicity, localized PRZZ, or counting-gate assumption is added.

The [latest verification record](checks/wu-proportion-verification.json) freshly compiles the five final modules and replays all 187 registered axiom outputs after checking the 182 baseline source hashes. This is not a fresh rebuild of all 187 modules or of upstream AF. The unchanged manuscript predates the completed Lean chain; the numerical certificate alone still proves only a finite inequality.

[日本語の案内](README.ja.md) · [Manuscript PDF](paper/manuscript.pdf) · [LaTeX source](paper/manuscript.tex) · [Expert audit questions](paper/README.md#questions-requiring-analytic-review)

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
| PRZZ shifted-moment input | One explicit external axiom in a separate Lean file |
| Actual normalized PRZZ residual on a fixed bidisc | Uniform convergence and arbitrary finite mixed-derivative convergence to zero, relative only to the existing PRZZ axiom |
| Regularity of the actual zeta integral and gcd main term | Joint complex smoothness proved for T > 1 and negative real parts of both shifts; Cauchy regularity premises discharged |
| Literal arithmetic gcd main term and moments | All four 00/02/20/22 limits, zeta/height composition, Cauchy jets and concrete zeta-derivative moments connected |
| Logarithmic numerical budget | Lean proof of `1 - log(1.128201)/R > 0.8845`; not a zero-counting theorem |
| Actual Wu counting and all-height proportion | `WuProportion.strict_proportion` and `ratio_eventually_gt`; only the existing PRZZ input beyond standard axioms |
| New simple-zero bound or publication-priority claim | Not claimed |

The candidate uses $R=1.04440033$, $\theta=4/7-10^{-6}$, and the unrestricted Dirichlet convolution $\mu*\Lambda*\Lambda$. The unchanged Python certificate encloses

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
paper/       Five-page manuscript and unchanged standalone numerical bundle
lean/        187 registered Lean modules and pinned dependency information
tools/       Portable package and Lean verification commands
checks/      Captured packaging and Lean verification output
docs/        Proof status and reproduction instructions
.github/     Numerical-verification workflow
```

The paper bundle is preserved byte-for-byte. [Provenance](provenance.json) records its source hashes. No upstream AF or mathlib source tree is vendored.

## Proof boundaries

See [proof status](docs/STATUS.md) before interpreting a passing test. In particular, PRZZ's gcd/lcm main term and the finite Mellin-pole functional are separate objects; the latter is not smuggled into the PRZZ axiom.

## Copyright and license

Copyright (c) 2026 MASAMICHI IIZUMI

Licensed under the [MIT License](LICENSE.md).

## References

- X. Wu, [arXiv:1206.3737v2](https://arxiv.org/pdf/1206.3737v2), Section 3.
- K. Pratt, N. Robles, A. Zaharescu and D. Zeindler, [arXiv:1802.10521v3](https://arxiv.org/pdf/1802.10521v3), Theorem 4.1 and the main-term analysis.
- L. Alpöge and R. Furman, [arXiv:2608.13637v2](https://arxiv.org/html/2608.13637v2), and the pinned [AF Lean library](https://github.com/anthropics/formal-math/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510).

The manuscript and audit guide give the detailed source roles and literature-search limitations.
