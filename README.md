# Two-piece mollification of xi prime

An explicit Conrey–Feng two-component mollifier for a proposed **88.45%** lower bound on the proportion of zeros of the derivative of the Riemann xi-function on the critical line, **counted with multiplicity**.

This repository contains a proof draft for specialist review, a reproducible finite numerical certificate, and partial Lean formalizations. The numerical certificate verifies a finite main-term inequality; it does not certify the analytic transplantation. The full zero-proportion theorem is not yet formalized in Lean.

[日本語の案内](README.ja.md) · [Manuscript PDF](paper/manuscript.pdf) · [LaTeX source](paper/manuscript.tex) · [Expert audit questions](paper/README.md#questions-requiring-analytic-review)

## What is checked

| Component | Current status |
| --- | --- |
| Fixed witness and finite main-term inequality | Exact rational checks and interval calculation, with saved output |
| Four K2 kernel identities, dual involution, witness identities and length margins | Lean proofs, compiled against the pinned environment |
| Uniform coefficient bound, Subpower and normalized PRZZ error envelope | Lean proofs without an external analytic axiom |
| Truncated inverse integrals and shift-jet identities | Lean foundations; full K2 evaluator equivalence and remainder bounds remain open |
| Beta-integral coefficients and four K2 coefficient sums | Lean proofs; differentiated quotient/dual assembly remains open |
| PRZZ shifted-moment input | One explicit external axiom in a separate Lean file |
| Leading-pole asymptotics, analytic Mellin identification and Wu counting adapter | Proof draft; formalization incomplete |
| New simple-zero bound or publication-priority claim | Not claimed |

The candidate uses $R=1.04440033$, $\theta=4/7-10^{-6}$, and the unrestricted Dirichlet convolution $\mu*\Lambda*\Lambda$. The finite certificate encloses

$$
1.12818163807203565629105<M<1.12818163807203565629124
<\exp\{R(1-0.8845)\}.
$$

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
lean/        Three Lean prototypes and pinned dependency information
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
