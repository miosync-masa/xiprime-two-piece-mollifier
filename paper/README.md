# Conditional xi-prime proportion: manuscript and finite certificate

Revised: 10 November 2026. The [manuscript source](manuscript.tex) and
[PDF](manuscript.pdf) now describe the current Lean route from two explicit
exponential-sum hypotheses to a fixed proportion strictly above 88.45%.
These are established estimates in the literature. The qualification is
formal: their proof terms are not included in this Lean development.
Both numerator and denominator are AF's actual **xi-prime** zero counts,
with analytic multiplicity; this is not a simple-zero result.

The paper states the complete `WeilIncomplete` and
`DeshouillersIwaniecLemma1` contracts, including quantifier order,
coprimality, modular inverses, floors and coefficient bounds. These are
explicit Lean hypotheses, **not estimates supplied with Lean proof terms here**.
Section 2.1 gives a prose deduction of the incomplete input from the
classical composite-modulus bound (Iwaniec–Kowalski, Corollary 11.12),
including the zero mode and long intervals. The former PRZZ
witness axiom is now derived from them. The source correspondence still
requires independent expert review.

## Reading order and verification levels

The current [local clean record](../checks/clean-verification-2026-11-10-local.json)
freshly compiles all 778 local modules (zero reused rows) and checks 4,405
axiom audits. Its linked [AF record](../checks/clean-verification-2026-11-10-af.json)
freshly builds all 101 required AF modules. Mathlib/package caches remain
fixed and reused; the explicit Weil/DI hypotheses are not thereby proved.
Older compiler records retain their original scope.

1. Sections 1–2: precise conditional conclusion and both external inputs.
2. Sections 3–4: exact fixed witness, height-dependent seven-vector family,
   all 49 ordered pairs, class-uniform Mellin masses, AFE residual assembly,
   shift orientation and the two admissible loss exponents.
3. Sections 5–7: arithmetic main-term identification, Cauchy derivatives,
   finite gate, exact auxiliary function, safe contours and actual counting.
4. Section 8 and [REVIEW_GUIDE.md](../docs/REVIEW_GUIDE.md): source contracts,
   recorded checks and independent-review questions.

| Artifact | Role and boundary |
| --- | --- |
| `manuscript.tex`, `manuscript.pdf` | Revised conditional proof guide, rebuilt together; not a report of completed human peer review. |
| `numerical_interval.py`, `verify.py` | Unchanged independent finite-functional calculation; neither an optimizer nor a formal proof of mpmath. |
| `certificate.json` | Four interval runs and exact fixed data unchanged; only the manuscript provenance hash is refreshed. |
| `SHA256SUMS` | Integrity of current paper-directory files, not mathematical validity. |
| [Render record](../checks/manuscript-render-verification.json) | Build version, source/PDF hashes, page count and visual-inspection scope; not a Lean rebuild. |

The [correspondence table](../docs/paper-correspondence.md) distinguishes
two hypothesis definitions, theorem contracts and the independently
computed decimal interval. The Lean gate is the coarser bound
`M_* ≤ 1.128201`; the counting proof uses the cap `1.128202`.
The narrow Python enclosure is not claimed to be that Lean theorem.

## Reproduce the finite certificate offline

Use Python 3.10 or later. Install the pinned dependency if necessary:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py --manifest
```

The script prints JSON and writes no files. After dependency installation
it uses no network. Compare stdout with `certificate.json`; source hashes
are part of the result. The runs use precision/order pairs (40,20),
(45,24), (55,24), (70,24). Every run passes the strict finite threshold.
Displayed decimal bounds are outward weakenings of the intervals,
not rounded midpoints. No zero table, CUE sample or private research
checkout is needed.

## Build the manuscript

From this directory:

```sh
tectonic -X compile manuscript.tex --keep-logs
```

The revised PDF was built with Tectonic 0.17.0, rendered with PyMuPDF
1.28.2, and inspected page by page. See the render record for exact
artifacts and checks. Standard TeX packages may require a network
download on first use. Alternatively run `pdflatex manuscript.tex`
twice and visually inspect that output. PDF byte equality across TeX
installations is not a mathematical reproducibility requirement.

## Questions requiring analytic review

These are specification and interpretation checks, not assertions that
the corresponding Lean connections remain unimplemented.

| Location | Review question |
| --- | --- |
| Hypothesis 1 / Section 2.1 | Check the prose completion argument from Iwaniec–Kowalski Corollary 11.12, including the Ramanujan zero mode, arbitrary interval and uniform epsilon loss. The resulting stronger square-root-gcd estimate implies the first-power-gcd contract; this implication is not formalized here. |
| Hypothesis 2 / Section 2.2 | Does DI Lemma 1 supply exactly the array class, filters, inverse phase and uniformity asserted here? The formula on p.310 was visually compared; this is not a new proof of the lemma. |
| Proposition 2 / Section 4 | Are the profile-class bounds, height-dependent support and all mixed coefficient slots modeled correctly, with constants preceding variable data? |
| Proposition 3 / Section 5 | Do the Euler-factor, Gamma and Mellin bridges produce precisely the density-oriented main term and the four finite kernels, including dual shift exchange? |
| Lemma 4 / Section 6 | Are the interval tail propagation and outward bounds sufficient? The program is supplied for independent reimplementation. |
| Lemma 5 / Section 7 | Are the exact auxiliary function, inward contours, boundary multiplicities and all-height AF count normalization faithful to the intended argument? |

The raw gcd kernel at `A+B=0` is not its holomorphic extension; the
negative-shift bidisc used here excludes that divisor. The v0.1.0
shift-placement correction is retained in Section 4.4 and
[STATUS.md](../docs/STATUS.md#v010-erratum-shift-placement-7-november-2026).
The historical tag and compiler records are not rewritten.

## Sources and boundaries

The published software snapshot is [v0.2.0](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0),
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490),
commit `8fbfbe376d879274c5be7e2f655551c967dfdf99`.
This bibliography/submission-metadata revision postdates the archived PDF;
it does not relabel or overwrite the frozen archive. The manuscript includes
author/contact details, MSC/keywords, data/code availability, funding/interest
declarations, acknowledgements and a substantive Claude/ChatGPT-Codex disclosure.
The [publication checklist](../docs/PUBLICATION.md) records the remaining
live JNT-guide/portal check and [metadata evidence](../checks/publication-metadata-verification.json).

The bibliography includes Weil, Harcos's prime-field exposition,
Iwaniec–Kowalski's composite-modulus corollary, the
DI paper (Acta Arithmetica **43**, 305–312), Wu, PRZZ and AF.
The original DI scan's Lemma 1 on p.310 was inspected for its displayed
formula and filters. Full BCHB original-source checking is not claimed.

Prior exploratory AI reviews are not human peer review. This package
makes no RH, simple-zero, global-optimality or priority claim. The revised
manuscript identifies the author as MASAMICHI IIZUMI, Miosync, Inc., Tokyo,
Japan, with the author-confirmed contact and declarations recorded in
[PUBLICATION.md](../docs/PUBLICATION.md). AI assistance is disclosed but
does not confer authorship. This post-release editorial update creates
no new software release or journal submission.
