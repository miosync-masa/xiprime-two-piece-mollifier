# Expert audit package for the 88.45 percent xi prime candidate

This package fixes one explicit two-component mollifier. It contains no optimizer and needs no CUE sample, zero table, private repository, or earlier internal report.

The claim submitted for verification is

\[
\liminf_{T\to\infty}N_{\xi',c}(T)/N(T)>.8845.
\]

Both counts include multiplicity. This is not a simple-zero claim. The manuscript is a proof draft for expert review, not a declaration of peer-reviewed validity or publication priority. Authorship and affiliations are intentionally not assigned in this package.

## Read first

1. `manuscript.pdf` or `manuscript.tex`: definitions, exact witness, counting lemma, published moment input, specialized kernel, and finite certificate.
2. `numerical_interval.py`: the compact interval evaluator, copied without numerical changes from the previously checked fixed-witness evaluator.
3. `verify.py`: exact rational admissibility, the four complete Laurent kernel identities, four interval runs, and optional package-integrity checking.
4. `certificate.json`: captured output of `verify.py`. The certificate covers the displayed finite functional, not the analytic reduction.

The main-term inequalities in the manuscript are outward decimal weakenings of the computed intervals. They are not rounded midpoints treated as bounds.

## Reproduce offline

Use Python 3.10 or later. Install the single pinned dependency if necessary:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py --manifest
```

The script prints JSON and writes no files. Internet access is not used by the verification. Compare the printed JSON with `certificate.json`; source hashes are part of the output. `SHA256SUMS` covers all delivered files other than itself.

The runs use 40 digits with Taylor order 20, and 45, 55, and 70 digits with order 24. All pass the strict 88.45-percent threshold. The normalized midpoint display agrees to 22 significant digits in the three order-24 runs; the rigorous information is the interval, not that agreement.

## Build the manuscript

No nonstandard font or local TeX macro is required. Either run `pdflatex manuscript.tex` twice, or use:

```sh
tectonic -X compile manuscript.tex --keep-logs
```

The delivered PDF was built with Tectonic 0.17.0 and visually inspected page by page. A fresh Tectonic installation may need network access to fetch standard TeX packages on its first build. PDF byte equality across TeX installations is not required for mathematical reproducibility.

## Questions requiring analytic review

| Location in manuscript | Exact question |
| --- | --- |
| Lemma 2, phase-counting step | Does the direct auxiliary function, with only a nonzero linear odd term in its centered polynomial, give the stated multiplicity-counted inequality with the specified boundary convention? |
| Lemma 2, right boundary and exact V | Are the absolute-convergence normalization and L2 comparison adequate before Jensen, without importing a negative-log-tail estimate? |
| Section 3, PRZZ Theorem 4.1 | Does the third coefficient case and its profile extension cover all four pairings of the unrestricted convolution at the fixed length, uniformly in the required complex shifts? |
| Proposition 3 | Does the published Euler-factor/contour analysis give precisely the four expanded kernels, including inverse Mellin powers and the dual shift exchange? |
| Lemma 4 | Are the interval tail propagation and outward bounds sufficient? The full code is supplied for reimplementation. |
| Lemma 2, globalization | Is the fixed-window-then-finite-dyadic-sum limiting order adequate for the claimed liminf? |

Prior separate AI contexts reviewed the analytic transplantation and the leading-pole implementation. They prompted explicit constructions of the counting auxiliary function and dyadic globalization. This is not a report of human peer review. A reviewer should not treat agreement among those checks as proof of the analytic interfaces above.

## Sources and literature scope

- X. Wu, [arXiv:1206.3737v2](https://arxiv.org/pdf/1206.3737v2), Section 3 and the Littlewood boundary argument in Section 2.
- K. Pratt, N. Robles, A. Zaharescu and D. Zeindler, [arXiv:1802.10521v3](https://arxiv.org/pdf/1802.10521v3), Theorem 4.1, Section 6 and p.45.
- L. Alpöge and R. Furman, [arXiv:2608.13637v2](https://arxiv.org/html/2608.13637v2#S7.SS3), Remark 7.1, for the distinct simple-and-on-line comparison.

The preceding literature search, including 2026 materials, did not locate a scholarly implementation of this precise fixed-xi-prime optimization. It did locate a [public proposal of the modern-mollifier transplant idea](https://github.com/teal-sea/zeta-lab/blob/main/hunts/rogue_frontier/IDEA_PORTFOLIO.md). No assertion of nonexistence or priority follows from the search. The present review should focus on the explicit witness and its analytic proof.

## Boundaries of the package

No RH assumption, root-Palm estimate, high-moment small-value hypothesis, simple-zero theorem, or global numerical optimality assertion is used. The interval library itself is not formally verified. The analytic conclusions are not certified by running the Python script. Nothing has been sent to a third party.
