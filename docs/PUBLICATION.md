# Publication and reviewer checklist

Updated: 10 November 2026. The mathematical-source baseline is commit
[`2418fd5`](https://github.com/miosync-masa/xiprime-two-piece-mollifier/commit/2418fd5d334dbd7b4d99baaba5d8c9f41681884a),
pushed to `main` at [the repository](https://github.com/miosync-masa/xiprime-two-piece-mollifier).
This page does not certify a journal submission, acceptance, release or priority.

## Existing package decisions

- [LICENSE.md](../LICENSE.md) supplies the MIT license and copyright notice for MASAMICHI IIZUMI. This page assigns no new license or manuscript authorship.
- The [current conditional theorem and audit boundary](REVIEW_GUIDE.md) use explicit Weil/DI hypotheses, not a PRZZ analytic axiom.
- Historical tags, compiler records and development reports are retained. Their old analytic inputs are not current assumptions.
- The numerical verifier and fixed witness remain unchanged; updated documentation and TeX provenance mean the entire paper bundle is not byte-identical to its initial snapshot.

## Before sending to reviewers

1. Read [REVIEW_GUIDE.md](REVIEW_GUIDE.md) and state the explicit hypotheses and multiplicity convention in the cover letter.
2. Choose the exact source commit or archive being sent and include its manifests and [verification scope](REPRODUCIBILITY.md). A passing numerical CI is not a Lean-build or peer-review badge.
3. Use the revised 10 November TeX/PDF together and include the [render record](../checks/manuscript-render-verification.json). They describe the current conditional Weil/DI route, not an unconditional theorem or completed expert review.
4. Complete the independent specification/source correspondence review and the candidate paper-to-Lean mapping. Neither is certified by a standard-only axiom list.
5. Confirm author names, affiliations, acknowledgements, citation metadata and submission venue with the maintainer. Do not infer authorship from a copyright notice or invent metadata.
6. Inspect the staged files: no credentials, dependency checkout, private transcript, unrelated research material or build cache. Review manifest updates separately from mathematical changes.

This documentation update makes no submission, announcement, new tag or release.
The claimed conclusion remains a conditional, multiplicity-counted proportion
strictly above 88.45%, not a simple-zero or global-optimality result.
