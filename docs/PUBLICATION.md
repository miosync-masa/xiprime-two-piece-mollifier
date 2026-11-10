# Publication and reviewer checklist

Updated: 10 November 2026. The mathematical-source baseline is commit
[`2418fd5`](https://github.com/miosync-masa/xiprime-two-piece-mollifier/commit/2418fd5d334dbd7b4d99baaba5d8c9f41681884a),
pushed to `main` at [the repository](https://github.com/miosync-masa/xiprime-two-piece-mollifier).
The software release [v0.2.0](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0)
is published and archived at [doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490),
at commit `8fbfbe376d879274c5be7e2f655551c967dfdf99`.
This is a software archive, not journal publication, acceptance or a priority claim.
The present bibliography/submission-metadata revision does not overwrite that tag or archive.

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
5. Author-confirmed details: MASAMICHI IIZUMI, Miosync, Inc., Tokyo, Japan; public correspondence `m.iizumi@miosync.email`; no external funding and no competing interests. The affiliation expands the archived Zenodo label `miosync` as explicitly supplied by the author. These are in the manuscript, together with MSC 2020 codes, keywords, AF/Lean/Mathlib acknowledgements and the generative-AI declaration.
6. Inspect the staged files: no credentials, dependency checkout, private transcript, unrelated research material or build cache. Review manifest updates separately from mathematical changes.

## Policy and source checks for this revision

- Elsevier's [generative-AI policy](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals) was checked on 10 November 2026. The manuscript discloses Claude and ChatGPT/Codex, their substantive uses and author responsibility in a separate declaration before the references; it is not limited to a language-polishing claim.
- The [JNT guide for authors](https://www.sciencedirect.com/journal/journal-of-number-theory/publish/guide-for-authors) returned HTTP 403 to the checking tools. This revision therefore does not certify every current JNT-specific requirement. Before actual submission, check the live guide and portal for affiliation/postal-address fields, journal formatting, separate declarations, source files and any other required uploads. No postal address or country has been invented.
- Missing references were checked against publisher/author-hosted records and DOI metadata. Wu is cited as the 2015 Quarterly Journal of Mathematics article; the inspected preprint and its Section 3 are retained. BCHB bibliographic checking is not an independent analytic audit of the original proof.
- The [metadata record](../checks/publication-metadata-verification.json) records source URLs, verified release/tag/archive correspondence, author-confirmed fields and access limitations.

This documentation update makes no journal submission, announcement, new tag or release.
The claimed conclusion remains a conditional, multiplicity-counted proportion
strictly above 88.45%, not a simple-zero or global-optimality result.
