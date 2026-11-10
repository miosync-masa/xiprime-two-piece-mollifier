# Reproduction instructions

Updated: 10 November 2026. Read [REVIEW_GUIDE.md](REVIEW_GUIDE.md) first for
the conditional claim and [trust-base.md](trust-base.md) for the exact types.
Numerical reproduction, Lean verification, source/specification review and
manuscript rendering are different checks.

## Frozen release versus current editorial revision

The published software snapshot is [v0.2.0](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0),
commit `8fbfbe376d879274c5be7e2f655551c967dfdf99`,
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).
For that immutable distribution, check out the tag and use its own manifests
and reproduction instructions. The archived PDF and both clean-build records
were checked against the tag. The current bibliography/submission-metadata
revision leaves the complete Lean source tree unchanged but produces a
different PDF and different documentation/provenance hashes. Do not compare
the current PDF to the archived PDF's hash as though they were the same file.
The [publication-metadata record](../checks/publication-metadata-verification.json)
records the archive correspondence and subsequent editorial scope.

## Numerical certificate

Python 3.10 or later and `mpmath==1.3.0` are required. From the repository root:

```sh
python3 -m pip install -r requirements.txt
python3 -B tools/verify_release.py
```

The wrapper checks both package integrity and local Markdown links, runs the
finite verifier and compares its output byte-for-byte with the saved JSON.
It never regenerates accepted hashes or overwrites the certificate. After
installation, this check uses no network. Do not use Python's `-O` option.
For the original finite output alone:

```sh
python3 -B paper/verify.py --manifest
```

The four precision/order pairs are (40,20), (45,24), (55,24), (70,24).
No optimizer, zero table, CUE sample or private research checkout is used.
These checks do not establish the analytic reduction or validate mpmath
inside Lean. [FixedCertificate](../lean/FixedCertificate.lean) is the separate
kernel-checked finite gate, with a different, coarser enclosure.

## Lean verification

The current headline is [WuProportion](../lean/WuProportion.lean), with explicit
`WeilIncomplete` and `DeshouillersIwaniecLemma1` arguments. Its witness bridge
runs through [PRZZFamilyMomentOptimal](../lean/PRZZFamilyMomentOptimal.lean),
[PRZZWitnessBridge](../lean/PRZZWitnessBridge.lean) and
[PRZZProvedInput](../lean/PRZZProvedInput.lean). The older fixed-label
`PRZZMomentOptimal` is not the height-dependent family supplier.

Use the pins in [lean/dependencies.json](../lean/dependencies.json):
AF `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`, Lean `v4.33.0-rc2`.
AF is an external checkout; its source and build products are not vendored.
Obtain/build the pinned AF tree following that tree's own instructions:

```sh
git clone https://github.com/anthropics/formal-math.git af
git -C af switch --detach 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
cd af
lake build
cd ..
```

A **fresh local source build with pinned external caches** uses a new empty
scratch directory, no `--prebuilt`, and a new output outside committed records:

```sh
python3 -B tools/verify_finite_family_rows.py --target WuProportion --all-local \
  --af /absolute/path/to/pinned-af --build /absolute/path/to/new-empty-scratch \
  --output build/review-verification.json --jobs 6
```

Add `--lake /absolute/path/to/lake` if necessary. `--all-local` includes the
48 modules outside the 730-module headline import closure. The runner checks
all source/dependency/artifact hashes, every emitted axiom audit and the
printed headline hypothesis types. It rejects local analytic axiom declarations,
nonstandard axiom outputs, `sorryAx`, errors and missing audit coverage.

A reused scratch directory is accepted only after fingerprint validation;
`fresh_module_count` records how much was newly compiled in that run.
`--prebuilt` optionally accepts unchanged baseline modules only when their
whole local source closure matches the historical baseline. The accepted
[current local record](../checks/clean-verification-2026-11-10-local.json)
freshly compiles **all 778** sources, with **zero reused local rows**, and
checks all 4,405 printed axiom audits. Its linked
[AF record](../checks/clean-verification-2026-11-10-af.json) freshly builds
all 101 required AF modules in an isolated pinned worktree, with no old AF
outputs. Only pinned Mathlib/package caches are reused. The compile stages
took 190.253 seconds (AF) and 2,939.546 seconds (local, six worker slots);
these measurements do not guarantee future run times.
The [preceding interface-switch record](../checks/weil-di-proportion-verification.json)
is preserved unchanged: its one fresh module and 777 reused rows describe
that earlier invocation, not the current clean build.

The alternative full runner always uses a temporary local output directory:

```sh
python3 -B tools/verify_lean.py --af /absolute/path/to/pinned-af \
  --output build/full-lean-verification.json --jobs 6
```

The runners do not install dependencies or rebuild AF/Mathlib automatically.
To rebuild both the complete required AF source closure and every local source,
while reusing only pinned Mathlib/package caches, use the clean orchestrator:

```sh
python3 -B tools/verify_clean_build.py \
  --af /absolute/path/to/pinned-af \
  --packages /absolute/path/to/pinned-af/.lake/packages \
  --output-prefix build/new-clean-verification --jobs 6
```

It checks all package Git pins and tracked package sources, creates a new
detached AF worktree and an empty local output directory, unsets inherited
Lean search paths, disables downloadable build caches, and never passes
`--prebuilt`. It retains the worktree, outputs and raw logs for inspection.
The two output records have suffixes `-af.json` and `-local.json`; an existing
record at either path is rejected rather than overwritten. Elapsed times,
source/artifact hashes and every local compiler audit are recorded. The AF
count excludes cached package jobs; Mathlib source is not rebuilt.

The earlier isolated-worktree procedure is recorded in
[clean-af-verification-2026-11-07.json](../checks/clean-af-verification-2026-11-07.json).
It rebuilt 101 AF modules, not Mathlib or unrelated AF targets. The paired
[698-module local record](../checks/clean-project-verification-2026-11-07.json)
is historical and does not certify the subsequent 80 additions or interface
changes. Never overwrite historical JSONs to make them appear current.
Individual module milestones and old reproduction notes are archived in
[history.md](history.md#archived-module-level-verification-notes).

## Readability documents

Generate and check the reading aids with the same pinned AF checkout:

```sh
python3 -B tools/generate_readability_docs.py --af /absolute/path/to/pinned-af
python3 -B tools/generate_readability_docs.py --check --af /absolute/path/to/pinned-af
python3 -B tools/test_readability_docs.py
python3 -B tools/test_polarization_audit.py
```

Generation requires a complete source-set/hash match with the current accepted
compiler record and successful compiler outputs. Stale/missing/failed evidence
stops generation. This is not a new Lean rebuild. `--check` writes only to a
temporary directory and cannot be combined with the writing `--sync-manual`.
The default local record is `checks/clean-verification-2026-11-10-local.json`;
the default AF record is `checks/clean-verification-2026-11-10-af.json`.

The [manual correspondence JSON](../tools/paper_correspondence_manual.json)
is edited only deliberately; ordinary generation preserves it. Unmapped
statements and candidate-only matches are not inferred to be exact matches.
To add newly introduced manuscript labels while preserving existing entries:

```sh
python3 -B tools/gen_paper_correspondence.py --sync-manual
```

## Manuscript

The numerical algorithms and fixed witness are unchanged. The TeX and PDF
were revised together on 10 November 2026 for the conditional Weil/DI proof,
including the shift-placement correction. Only the manuscript provenance
hash in the numerical certificate is refreshed; its exact checks and all
interval results are unchanged. See [paper/README.md](../paper/README.md)
and [the PDF render record](../checks/manuscript-render-verification.json).

To rebuild in a separate copy if preserving the distribution:

```sh
cd paper
tectonic -X compile manuscript.tex --keep-logs
```

This revision used Tectonic 0.17.0 and PyMuPDF 1.28.2 to render every page,
then visual inspection. Alternatively run `pdflatex manuscript.tex` twice.
Later narrow edits can preserve this visual coverage by inspecting changed
pages and checking that the other rendered PNG hashes are identical to the
previously inspected pages, as recorded in the current render record.
Packages may need an initial network download. Each rebuilt PDF should be
checked page by page; a compiler exit or numerical certificate is not that check.

## Continuous integration and integrity

The [workflow](../.github/workflows/verify.yml) is configured for Python 3.10
and 3.12 and pinned third-party actions. It checks the finite package and
readability regression tests, not a Lean/AF source build or human peer review.
Local success does not imply any particular GitHub-hosted run succeeded.
[package-verification.json](../checks/package-verification.json) is the older
clean-extraction packaging record; do not interpret it as a current CI result.

`paper/SHA256SUMS` covers the current paper-directory files. Root `SHA256SUMS`
covers the full distribution except itself and runtime files.
[provenance.json](../provenance.json) retains dated historical claims with a
current documentation pointer; it is not a replacement for the manifests.
After a deliberate edit, inspect changes, regenerate affected documents and
update hashes separately. In this manuscript revision the Lean sources,
compiler JSONs and numerical scripts are unchanged. The numerical certificate
diff is restricted to its manuscript provenance hash. Rendering and editorial
checks do not replace the accepted Lean verification record.
