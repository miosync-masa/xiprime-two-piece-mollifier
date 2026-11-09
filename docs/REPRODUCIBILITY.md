# Reproduction instructions

Updated: 9 November 2026. Read [REVIEW_GUIDE.md](REVIEW_GUIDE.md) first for
the conditional claim and [trust-base.md](trust-base.md) for the exact types.
Numerical reproduction, Lean verification, source/specification review and
manuscript rendering are different checks.

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
[current record](../checks/weil-di-proportion-verification.json) checks all
778 sources and 4,405 axiom outputs, but its final run freshly compiles only
one module and reuses 777 verified caches. It is **not** a fresh 778-module
build. These counts are evidence for that recorded source snapshot.

The alternative full runner always uses a temporary local output directory:

```sh
python3 -B tools/verify_lean.py --af /absolute/path/to/pinned-af \
  --output build/full-lean-verification.json --jobs 6
```

The runners do not install dependencies or rebuild AF/Mathlib automatically.
For a fresh AF source-closure build with fixed package caches, follow the
isolated-worktree procedure recorded in
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
The default record is `checks/weil-di-proportion-verification.json`.

The [manual correspondence JSON](../tools/paper_correspondence_manual.json)
is edited only deliberately; ordinary generation preserves it. Unmapped
statements and candidate-only matches are not inferred to be exact matches.
To add newly introduced manuscript labels while preserving existing entries:

```sh
python3 -B tools/gen_paper_correspondence.py --sync-manual
```

## Manuscript

The numerical algorithms and fixed witness are unchanged. The TeX has a
shift-placement erratum and its certificate provenance hash was updated;
the PDF predates the note. The paper bundle is not wholly byte-identical to
its original snapshot. Neither artifact narrates the complete current
Weil/DI-based proof. See [paper/README.md](../paper/README.md).

A TeX revision and render/visual review are separate from this documentation
refresh. To rebuild in a separate copy if preserving the distribution:

```sh
cd paper
tectonic -X compile manuscript.tex --keep-logs
```

Alternatively run `pdflatex manuscript.tex` twice. Packages may need an initial
network download. A rebuilt PDF must be checked page by page before delivery;
a successful compiler exit or a matching numerical certificate is not that check.

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
update hashes separately. For this docs-only refresh the Lean sources,
compiler JSONs, manuscript, numerical scripts and certificate are unchanged.
