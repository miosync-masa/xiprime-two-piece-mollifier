# Reproduction instructions

Updated: 11 November 2026. Start with [REVIEW_GUIDE.md](REVIEW_GUIDE.md)
for the conditional claim and [trust-base.md](trust-base.md) for exact types,
axiom outputs and dependency pins. Numerical checks, Lean builds and independent
specification review are separate checks.

## Version to reproduce

The frozen release is [v0.2.0](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0),
commit `8fbfbe376d879274c5be7e2f655551c967dfdf99`,
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).
Use that tag's own instructions and manifests to reproduce the archive.
The current manuscript and documentation postdate it; the Lean sources are
unchanged, but the current PDF and documentation hashes differ.
For a current checkout, record its exact commit and any uncommitted changes.

## Numerical certificate

Requires Python 3.10 or later and `mpmath==1.3.0`. From the repository root:

```sh
python3 -m pip install -r requirements.txt
python3 -B tools/verify_release.py
```

Expected: three `PASS` lines for distribution hashes/local links, exact rational
checks/four interval runs and byte-for-byte certificate JSON equality. After
dependency installation, verification is offline. Do not use Python's `-O`.
The wrapper does not rewrite accepted hashes or the certificate. To inspect
the original finite output alone:

```sh
python3 -B paper/verify.py --manifest
```

This does not prove the analytic reduction or the Weil/DI inputs.
[FixedCertificate](../lean/FixedCertificate.lean) is the separate Lean gate.

## Lean verification

Use [lean/dependencies.json](../lean/dependencies.json): AF
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`, Lean `v4.33.0-rc2`.
Install the toolchain and obtain/build AF following its own instructions:

```sh
git clone https://github.com/anthropics/formal-math.git af
git -C af switch --detach 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
cd af
lake build
cd ..
```

For **all 778 local sources and all 101 required AF modules freshly built**,
with only pinned Mathlib/package caches reused, run:

```sh
python3 -B tools/verify_clean_build.py \
  --af /absolute/path/to/pinned-af \
  --packages /absolute/path/to/pinned-af/.lake/packages \
  --output-prefix build/new-clean-verification --jobs 6
```

The orchestrator checks package pins, creates an isolated detached AF worktree
and empty local output directory, excludes old AF outputs and inherited Lean
search paths, disables downloadable build caches and never uses `--prebuilt`.
It retains raw logs/artifacts and writes `-af.json` and `-local.json` records;
existing output records are rejected rather than overwritten. Mathlib sources
and unrelated AF targets are not rebuilt.

For a **local-only fresh build** against an already built pinned AF checkout:

```sh
python3 -B tools/verify_finite_family_rows.py --target WuProportion --all-local \
  --af /absolute/path/to/pinned-af --build /absolute/path/to/new-empty-scratch \
  --output build/review-verification.json --jobs 6
```

Use a new empty scratch directory and no `--prebuilt`; add
`--lake /absolute/path/to/lake` if needed. Reused scratch outputs require
fingerprint validation; `fresh_module_count` reports actual fresh compilations.
The runner checks source/dependency/artifact hashes, audit coverage and headline
types, rejecting local analytic axioms, nonstandard axiom outputs, `sorryAx`
and compiler errors. The four headline audits should list only
`propext, Classical.choice, Quot.sound`; the theorem types still have explicit
Weil/DI arguments. Standard-only axiom output does not prove those arguments.

Accepted evidence: [local clean record](../checks/clean-verification-2026-11-10-local.json)
(778 fresh, zero reused, 4,405 audits; 730 modules in the headline closure) and
[AF clean record](../checks/clean-verification-2026-11-10-af.json)
(101 fresh, no old AF outputs; pinned package caches reused).
Compile stages took 2,939.546 seconds locally and 190.253 seconds for AF,
with six local workers; these are measurements, not rerun guarantees.
Historical compiler JSONs remain unchanged and do not certify later sources.

## Generated reading aids

With the same pinned AF checkout:

```sh
python3 -B tools/generate_readability_docs.py --check --af /absolute/path/to/pinned-af
python3 -B tools/test_readability_docs.py
python3 -B tools/test_polarization_audit.py
```

Generation requires the complete current source-set/hash match and successful
compiler evidence; it is not a new Lean build. `--check` is read-only.
To regenerate deliberately, omit `--check`. Ordinary generation preserves
[manual paper correspondence](../tools/paper_correspondence_manual.json);
new labels require an explicit `gen_paper_correspondence.py --sync-manual`.

## Manuscript and integrity

See [paper/README.md](../paper/README.md) and the
[render record](../checks/manuscript-render-verification.json) for the current
TeX/PDF, compiler version, artifact hashes and visual-inspection scope.
To rebuild, preferably in a separate copy:

```sh
cd paper
tectonic -X compile manuscript.tex --keep-logs
```

The current render used Tectonic 0.17.0 and PyMuPDF 1.28.2; alternatively run
`pdflatex manuscript.tex` twice. Initial package downloads may need a network.
Inspect the rebuilt pages; PDF byte equality across TeX installations is not
required, and a successful compile is not a visual check.

Root `SHA256SUMS` covers the distribution except itself/runtime files;
`paper/SHA256SUMS` covers the paper bundle. After deliberate edits, review
manifest changes separately and rerun the release verifier. Repository
[CI](../.github/workflows/verify.yml) checks the finite package and documentation
tests, not a fresh Lean/AF build or human peer review.
Supplementary development history is in [STATUS.md](STATUS.md),
[history.md](history.md) and [RELEASE_NOTES.md](RELEASE_NOTES.md).
