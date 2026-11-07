# Reproduction instructions

## Numerical certificate

Use Python 3.10 or later with `mpmath==1.3.0`. The root requirements file points to the unchanged pinned requirements in `paper/`.

```sh
python3 -m pip install -r requirements.txt
python3 tools/verify_release.py
```

For the original JSON output alone:

```sh
python3 -B paper/verify.py --manifest
```

The wrapper checks the root manifest, rejects unexpected distributable files, runs the paper verifier, and compares its output byte-for-byte with `paper/certificate.json`. It neither overwrites that certificate nor regenerates accepted hashes. Do not use Python's `-O` option; the original verifier uses assertions.

The finite verifier performs exact rational checks and interval runs at precision/order pairs (40,20), (45,24), (55,24), (70,24). No optimizer or random-number generator is used.

## Lean verification

The zero-proportion entry point is [`WuProportion.lean`](../lean/WuProportion.lean); the explicit Weil/DI moment entry point is [`PRZZMomentOptimal.lean`](../lean/PRZZMomentOptimal.lean). The [7 November full local record](../checks/clean-project-verification-2026-11-07.json) contains fresh compiler outputs for all 698 local modules, with 3,971 axiom audits; the [paired scope record](../checks/clean-af-verification-2026-11-07.json) describes the fresh 101-module AF closure and post-compilation registry corrections/re-audit. Mathlib/package caches were reused. The earlier [187-module record](../checks/wu-proportion-verification.json) remains a historical incremental/replay record. To freshly compile **all** local modules directly with the corrected registry, use the full runner below.

The Lean files deliberately use AF as an external environment rather than vendoring its source and build products. Obtain and build the pinned upstream tree using its own instructions:

```sh
git clone https://github.com/anthropics/formal-math.git af
git -C af switch --detach 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
```

The pinned commit has the project at its root; newer upstream layouts need not match it. The required pins are recorded in [lean/dependencies.json](../lean/dependencies.json). Build the pinned upstream project following its toolchain/cache setup:

```sh
cd af
lake build
cd ..
python3 tools/verify_lean.py --af af
```

If `lake` is not on PATH, add `--lake /path/to/lake`. The runner checks AF and mathlib commit identities and the selected AF source files, then invokes `lake env lean` for all 698 currently registered local files. It freshly compiles all local import dependencies into a temporary directory. It performs no fetch, reset, checkout or package installation and does not write build products into AF. An existing modified dependency tree is not certified as a clean upstream build. Unset inherited `LEAN_PATH` to exclude unrelated local build caches; `--jobs 3` enables dependency-aware parallel compilation.

For a clean AF dependency rebuild with fixed Mathlib caches, use a detached worktree at the pinned AF commit, starting without its own `.lake/build`. Reuse only the pinned `.lake/packages` directory, not the old AF outputs. Build the 16 AF roots imported by local sources using `lake build Module:olean ...`; their transitive AF source closure contains 101 modules. Then run the full verifier against that isolated AF tree with `LEAN_PATH` unset. This is a fresh AF dependency-closure build, not a source rebuild of Mathlib or of unrelated AF targets. The original AF working tree need not be reset or cleaned.

### Earlier module-level records

The descriptions below concern earlier verification stages and individual modules, not remaining premises of the final proportion theorem. The final axiom boundary is the existing PRZZ input only, beyond the three standard axioms.

The `NumericalGate` audit covers the fixed exponential bounds and aggregate Taylor error. `RationalEvaluator` proves equality between executable rational arithmetic and the existing coefficient expression. `RationalBounds` checks the actual rational inequalities by `decide +kernel`, without `native_decide` or imported numerical data. `FixedCertificate.fixed_functional_gate` discharges the coefficient premise of the earlier scalar helper. Its axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`; it has no numerical or analytic premise. This completes the finite-functional inequality, not the arithmetic asymptotic or the final zero-proportion theorem.

The `PRZZAsymptotic` audit distinguishes its five elementary theorems from the six theorems that additionally use the existing PRZZ axiom. Its generic Cauchy-transfer theorem retains explicit regularity premises, now discharged by `ArithmeticRegularity`. The latter has twelve standard-three-only audits and one audit permitting exactly the existing PRZZ axiom in addition. `CompactShiftIntegral` has three standard-three-only audits; `LogarithmicBudget` has six. `GcdDecomposition`, `ZetaPoleScaling` and `HeightScaling` add eight, four and nine standard-three-only audits, respectively. The main-term transfer theorems still retain their explicit gcd-limit premise: exact direct/dual separation and outer-factor limits do not prove the arithmetic-sum-to-H-kernel asymptotic or the zero-counting conclusion.

To save fresh output in an ignored location:

```sh
python3 tools/verify_lean.py --af af --output build/lean-verification.json
```

The committed [Lean check record](../checks/lean-verification.json) describes a successful existing-build run, not the full 88.45% theorem.

## Readability documents

Generate the dependency graph, module table, paper correspondence and trust base with the same pinned AF checkout used for the library-manifest comparison:

```sh
python3 -B tools/generate_readability_docs.py --af /path/to/pinned-af
python3 -B tools/generate_readability_docs.py --check --af /path/to/pinned-af
python3 -B tools/test_readability_docs.py
```

Generation first checks the complete local Lean source set and its SHA-256 hashes against the captured compiler record, successful exit codes, and absence of `sorryAx` / compiler errors. Stale, missing or failed records stop generation; this consistency check is not a new Lean rebuild. `--check` writes only temporary output, not repository files or human correspondence input. Running it without the same `--af` option produces different trust-base content and fails the byte comparison.

The human-maintained `tools/paper_correspondence_manual.json` is read-only during ordinary rendering and checking. To explicitly add new manuscript labels (preserving existing entries), run:

```sh
python3 -B tools/gen_paper_correspondence.py --sync-manual
```

Review any such input changes and regenerate the documents before deliberately updating `SHA256SUMS`. The regression tests operate on temporary copies and cover read-only checks, stale/missing/failed evidence, explicit manual synchronization, and SVG label bounds. They require only the Python standard library.

## Manuscript

The PDF and LaTeX source are unchanged copies of the five-page audit draft. To rebuild:

```sh
cd paper
tectonic -X compile manuscript.tex --keep-logs
```

Alternatively run `pdflatex manuscript.tex` twice. Standard packages may require a first-time network download. PDF bytes can differ between TeX installations; the root snapshot manifest intentionally detects such a change. Keep a rebuild in a separate copy if preserving the distributed manifest.

## Continuous integration

The [workflow](../.github/workflows/verify.yml) runs numerical, packaging and readability-generator regression checks on Python 3.10 and 3.12. Its third-party actions are pinned to commit hashes. The readability tests use temporary fixtures and need no AF installation. The workflow does not claim an AF build or a Lean proof of the final theorem.

The commands are tested locally; GitHub-hosted job results are separate evidence and are not implied by adding a workflow step. Action configuration follows the official [checkout](https://github.com/actions/checkout) and [setup-python](https://github.com/actions/setup-python) documentation.

The [packaging check record](../checks/package-verification.json) records a clean archive extraction, installation into a fresh virtual environment, and reproduction from an unrelated working directory. Local execution used Python 3.12.4; the Python 3.10 CI job has not yet run. Synthetic hash tampering and Python optimization were both rejected by the wrapper.

## Integrity and changes

`paper/SHA256SUMS` is the original audit-bundle manifest. Root `SHA256SUMS` covers the entire prepared distribution, excluding itself and ignored runtime files. `provenance.json` records which artifacts are byte-identical copies.

When deliberately revising a mathematical source, review the change, regenerate its certificate as appropriate, and update manifests as a separate reviewed step. A verification command must never silently bless new file contents.
