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

The zero-proportion entry point is [`WuProportion.lean`](../lean/WuProportion.lean); the explicit Weil/DI moment entry point is [`PRZZMomentOptimal.lean`](../lean/PRZZMomentOptimal.lean). The [7 November full local record](../checks/clean-project-verification-2026-11-07.json) contains fresh compiler outputs for the **pre-erratum** 698 local modules, with 3,971 axiom audits; the [paired scope record](../checks/clean-af-verification-2026-11-07.json) describes the fresh 101-module AF closure and post-compilation registry corrections/re-audit. Mathlib/package caches were reused. These records are historical, not evidence for the subsequently changed interface. The [witness-only migration record](../checks/witness-only-proportion-verification.json) is historical. The current [Weil/DI dependency-switch record](../checks/weil-di-proportion-verification.json) checks the new public path and every local source against compiled output and direct dependency/artifact fingerprints. See the [shift-placement erratum](STATUS.md#v010-erratum-shift-placement-7-november-2026). To freshly compile **all** current local modules, use the full runner below.

The Lean files deliberately use AF as an external environment rather than vendoring its source and build products.

The current headline theorems take `WeilIncomplete` and
`DeshouillersIwaniecLemma1` as explicit arguments. The former witness input
is a theorem in `PRZZProvedInput`, not an axiom. `PRZZAsymptoticCore` separates
definitions and elementary regularity from the high-level analytic transfer.
The four final axiom audits and the printed theorem signatures are checked;
all intermediate printed audits reject nonstandard axioms and `sorryAx`.

For a fresh source build of all current local modules with pinned external
caches, use a new empty scratch directory (omit `--prebuilt`):

```sh
python3 -B tools/verify_finite_family_rows.py --target WuProportion --all-local \
  --af /path/to/pinned-af --build /path/to/new-empty-scratch \
  --output /path/to/weil-di-proportion-verification.json --jobs 6
```

`--all-local` also checks modules outside the headline import closure.
Reusing a previous scratch directory is allowed only after matching source,
direct-dependency and artifact hashes; `fresh_module_count` distinguishes
that reuse from newly compiled modules. `--prebuilt` additionally permits
unchanged baseline modules only when their full local source closure still
matches the historical record. A successful cached run is not a fresh
full-project rebuild. AF and Mathlib outputs remain external pinned caches.
Historical verification JSONs are never overwritten.

Obtain and build the pinned upstream tree using its own instructions:

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

If `lake` is not on PATH, add `--lake /path/to/lake`. The runner checks AF and mathlib commit identities and the selected AF source files, then invokes `lake env lean` for all 778 currently registered local files. It freshly compiles all local import dependencies into a temporary directory. It performs no fetch, reset, checkout or package installation and does not write build products into AF. An existing modified dependency tree is not certified as a clean upstream build. Unset inherited `LEAN_PATH` to exclude unrelated local build caches; `--jobs 3` enables dependency-aware parallel compilation. The dependency-switch record distinguishes fresh compilation from verified cache reuse; it must not be described as a fresh 778-module rebuild unless every row is fresh.

For a clean AF dependency rebuild with fixed Mathlib caches, use a detached worktree at the pinned AF commit, starting without its own `.lake/build`. Reuse only the pinned `.lake/packages` directory, not the old AF outputs. Build the 16 AF roots imported by local sources using `lake build Module:olean ...`; their transitive AF source closure contains 101 modules. Then run the full verifier against that isolated AF tree with `LEAN_PATH` unset. This is a fresh AF dependency-closure build, not a source rebuild of Mathlib or of unrelated AF targets. The original AF working tree need not be reset or cleaned.

### Quantitative Mellin-class verification

Use the scoped runner above with `--target PRZZMellinInterval` or `--target PRZZProfileMellin` and distinct `--output` paths. The records [mellin-interval-verification.json](../checks/mellin-interval-verification.json) and [profile-mellin-verification.json](../checks/profile-mellin-verification.json) audit the general-support estimate and the common-jet DI class supplier. Constants precede the varying profile and support scale; the full profile-family moment estimate is still a separate obligation. Older records retain their original hashes, including before the documentation-only pole warning added to `PRZZInterface`.

For the actual class-uniform HB small-source, residual-variation and signed DI suppliers, use `--target PRZZClassDI`. The [class-hb-verification.json](../checks/class-hb-verification.json) record covers the three new modules and their exact import closure; it is not a full profile-family moment or whole-project rebuild.

For class-uniform free Type I, the original three-case classifier and independent-label mixed dyadic row aggregation, use `--target PRZZClassRows`. The [class-rows-verification.json](../checks/class-rows-verification.json) record retains the complete dependency and compiler-output provenance. The finite row budget has not yet been substituted into a full mixed-profile moment bound.

For the integrated mixed literal budget and its optimal dyadic absorption, use `--target PRZZClassLiteral`; [class-literal-verification.json](../checks/class-literal-verification.json) checks its 328-module closure. For the actual direct replacement and complete zeta-to-W defect integral, use `--target PRZZMixedReplacement` and `--target PRZZMixedDefect`; their [replacement](../checks/mixed-replacement-verification.json) and [defect](../checks/mixed-defect-verification.json) records check 233 and 234 modules. All seventeen audits in the four new modules are standard-three-only. Fixed AF/Mathlib outputs and source/fingerprint-verified local caches are reused, with freshly compiled targets recorded separately. These estimates do not yet supply the full mixed post-Poisson moment bound or discharge the witness axiom.

For the complete mixed Poisson model and its insertion into the original mixed moment equation, use `--target PRZZMixedMoment`. The [mixed-poisson-moment-verification.json](../checks/mixed-poisson-moment-verification.json) record covers its 342-module closure. The two new modules have thirteen standard-only audits, including actual defect integrability, identification of the limiting error integral, the complete collective-field limit and the height-dependent witness-family substitution. This is an evaluated AFE error limit, not a bound for the retained collective Poisson field or a full mixed moment theorem.

For the actual mixed positive Poisson-cell identification and its class-uniform Weil/DI bound at every prescribed positive height-loss exponent, use `--target PRZZClassPoisson`. The [class-poisson-verification.json](../checks/class-poisson-verification.json) record audits eight standard-only theorems, including the actual spatial-partition class supplier. The source-scale and arithmetic-support premises remain explicit. This positive-cell verification does not establish the optimal bound for the full collective Poisson field.

For width-six mixed positive cells, actual rounded/body cutoffs and the outer `d,Q,V,M` aggregation, use `--target PRZZClassPositiveGrid`. For the same two positive AFE branches with the genuine Gamma-multiplied dual time profile, use `--target PRZZClassPairedGrid`. Their records are [class-positive-grid-verification.json](../checks/class-positive-grid-verification.json) and [class-paired-grid-verification.json](../checks/class-paired-grid-verification.json). The five new modules have twelve standard-only theorem audits. The fixed-profile width-six frequency estimate was already present; these modules connect it to the varying mixed cutoff class. The paired positive-body bound does not estimate all remaining negative, tail, boundary, freezing or zero-frequency components.

For mixed negative cells and both signs in both AFE branches, use `--target PRZZClassPairedSignedGrid`. The [class-paired-signed-grid-verification.json](../checks/class-paired-signed-grid-verification.json) record includes the ten new spatial-cap, negative-literal/cell/grid and signed/paired-grid modules, with 29 standard-only audits. Arithmetic suppliers require only the spatial norm cap; reflected spatial support is not falsely asserted positive. The physical integral retains its positive-support class. Rounded/body cutoffs and both frequency signs are included, but mixed tails, boundary/freezing and zero-frequency corrections are not yet bounded by this central-body result.

For the actual original mixed `zeroMismatch`, including primal/dual spatial boundaries and omitted-gap grids, use `--target PRZZClassZeroCorrection`. The [class-zero-correction-verification.json](../checks/class-zero-correction-verification.json) record audits four new modules and sixteen standard-only outputs. `family_power` supplies the true height-dependent witness basis and covers all 49 ordered pairs with the common coefficient cap 84; `arithmetic_bound` inserts the evaluated correction into the original arithmetic residual. The nonzero Fourier/freezing remainders and complete moment estimate are not supplied by this zero-frequency result.

For common-cap nonzero Fourier tails and actual active freezing row integrals, use `--target PRZZCappedWindowField` and `--target PRZZCappedFreezeBudget`, with separate outputs. The [window-field](../checks/capped-window-field-verification.json) and [freezing-budget](../checks/capped-freeze-budget-verification.json) records check the seven new modules and 24 standard-only audits. Constants precede the arbitrary coefficient slots; the physical cutoff profiles remain fixed. The true Gamma-weighted dual freezing branch is supplied by `paired_mixed_bound`. This is not yet the strict-mask/common-body-cutoff identification with the whole exhaustive remainder.

For the exact strict-mask/source-tail identification and evaluated transfer to the common Fourier cutoff, use `--target PRZZCappedTailBand`. The [capped-tail-band-verification.json](../checks/capped-tail-band-verification.json) record checks five new modules and 26 standard-only compiler audits. `mixed_tailBand_target` evaluates the actual reconstructed paired tailBand; `original_moment_split` returns the exact residual sum to the original mixed moment/literal-model equation. The strict freezing, discarded and collective large-spatial terms are retained there, not declared bounded by that equality.

For the original reconstructed residual with common-cap mixed coefficients, use `--target PRZZCappedRemainder`. The [capped-remainder-verification.json](../checks/capped-remainder-verification.json) record covers the strict native freezing identification and outer grids, valued selected discarded IBP (including genuine Gamma jets), collective large-spatial pruning and their actual `remainderPair` bound. The exact moment equation retains the separate AFE model defect; this check does not discharge the public witness input.

For the actual AFE replacement/residual combination, both exhaustion removals and density-oriented main-kernel comparison, use `--target PRZZCappedMainTerm`. The [capped-main-term-verification.json](../checks/capped-main-term-verification.json) record includes `PRZZCappedMomentBridge`. The final reduction retains the original nonzero central collectors and the separate integrated `gammaDefect`; it does not claim their identification with class-uniform Weil/DI grids or discharge the public witness axiom.

For the exact original mixed nonzero collector to signed body-grid identity, use `--target PRZZCentralGridIdentity` and a separate `--output checks/central-grid-identity-verification.json`. Its seven audits retain the actual common-to-row cutoff transfer and Fourier tail, with both original AFE branches and unchanged coefficient order. This identifies the arithmetic-label body with the evaluated grid; it does not yet supply the witness-profile absorption or bounds for the retained corrections.

For actual height-dependent basis absorption and the common 49-pair Weil/DI body bound, use `--target PRZZBasisGridBound --output checks/basis-grid-bound-verification.json`. The closure includes `PRZZBasisGridCutoff`. This supplies smooth normalized profiles for all windows through `Q<=2Y` and the original signed-body bound for every positive loss exponent. The common-J tail convergence is fixed-height only; the exact transfer-plus-tail body remainder is retained and is not asserted to satisfy a uniform bound by this check.

For the evaluated actual paired body tail with common-cap coefficients, use `--target PRZZCappedBodyTail --output checks/capped-body-tail-verification.json`. Its closure includes the common-cap window-transfer, subunit and native body-mass suppliers. `mixed_bound` retains both true Gamma branches and the strict original masks; `family_bound` substitutes the height-dependent seven-vector boxes, and `nonzero_reduction` returns the bound to the original nonzero collector for every common Fourier cutoff. This closes the body-tail obligation of the preceding scoped stage, not the full moment/public witness-input bridge.

For the complete actual height-dependent finite-family moment estimate, use `--target PRZZFamilyMomentOptimal --output checks/family-moment-optimal-verification.json`. The closure includes `PRZZBasisPairedBody` and `PRZZCappedGammaDefect`. `moment_bound` supplies every positive final loss under explicit Weil/DI hypotheses, before both independent radius-two profile vectors. `witness_uniform_normalized` uses the actual floor cutoff and tau=1/4000000. That scoped stage did not yet rewire the public input; the dependency-switch check at the top of this page now covers the replacement and headline chain.

### Earlier module-level records

For the exact 49-pair moment assembly and evaluated density-oriented main-kernel defect, run the scoped checker with `--target PRZZFamilyMoment` and `--target PRZZKernelComparison`, respectively, using the same `--af`, `--build`, `--output` options as above. The target is freshly compiled; dependency-cache reuse requires matching source hashes, direct dependency fingerprints and artifact hashes. The current records are [family-moment-verification.json](../checks/family-moment-verification.json) and [kernel-comparison-verification.json](../checks/kernel-comparison-verification.json). Run `python3 -B tools/test_polarization_audit.py` to exercise exact audit coverage, analytic-axiom/error rejection and the complete topological local-source registry. These checks do not supply the remaining all-mixed-pair moment bound.

The descriptions below concern earlier verification stages and individual modules. Their then-current witness-only axiom boundary is historical. The current final theorems instead take explicit Weil/DI hypotheses and have standard-only axiom audits.

The `NumericalGate` audit covers the fixed exponential bounds and aggregate Taylor error. `RationalEvaluator` proves equality between executable rational arithmetic and the existing coefficient expression. `RationalBounds` checks the actual rational inequalities by `decide +kernel`, without `native_decide` or imported numerical data. `FixedCertificate.fixed_functional_gate` discharges the coefficient premise of the earlier scalar helper. Its axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`; it has no numerical or analytic premise. This completes the finite-functional inequality, not the arithmetic asymptotic or the final zero-proportion theorem.

In the historical 698-module record, the `PRZZAsymptotic` audit distinguished its five elementary theorems from the six theorems that additionally use the existing PRZZ axiom. Its generic Cauchy-transfer theorem retains explicit regularity premises, now discharged by `ArithmeticRegularity`. The latter has twelve standard-three-only audits and one audit permitting exactly the existing PRZZ axiom in addition. `CompactShiftIntegral` has three standard-three-only audits; `LogarithmicBudget` has six. `GcdDecomposition`, `ZetaPoleScaling` and `HeightScaling` add eight, four and nine standard-three-only audits, respectively. The main-term transfer theorems still retain their explicit gcd-limit premise: exact direct/dual separation and outer-factor limits do not prove the arithmetic-sum-to-H-kernel asymptotic or the zero-counting conclusion.

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

The reading aids now use the current all-local source/fingerprint-checked dependency-switch record, not the historical 698-module record. The source-set/hash guard still rejects missing, extra, stale or failed entries. Never bypass the guard or relabel historical outputs as current.

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
