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

## Optional Lean probes

The Lean files deliberately use AF as an external environment rather than vendoring its source and build products. Obtain and build the pinned upstream tree using its own instructions:

```sh
git clone https://github.com/anthropics/formal-math.git af
git -C af switch --detach 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
```

The pinned tag has the project at its root; newer upstream layouts need not match it. The required pins are recorded in [lean/dependencies.json](../lean/dependencies.json). Build the three import targets and their dependencies in that checkout, following upstream toolchain/cache setup:

```sh
cd af
lake build Zeta23.Analytic.RectangleLogDeriv Zeta23.XiPrime.Seam Zeta23.XiPrime.ZeroCount.Contour
cd ..
python3 tools/verify_lean.py --af af
```

If `lake` is not on PATH, add `--lake /path/to/lake`. The runner checks AF and mathlib commit identities and the selected AF source files, then invokes `lake env lean` for each of the six supplied files. It freshly compiles `BetaKernel` and `FiniteJet` into a temporary import directory before compiling `IntegralJet`, so the new module does not rely on stale local import artifacts. It performs no fetch, reset, checkout or package installation and does not write build products into AF. An existing modified dependency tree is not certified as a clean upstream build.

To save fresh output in an ignored location:

```sh
python3 tools/verify_lean.py --af af --output build/lean-verification.json
```

The committed [Lean check record](../checks/lean-verification.json) describes a successful existing-build run, not the full 88.45% theorem.

## Manuscript

The PDF and LaTeX source are unchanged copies of the five-page audit draft. To rebuild:

```sh
cd paper
tectonic -X compile manuscript.tex --keep-logs
```

Alternatively run `pdflatex manuscript.tex` twice. Standard packages may require a first-time network download. PDF bytes can differ between TeX installations; the root snapshot manifest intentionally detects such a change. Keep a rebuild in a separate copy if preserving the distributed manifest.

## Continuous integration

The [workflow](../.github/workflows/verify.yml) runs numerical and packaging checks on Python 3.10 and 3.12. Its third-party actions are pinned to commit hashes. It does not claim an AF build or a Lean proof of the final theorem.

The CI command is tested locally, but GitHub-hosted execution awaits an actual repository upload. Action configuration follows the official [checkout](https://github.com/actions/checkout) and [setup-python](https://github.com/actions/setup-python) documentation.

The [packaging check record](../checks/package-verification.json) records a clean archive extraction, installation into a fresh virtual environment, and reproduction from an unrelated working directory. Local execution used Python 3.12.4; the Python 3.10 CI job has not yet run. Synthetic hash tampering and Python optimization were both rejected by the wrapper.

## Integrity and changes

`paper/SHA256SUMS` is the original audit-bundle manifest. Root `SHA256SUMS` covers the entire prepared distribution, excluding itself and ignored runtime files. `provenance.json` records which artifacts are byte-identical copies.

When deliberately revising a mathematical source, review the change, regenerate its certificate as appropriate, and update manifests as a separate reviewed step. A verification command must never silently bless new file contents.
