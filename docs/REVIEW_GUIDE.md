# Reviewer entry point

Updated: 10 November 2026. Mathematical-source baseline:
[`2418fd5`](https://github.com/miosync-masa/xiprime-two-piece-mollifier/commit/2418fd5d334dbd7b4d99baaba5d8c9f41681884a).
This guide organizes the existing evidence; it is not an independent analytic
audit, a new mathematical proof or a record of human peer review.

The frozen software release is [v0.2.0](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0),
commit `8fbfbe376d879274c5be7e2f655551c967dfdf99`, archived at
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).
Its entire `lean/` tree is identical to the mathematical baseline above.
The current manuscript's bibliography, submission metadata and reviewer
clarifications postdate that archive; its revised PDF does not overwrite
the frozen release PDF. See the [metadata checks](../checks/publication-metadata-verification.json).

## 1. Exact claim and remaining hypotheses

For AF's actual total and critical-line xi-prime zero counts, **with analytic
multiplicity**, `XiPrime8845.WuProportion.strict_proportion` proves

```text
WeilIncomplete → DeshouillersIwaniecLemma1 →
  ∃ b > 0.8845, ∀ sufficiently large real X, b * Ncount 0 X ≤ N0 0 X.
```

`ratio_eventually_gt` gives the corresponding eventual strict quotient
inequality. Read the exact [Lean statement](../lean/WuProportion.lean) and
its verbatim statement/output in [trust-base.md](trust-base.md).
The count is not a simple-zero count. No RH, localized counting gate,
endpoint-tightness premise or numerical JSON input is added to the headline.

The two hypotheses are the **exact propositions** in
[PRZZKloostermanInputs.lean](../lean/PRZZKloostermanInputs.lean):

- `WeilIncomplete`: an unweighted incomplete inverse-phase sum bound,
  with its gcd factor, unrestricted starting point/length and `1+H/q`
  factor. For every positive epsilon the constant precedes all sum data.
  It is a completion specification, not simply the prime-field statement
  `WeilPrime`. Prime-power estimates, CRT and completion are not proved here
  as a derivation of this input from `WeilPrime`.
- `DeshouillersIwaniecLemma1`: the stated four-length sum bound, with the
  constant chosen before the positive integer `rho`, the lengths and every
  coefficient array satisfying the unit norm cap. Check floors, coprimality
  conditions and the placement of the absolute value against the source.

These are established estimates in the literature, not new conjectures;
the formal qualification is that their proofs are not supplied in Lean here.
The manuscript gives the completion deduction and a qualified epsilon-power
loss absorption argument for DI's rho-uniformity. Those prose arguments
do not replace independent source-to-specification review.
Neither proposition is supplied with an inhabitant here. The class
`PRZZProvedInput.DeepInputs` only bundles them for intermediate theorems;
it is not a default instance asserting them.

The four headline `#print axioms` outputs contain only
`propext`, `Classical.choice`, `Quot.sound`. This means **no additional
analytic axiom is used**, not that the two theorem arguments are proved.

## 2. Recommended reading route

1. [WuProportion](../lean/WuProportion.lean): conclusion, explicit inputs,
   multiplicity convention and the printed types of the two headline forms.
2. [PRZZKloostermanInputs](../lean/PRZZKloostermanInputs.lean): the exact
   external specifications and their source notes. Their mathematical
   validity/source correspondence is an independent review obligation.
3. [PRZZProvedInput](../lean/PRZZProvedInput.lean) and
   [PRZZWitnessBridge](../lean/PRZZWitnessBridge.lean): the former public
   witness axiom is now a theorem. The bridge constructs a smooth plateau,
   identifies the all-real-time integral with the supported window and
   supplies the actual floor cutoff for every `0 < theta < 4/7`.
4. [PRZZFamilyMomentOptimal](../lean/PRZZFamilyMomentOptimal.lean): constants
   precede height and the independent coefficient vectors in the finite
   seven-vector family. This is not the older fixed-label
   [PRZZMomentOptimal](../lean/PRZZMomentOptimal.lean), nor a theorem for
   arbitrary coefficient families without the stated conditions.
5. [PRZZAsymptotic](../lean/PRZZAsymptotic.lean),
   [TwoPieceMoment](../lean/TwoPieceMoment.lean) and the downstream Wu modules:
   the normalized moment, finite Cauchy jets, exact auxiliary function,
   boundary handling, local counting and all-height aggregation.
6. [FixedCertificate](../lean/FixedCertificate.lean) and
   [the numerical bundle](../paper/README.md): distinguish the kernel-checked
   rational gate from the independent Python interval computation.

Use the [dependency graph](dependency-graph.md) and [module table](modules.md)
to navigate the full 730-module headline import closure. The table's
comment-extraction column describes individual files, not a global list of
unresolved obligations. Narrow early-module comments must be read together
with their later suppliers.

## 3. Evidence and its limits

| Evidence | What was checked | What it does not establish |
| --- | --- | --- |
| [Current local clean record](../checks/clean-verification-2026-11-10-local.json) | All 778 local modules freshly compiled, zero reused local rows, source/dependency/artifact hashes and 4,405 axiom audits; four headline audits and their types | A proof of the explicit Weil/DI hypotheses or independent specification review |
| [Current AF clean record](../checks/clean-verification-2026-11-10-af.json) | All 101 required pinned AF modules freshly built in an isolated worktree; no old AF outputs | A Mathlib source rebuild: pinned Mathlib/package caches are reused; unrelated AF targets are outside the required closure |
| [Earlier interface-switch record](../checks/weil-di-proportion-verification.json) | The preceding run with one fresh local module and 777 verified cached outputs | The new clean build; this historical record is preserved unchanged |
| [Historical local clean record](../checks/clean-project-verification-2026-11-07.json) | Fresh outputs for the then-current 698 local modules | The later 80 additions or changed public interface |
| [Historical AF clean record](../checks/clean-af-verification-2026-11-07.json) | The pinned 101-module AF dependency closure, with fixed package caches | A fresh Mathlib source rebuild or a current local full rebuild |
| [Python certificate](../paper/certificate.json) and [finite verifier](../paper/verify.py) | Exact rational checks and four interval runs for the fixed functional | A formal proof of mpmath, the analytic reduction or the deep input specifications |
| [Paper correspondence](paper-correspondence.md) | Five theorem/lemma/proposition environments and two separately numbered hypothesis definitions, with named source contracts | Completed independent equivalence review; the narrow Python interval deliberately has no matching Lean theorem |
| [Revised manuscript/PDF](../checks/manuscript-render-verification.json) | Current conditional narrative, TeX compilation and every rendered page inspected | A new Lean build, proof of the two inputs, or completed human review |

Reproduction commands, cache rules and fresh-build options are in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md). Passing repository CI checks the
finite package and documentation tests, not a fresh Lean/AF build.

## 4. Questions for independent review

These are interpretation and specification checks, not assertions that the
formal connections have yet to be implemented.

- Do the exact Weil completion and DI specifications follow from the cited
  sources with the stated uniformity, coefficient class and parameter ranges?
- Does the intended original density match the Lean coefficients and shift
  orientation? The diagonal relation puts beta on `d` and alpha on `e`.
  Review the [v0.1.0 erratum](STATUS.md#v010-erratum-shift-placement-7-november-2026),
  both ordered cross terms and genuine dual Gamma factors. Full BCHB source
  checking remains unrecorded; finite witness symmetry is not a general
  mixed-profile identity with incorrectly placed shifts.
- Do the finite-family expansion, natural cutoff and order of quantifiers
  model the intended height-dependent witness? Inspect norm caps, retained
  supports and loss margins rather than reading `moment_bound` in isolation.
- Do the manuscript's counts, denominator and limiting convention match the
  actual AF statement? Complete the paper-to-Lean mapping, including boundary
  multiplicities and the fixed margin for all sufficiently large real heights.
- Are the normalizations of the actual moment, density gcd main term and
  finite functional correct? These objects have separate definitions and
  proved bridges. The raw main-term formula at `A+B=0` is not its regularized
  value; the actual negative-shift bidisc excludes that divisor.

## 5. Manuscript and historical material

[manuscript.tex](../paper/manuscript.tex) and
[manuscript.pdf](../paper/manuscript.pdf) were revised together on
10 November 2026. They give both deep-input formulas and quantifier
orders, the family-uniform moment, main-term orientation, finite gates
and actual AF count transfer. The PDF was rebuilt and inspected page by
page; [the render record](../checks/manuscript-render-verification.json)
fixes its source/output hashes and verification scope.
The DI Lemma 1 scan on p.310 was visually compared with the displayed
formula and filters; this is not a proof of the analytic input.
The current bibliography includes published Wu and PRZZ citations while
pinning the inspected arXiv versions for argument, theorem and page references.
Author/contact information, funding/interests and substantive AI use are
recorded in the manuscript and [publication checklist](PUBLICATION.md);
the remaining live JNT-guide/portal check is not claimed complete.

[STATUS.md](STATUS.md) separates current results from dated milestones.
[history.md](history.md), old compiler JSONs and `provenance.json` retain
their historical context. The historical `v0.1.0` tag is not rewritten.
No claim of human peer review, publication priority, global numerical
optimality or a new simple-zero result follows from this package.
