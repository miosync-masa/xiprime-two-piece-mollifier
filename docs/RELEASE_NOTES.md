# Release notes

## 2026 November 10 — Full clean verification and revised manuscript

The [local clean record](../checks/clean-verification-2026-11-10-local.json)
freshly compiles all 778 local modules, with zero reused local rows, and
checks 4,405 printed axiom audits. The linked
[AF clean record](../checks/clean-verification-2026-11-10-af.json) freshly
builds all 101 required pinned AF modules; no old AF outputs are used.
Only fixed Mathlib/package caches are reused. Compile stages took
190.253 seconds (AF) and 2,939.546 seconds (local, six worker slots).

README, generated reading aids and the revised manuscript/PDF now reference
these records. The 9 November one-fresh/777-reused record and earlier
historical records are preserved unchanged. Mathematical Lean sources,
explicit Weil/DI hypotheses, fixed witness and numerical results are unchanged;
the numerical certificate refreshes only the manuscript provenance hash.
This is not a Mathlib source rebuild, proof of the two deep inputs,
or completed independent human review.

## 2026 November 9 — Proved witness input and Weil/DI headline path

The former `PRZZ.przz41_case3_K2_witness` axiom is replaced by a theorem
with explicit `WeilIncomplete` and `DeshouillersIwaniecLemma1` hypotheses.
`PRZZWitnessBridge` identifies the public moment, its actual floor cutoff
and density-oriented main term with the height-uniform finite-family
estimate. `PRZZProvedInput` supplies that result to `PRZZAsymptotic` and
the original Wu counting chain. A definitions-only `PRZZAsymptoticCore`
prevents a circular dependency through the arithmetic regularity proofs.

All four `WuProportion` headline theorems now expose both hypotheses
explicitly. No local analytic axiom is declared; this does **not** prove
Weil or DI themselves. The numerical witness, multiplicity convention,
fixed strict margin and historical records are unchanged.
The [dependency-switch record](../checks/weil-di-proportion-verification.json)
distinguishes fresh compilation from verified source/dependency/artifact
caches; pinned AF/Mathlib outputs are reused. The older entries below
describe the interfaces at their recorded dates.

## 2026 November 7 — v0.1.0 shift-placement erratum

The `v0.1.0` tag is retained, not rewritten. See the dated
[STATUS erratum](STATUS.md#v010-erratum-shift-placement-7-november-2026)
for the density-oriented shift placement, removal of the former general
profile axiom from current source, and the proved finite witness symmetry.
The following October entry and its compiler records describe the former
interface. The numerical intervals are unchanged; only the certificate's
manuscript provenance hash is updated for the new note. At this checkpoint
the PDF was still the pre-note version, pending rebuild and visual inspection;
the 10 November revision above supersedes that rendering status.

## 2026 October 31 — Strict xi-prime proportion under the PRZZ input

Implementation milestone: [`b2b2b71`](https://github.com/miosync-masa/xiprime-two-piece-mollifier/commit/b2b2b71f06b996f721849f46e71879a320b736b7).

### Main theorem

[`WuProportion.strict_proportion`](../lean/WuProportion.lean) proves that there exists a fixed real number `b > 0.8845` such that, for every sufficiently large real height `X`,

```text
b * (Ncount 0 X : ℝ) ≤ (N0 0 X : ℝ).
```

`Ncount` and `N0` are AF's actual total and critical-line xi-prime zero counts, with multiplicity. The fixed margin gives an asymptotic lower proportion strictly greater than 88.45%, not merely a bound on a geometric subsequence. `ratio_eventually_gt` also proves the literal eventual quotient inequality.

This conclusion is conditional on the existing external PRZZ input. It does not assert a simple-zero bound or a formal proof of PRZZ itself.

### Complete axiom output

The following is the complete output of `#print axioms ratio_eventually_gt` inside the `XiPrime8845.WuProportion` namespace, reproduced verbatim from the [final compiler audit](../checks/wu-proportion-final-audit.json):

```text
'XiPrime8845.WuProportion.ratio_eventually_gt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PRZZ.przz41_case3_K2_profiles]
```

Beyond the three standard axioms, the only dependency is `PRZZ.przz41_case3_K2_profiles`. There is no `sorryAx` or additional analytic axiom. The theorem requires no supplied `LocalizedEstimate`, endpoint-tightness condition, counting gate, or simplicity assumption. The correspondence between the PRZZ interface and the source theorem remains part of the external-input audit.

### Completed connections

- Return the quotient logarithm to the original left line using reverse Fatou and the regular gamma factor.
- Supply safe contours, finite zero sets and local counting bounds with full analytic multiplicity.
- Include independently shortened windows in `(T, 2*T]`, normalize using AF's actual dyadic total count, and aggregate to all real terminal heights. No arbitrary-window Riemann–von Mangoldt formula is assumed.

### Verification scope

The [five-module verification record](../checks/wu-proportion-verification.json) contains fresh compilations of the five final modules and 24 new axiom audits: 17 standard-only and seven additionally using the existing PRZZ input. The 182 baseline source hashes were checked and all 187 registered axiom outputs replayed.

The [final audit](../checks/wu-proportion-final-audit.json) separately recompiles `WuProportion.lean`, checks all 187 source hashes, and replays the recorded outputs with the updated verification runner. These checks use previously verified dependency artifacts; they are not a full clean rebuild of all 187 modules or upstream AF.

At the implementation milestone, distribution hashes and local links passed, all four interval runs passed, and the freshly computed numerical certificate matched the saved JSON byte-for-byte. The manuscript and numerical bundle remain unchanged; the manuscript predates the completed Lean chain. See [reproduction instructions](REPRODUCIBILITY.md) for the full local Lean runner and numerical checks.
