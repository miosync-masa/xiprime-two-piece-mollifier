# Release notes

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
