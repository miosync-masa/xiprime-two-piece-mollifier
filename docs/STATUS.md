# Proof status

Updated: 7 November 2026. The fixed witness is unchanged.

## Original moment estimate (7 November 2026)

[`PRZZMomentOptimal.moment_bound`](../lean/PRZZMomentOptimal.lean) proves, under the explicit `WeilIncomplete` and `DeshouillersIwaniecLemma1` hypotheses,

$$\left|\mathrm{moment}-\mathrm{diagonalMain}\right|
\le C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

Here `moment` is the actual weighted mollifier/zeta-product time integral, not merely a literal proxy; `diagonalMain` is the stated coupled two-branch main term. The theorem fixes `K ≥ 4`, coefficient labels `js`, `tau > 0`, bounded-shift radius `S`, separation `r > 0`, a smooth monotone plateau seed `P` taking values in `[0,1]` (one below `1/2`, zero above `1`), and a smooth compact time cutoff `Phi` supported in `[1,2]`. Its constant precedes height, `N` and the shifts. The conclusion holds eventually in height for `1 ≤ N ≤ T^(4/7)`, `N+1 ≤ T`, `log T ≥ 1`, `‖A‖, ‖B‖ ≤ S` and `r ≤ ‖A+B‖`, with shifts `A/log T`, `B/log T`.

`PRZZBodyTailMass`, `PRZZBodyTailTime`, `PRZZTailRowIntegrable`, `PRZZNativeTailRectangle`, `PRZZBodyTailCollector` and `PRZZBodyTailOptimal` connect the actual `bodyCut` tail, transfer-band/subunit corrections, native residual masses and finite row/time integration. In particular the final moment theorem no longer assumes an unevaluated `actualTail` bound. The printed audit of `moment_bound` is standard-only (`propext`, `Classical.choice`, `Quot.sound`); Weil and DI are theorem parameters, not proved deep inputs.

**Boundary:** this separated logarithmic-shift moment theorem is not yet a substitution for the public `PRZZ.przz41_case3_K2_profiles` interface in `WuProportion`. The headline proportion theorem below still has its existing external axiom. The manuscript and numerical witness are unchanged. Earlier development entries describing unfinished connections are historical, not the current scope of `moment_bound`.

### Clean dependency verification

The [AF clean-build record](../checks/clean-af-verification-2026-11-07.json) checks the pinned, unmodified transitive source closure of all 16 AF imports: 101 AF modules rebuilt in a detached worktree with no initial AF output directory. Only fixed Mathlib/package caches were reused; inherited `LEAN_PATH` and old AF outputs were excluded. Lake's 3,788 job total includes cached package jobs and must not be read as 3,788 source rebuilds. Unrelated AF working-tree edits were preserved.

The [full local verification record](../checks/clean-project-verification-2026-11-07.json) covers all 698 local Lean sources and 3,971 printed axiom audits. Every source was freshly compiled in a new temporary local output directory against the freshly built AF closure (six worker slots). Successful compiler diagnostics were saved with source hashes. Clean verification exposed audit-registry defects: one non-topological module ordering, three misplaced coverage entries, and several exact axiom sets that unnecessarily expected `Classical.choice` or `Quot.sound`. After correcting the registry, the final verifier rechecked all 698 source hashes and those same fresh compiler outputs successfully. This is not replay of the historical baseline records. No mathematical Lean source was changed for these registry corrections, and `sorryAx` is absent. The sole explicit local axiom declaration remains the existing public PRZZ input; `moment_bound` itself prints only the standard three axioms.

## Current conclusion: strict proportion under the existing PRZZ input

[`WuProportion.strict_proportion`](../lean/WuProportion.lean) proves that there exists a fixed real `b > 0.8845` such that, for every sufficiently large real height `X`, `b * Ncount 0 X ≤ N0 0 X`. These are AF's actual xi-prime zero counts, with analytic multiplicity. `ratio_eventually_gt` gives the literal quotient inequality; the fixed-margin theorem also gives a strict asymptotic lower bound, not merely a pointwise strict inequality converging to 0.8845.

The final chain returns the quotient logarithm to the original left line via reverse Fatou and the regular H factor, supplies actual safe contours and their finite zero sets, proves the local count, includes retained zeros in `(T, 2*T]`, and uses AF's dyadic-to-cumulative theorem for all terminal heights. Thus an arbitrary-window Riemann--von Mangoldt adapter is not needed and is not claimed proved here. No `LocalizedEstimate`, `EndpointTight`, supplied counting gate, or simplicity premise enters the headline theorem.

Printed dependencies of the final theorem are exactly `propext`, `Classical.choice`, `Quot.sound`, and `PRZZ.przz41_case3_K2_profiles`. This closes the Lean derivation **relative to that existing external PRZZ input**, not a Lean proof of PRZZ itself or independent validation of its translation from the literature.

The [verification record](../checks/wu-proportion-verification.json) covers five fresh compilations, 182 unchanged baseline source hashes, and strict replay of all 187 registered axiom outputs. Its 24 new audits comprise 17 standard-only and seven additionally using the existing PRZZ input, with no `sorryAx`. It is not a full clean rebuild of all local modules or AF. The manuscript remains the older audit draft; no new simple-zero or priority claim is made.

## PRZZ decomposition milestone (2 November 2026)

[`PRZZActiveRows.literal_absorbed`](../lean/PRZZActiveRows.lean) proves a bound for the **original literal A-star**, with explicit Weil and DI hypotheses:

$$
|A^*|\le C T^{\delta+\gamma}\frac{\lambda}{d}
\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)
\int_{\mathbb R}(1+|t|)|\operatorname{mellin}\Phi(it)|\,dt.
$$

The connection is no longer a sum of unidentified row budgets:

- [`PRZZLiteralRows`](../lean/PRZZLiteralRows.lean) identifies the original literal integral with its complete dyadic row sum and windowed Mellin/Heath–Brown expansion.
- [`PRZZRowIntegralBudget`](../lean/PRZZRowIntegralBudget.lean) supplies the row integral bound and arithmetic branch/allocation bounds from Weil and DI. Original row masses remain inside the dyadic sum.
- [`PRZZNonemptyRowBudget`](../lean/PRZZNonemptyRowBudget.lean) obtains cutoff witnesses from nonzero source rows, combines their local frequency bounds with original outer masses, and absorbs the three-case losses. It compares scalar masses, not an asserted inclusion of differently scaled boxes.
- [`PRZZActiveRows`](../lean/PRZZActiveRows.lean) splits on nonvanishing of the **original signed row** before taking branch envelopes. Inactive original integrals vanish; active rows supply the witness needed by `nonempty_row_absorbed`. Labelled allocation multiplicities and both complete dyadic grids are then absorbed.

### Explicit conditions and remaining scope

`WeilIncomplete` and `DeshouillersIwaniecLemma1` are `Prop` parameters, not new axiom declarations. The result does not assume `CellBound`, a decomposition equality, or a Fubini premise. It retains the following source conditions (the linked Lean statement is authoritative):

- Positive integer sizes, `N+1 ≤ T`, `d ≤ T`, and `1 ≤ log T`.
- With `F = frequencyBound d D H`, `1 ≤ F ≤ T^rho` and `F ≤ lam * Q1 * Q2 / (d^2*T)`, with `1 ≤ lam`. These do not follow for arbitrary `D,H`.
- The two arithmetic cutoff supports lie in `[Q1,2*Q1]` and `[Q2,2*Q2]`; the outer cutoff lies in `[M/2,3*M]`. The required logarithmic scale bound holds for every retained dyadic index.
- The stated small-shift bounds and positive separation `r ≤ norm(A+B)` for `sourceW ((A+B)/log T)`.
- Nonnegative loss parameters with `(6+rho)*eta + (3+rho)*eps + b < delta`, and positive `gamma` for the final dyadic absorption.

Constants precede the variable sizes, heights and row data, but the cutoff functions `F0,F2,FM` are fixed before the constants. This statement must not be read as an already supplied uniform theorem for arbitrary height-varying `F2,FM` families. Instantiating all source-scale conditions and any required scaled-cutoff families remains distinct from this conditional bound.

The L1 files [`PRZZL1Finite`](../lean/PRZZL1Finite.lean), [`PRZZL1Truncation`](../lean/PRZZL1Truncation.lean) and [`PRZZL1Poisson`](../lean/PRZZL1Poisson.lean) provide preliminary finite/truncation interfaces and exact Poisson summation for smooth compact weights, including its Jacobian and residue phase. They do **not** supply the full AFE, its actual-kernel summability and truncation removal, or the actual Poisson-to-A-star reduction. Consequently `PRZZ.przz41_case3_K2_profiles` is still the external input of the headline proportion theorem.

### Verification of this milestone

The new modules were individually compiled against the existing pinned dependency caches. The final module's printed audit is:

```text
'XiPrime8845.PRZZActiveRows.active_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'XiPrime8845.PRZZActiveRows.inactive_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'XiPrime8845.PRZZActiveRows.active_budget_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound]
'XiPrime8845.PRZZActiveRows.literal_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These standard-only axiom lists do **not** discharge the explicit Weil/DI theorem hypotheses. The modules and expected audits are registered in `tools/verify_lean.py`; distribution hashes and the independent finite Python certificate are checked by `tools/verify_release.py`. Individual compilation and the Python release check are not a fresh whole-DAG or upstream AF rebuild. The earlier 187-module proportion audit above remains a historical verification record, not the size of the expanded module set.

## Historical ledger (28 October 2026)

The earlier development ledger (module-by-module descriptions and the "Verification levels" and "Lean scope" sections written before the counting chain was completed) has moved to [history.md](history.md). Statements there about then-missing connections are superseded by the current conclusion above; the moved text carries dated notes where the current status is recorded in the verification record.

## Analytic review

The exact review questions are in [the audit guide](../paper/README.md#questions-requiring-analytic-review). In particular, the transition from PRZZ's coefficient sum to the finite leading-pole functional and the Wu counting interface must be checked independently of the numerical margin.

An eventual theorem relative only to PRZZ must have no other custom analytic axiom, no `sorryAx`, and no trusted numerical JSON input in its axiom dependencies.
