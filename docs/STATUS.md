# Proof status

Updated: 9 November 2026. The fixed witness is unchanged.

## Current dependency switch: explicit Weil and DI (9 November 2026)

The public witness input is now a **proved theorem**, not an axiom.
[`PRZZWitnessBridge.witness_estimate`](../lean/PRZZWitnessBridge.lean)
constructs the auxiliary smooth plateau, identifies the all-real-time public
`twistedMoment` with the compact-window moment, supplies the actual natural
cutoff geometry, and derives the exact former witness estimate for every
`0 < theta < 4/7`. Its two analytic hypotheses are `WeilIncomplete` and
`DeshouillersIwaniecLemma1`; neither deep estimate is proved here.

[`PRZZ.przz41_case3_K2_witness`](../lean/PRZZProvedInput.lean)
(the declaration is in namespace `PRZZ`) replaces the former axiom with a
theorem taking both hypotheses explicitly. `DeepInputs` is only a
Prop-valued bundle used to thread those hypotheses through the intermediate
moment/counting chain; there is no default instance asserting them.
All four [`WuProportion`](../lean/WuProportion.lean) headline theorems
expose `hWeil` and `hDI` as explicit arguments. The conclusion still counts
zeros with multiplicity and retains a fixed margin above 0.8845.

The import path is now
`WuProportion -> ... -> PRZZAsymptotic -> PRZZProvedInput ->
PRZZWitnessBridge -> PRZZFamilyMomentOptimal ->` the evaluated Weil/DI
row and AFE suppliers. The old fixed-label `PRZZMomentOptimal` is not
silently substituted for a height-dependent coefficient family.
[`PRZZAsymptoticCore`](../lean/PRZZAsymptoticCore.lean) keeps elementary
geometry, definitions and Cauchy estimates separate from the analytic
transfer, avoiding a circular import through `ZetaPoleScaling` and
`ArithmeticRegularity`. The actual regularity proofs remain independent
of Weil/DI; their asymptotic application uses those hypotheses.

The current verification record is
[`weil-di-proportion-verification.json`](../checks/weil-di-proportion-verification.json).
It distinguishes fresh compilation from source/dependency/artifact-checked
local caches and reuses the pinned AF/Mathlib outputs. It is not a fresh
AF/Mathlib source rebuild. The numerical certificate and historical
verification JSONs are unchanged by this dependency switch.

The final stable-verifier run checks all **778** current local sources and
**4,405** printed axiom audits, including the **730**-module headline import
closure. It freshly recompiles `WuProportion`; the other 777 entries are
verified caches, including the changed sources compiled in the preceding
stages. This is not a fresh 778-module rebuild. All four headline audits
contain exactly `propext`, `Classical.choice`, `Quot.sound`, with no
`sorryAx` or PRZZ analytic axiom. The recorded `#check` output also confirms
both explicit deep-input arguments. Audit regression tests cover comments,
nested comments, apostrophes in Lean names and axiom-free declarations.

Dated development entries below describe their own stage. In particular,
statements that the public witness input remained external are superseded
by this section; they do not describe the current dependency path.

## v0.1.0 erratum: shift placement (7 November 2026)

The tag `v0.1.0` is preserved. Its general-profile input
`PRZZ.przz41_case3_K2_profiles` copied the printed denominator
`d^alpha * e^beta` in PRZZ Theorem 4.1 (arXiv:1802.10521v3, p.18).
For the density actually defined here, the diagonal condition is
`d*m = e*m'`, so the density-oriented denominator is instead
`d^beta * e^alpha`. The general, independently specified profile statement
must not be justified by a silent change of conventions.

The 7 November revision removed that general axiom and used the
**witness-only** `PRZZ.przz41_case3_K2_witness`, stated using
`PRZZ.densityGcdMainTerm` with the density-oriented shifts. Mixed and
polarized coefficient combinations are not covered by this input; their
internal bridge must use the correctly oriented kernel. The 9 November
switch above subsequently derived this witness estimate from Weil/DI.

`PRZZ.gcdMainTerm_swap` proves the exact finite-sum identity
`M(P,Q;A,B) = M(Q,P;B,A)` without an analytic axiom.
`PRZZ.witness_densityGcdMainTerm_eq` therefore identifies the two main terms
for the real `witness,witness` specialization, for every pair of shifts.
This equality precedes limits and differentiation: the symmetric sum of
both ordered cross terms, and the identical operators on both sides, leave
the certified numerical functional unchanged under this correction alone.
This is not a claim that every other analytic obligation is discharged.

The general shift placement is also printed in the inspected PRZZ source;
this note records the comparison, not an attribution of responsibility.
The full BCHB original has not yet been obtained and checked. Historical
compiler records are retained unchanged; the numerical certificate keeps
the same interval results, updating only its manuscript provenance hash.
Neither is a fresh analytic audit of the revised input. The preceding
witness-only scoped proportion audit is recorded separately in
[`witness-only-proportion-verification.json`](../checks/witness-only-proportion-verification.json).
All 171 local modules in the `WuProportion` closure were freshly compiled;
fixed AF/Mathlib outputs were reused. The four final theorem audits contain
exactly the standard three axioms and `PRZZ.przz41_case3_K2_witness`, with
no old general-profile axiom or `sorryAx`. This was a scoped check of
171 modules, not a full-project rebuild.

## Witness bridge progress (7 November 2026)

[`PRZZWitnessBasis`](../lean/PRZZWitnessBasis.lean) expands the actual public witness into seven height-dependent basis vectors: four Conrey monomials and three Feng monomials, with the original support and `(log N)^(-2)` normalization retained. A fixed rescaling puts the witness coordinates in the unit box. The entire radius-two complex coordinate box has the uniform coefficient bound `84`, proved before choosing height or coordinates.

[`PRZZWitnessMass.basis_arithmetic_factorization`](../lean/PRZZWitnessMass.lean) identifies those basis vectors with the fixed arithmetic labels `[]` and `[0,0]` times explicit height-dependent profile weights. `uniform_mass` supplies the actual diagonal contour-error mass for that whole box:

$$\mathrm{errorMass}\le C N^{1/4}T^{-1/8}(1+\log N)^2.$$

Here the constant precedes height, coordinates and bounded cutoff values. `normalized_cutoff_target` also proves the target budget divided by `T` tends to zero for the actual natural cutoff `floor(T^(4/7-10^(-6)))` and `tau=1/4000000`. The [scoped record](../checks/witness-basis-mass-verification.json) covers the 288-module import closure with cached dependencies distinguished from fresh compilation; all twelve new basis/mass theorem audits use only the standard three axioms.

**Still required:** a Weil/DI moment estimate uniform for the explicit profile-weight family (the existing `moment_bound` fixes an arithmetic label and does not provide this extension). The uniform smooth cutoff norms and basic Weil/DI block suppliers are supplied below, but their full row/AFE aggregation is separate. The componentwise Gamma main-kernel comparison is now evaluated in the 8 November milestone below. `witness_of_uniform_squares` is only an adapter with its square supplier explicit. At that stage the witness-only external input remained in the public theorem.

### Uniform smooth profile suppliers

[`PRZZProfileSmooth`](../lean/PRZZProfileSmooth.lean) expands `F(x)*(a-b*log x)^k` into the finite fixed family `F(x)*(log x)^j`. Positive compact support makes every member globally smooth, including at zero. This supplies all-order ordinary and dimensionless derivative bounds, and a DI coupled-block estimate with its constant selected before `a,b` in the unit parameter box and before the dilation scale.

[`PRZZProfileScale`](../lean/PRZZProfileScale.lean) identifies the seven actual profiles with this family, retaining the Feng denominator. For `log Y >= 1` and `1 <= Q <= Y`, `parameterA=log(Y/Q)/log Y` and `parameterB=1/log Y` lie in the unit box. With `G=cutoffRaw F Y Q i`, one constant sequence, fixed before `Y,Q,i,x`, gives

$$\|G^{(n)}(x)\|\le C_n Q^{-n},\qquad \|x^nG^{(n)}(x)\|\le D_n.$$

`weight_on_support` removes the sharp arithmetic indicator only on the original retained indices; no sharp indicator is differentiated. `log_length_eventually` supplies `log(length theta T)>=1` eventually for each fixed positive `theta`.

`source_bound_actual` feeds common cutoff constants into the actual Type I source derivative, retaining its complex-power and logarithmic costs. `variation_uniform` and `weil_bound_actual` genuinely apply WeilIncomplete to the real profile-weighted inverse-phase sum, with `H<=2Q` explicit. `coupled_bound_actual` genuinely applies DI to the actual seven profile cutoffs with a common constant before height and scale. The [scoped record](../checks/profile-uniform-verification.json) checks the 290-module import closure, distinguishing fresh compilation from verified caches; all 28 new theorem audits are standard-three-only. Weil and DI remain explicit theorem hypotheses.

These are **block suppliers**, not yet the full profile-family `moment_bound`. Threading both coefficient slots through the HB/allocation sums, masks, outer integrals and paired AFE residuals remains to be composed; no full moment uniformity or PRZZ-input discharge is claimed by these block estimates.

### Quantitative Mellin classes (8 November 2026)

[`PRZZMellinInterval`](../lean/PRZZMellinInterval.lean) extends the fixed `[1,2]` seminorm estimate to any positive support `[a,b]`, with `0<a<=b`. Ordinary jets retain the explicit factors `b,b^2,b^3`. Dimensionless bounds `norm(x^n*f^(n)(x))<=U_n` instead give

$$\int_{\mathbb R}(1+|t|)|\operatorname{mellin}f(it)|\,dt
\le 4\log(b/a)(U_0+U_1+3U_2+U_3)
\int_{\mathbb R}(1+t^2)^{-1}\,dt.$$

[`PRZZProfileMellin.Member`](../lean/PRZZProfileMellin.lean) retains smoothness, positive compact support of bounded logarithmic width, and the common dimensionless jet sequence. `profiles_member` supplies this class for all seven actual `cutoffRaw` profiles from `PRZZProfileScale.scaled_uniform`. Their support `[lo*Q,hi*Q]` has width `log(hi/lo)`, independent of `Q`. `profiles_mass` selects one weighted Mellin-mass bound before `Y,Q,i`.

`coupled_bound_class` replaces absorption of one fixed function's Mellin mass by the explicit common class cap; its DI constant precedes the arbitrary function. `coupled_bound_profiles` actually substitutes the seven profile family into that estimate. Smoothness is not inferred from totalized derivative bounds. These are quantitative DI block estimates, **not** the remaining full HB/row/AFE moment aggregation. The public witness axiom is not discharged.

The two scoped records, [Mellin interval](../checks/mellin-interval-verification.json) and [profile Mellin](../checks/profile-mellin-verification.json), distinguish freshly compiled targets from source/fingerprint-verified dependency caches and fixed AF/Mathlib outputs. They are not a full local rebuild. The raw `gcdMainTerm` docstring now explicitly warns that the formal `2*riemannZeta 1` at `A+B=0` is not its holomorphic extension; the witness domain still excludes that divisor. Older verification records precede this documentation-only source edit and are retained unchanged.

### Quantitative classes in actual HB sources (8 November 2026)

[`PRZZClassSources`](../lean/PRZZClassSources.lean) removes the fixed-function sup-norm choices from the actual `secondCoeff`, original small HB cells, both signed small sources, and the sharp DI branch supplier. The common caps precede `F0,F2,FM` and all height/branch data. `small_source_class` obtains those caps from `Member.jet_bound` at order zero, not an assumed source estimate. Independent left/right arithmetic labels remain explicit.

The actual sharp DI row needs discrete variation as well as Mellin mass. [`PRZZClassVariation`](../lean/PRZZClassVariation.lean) threads the common dimensionless order-zero and order-one bounds through the power/log weight, sharp interval masks, both endpoint jumps, retained sampling and full zero extension. `full_variation` includes empty rows and chooses its constant before the cutoff; `weil_row` applies the incomplete Weil hypothesis to that actual residual row. The original fixed plateau seed is not replaced by an arbitrary class member.

[`PRZZClassDI.source_bound`](../lean/PRZZClassDI.lean) inserts this evaluated full variation and the class-uniform right coefficient into the original signed HB source. Its five positive budget constants precede all three arbitrary class members. Original coprimality, sharp product cutoffs, actual dyadic modulus, and both frequency signs are retained. This is a genuine DI supplier, not an unevaluated variation or cell-bound premise. The [scoped record](../checks/class-hb-verification.json) records its local import closure and cached/fresh distinction; the new supplier audits use only standard axioms, with Weil/DI retained as hypotheses.

The next milestone below supplies the previously missing class-uniform free-factor Type I and finite row sums. The existing full `moment_bound` is not generalized by the above source estimates alone. In particular the 49-pair analytic supplier in `PRZZFamilyMoment` is still a premise, and the public witness input remains external.

### Free Type I, three cases and all mixed dyadic rows (8 November 2026)

[`PRZZClassFreeLength`](../lean/PRZZClassFreeLength.lean) inserts the common jets into logarithmic free rows, including retained sampling, full zero extension and the additional dyadic free-factor mask. Its actual incomplete-Weil estimate keeps the effective shortened endpoint, the inverse-residue gcd and both coprimality conditions. Constants precede the cutoff function and all height/window choices.

[`PRZZClassTypeI`](../lean/PRZZClassTypeI.lean) substitutes the class-uniform right coefficient, both signs of the actual `nu`, the complete frequency image and the complementary HB mass. It then performs the original modulus averaging and retained Type I scale comparison. The eight source/slice/cell theorems supply estimates rather than assuming them.

[`PRZZClassCases`](../lean/PRZZClassCases.lean) joins small, free Type I and balanced DI on the original retained-root classifier, eliminating empty original rows before selecting a retained sample. [`PRZZClassRows`](../lean/PRZZClassRows.lean) propagates these constants through the labelled HB branches, grids, supported `h` sum and allocation weights. `basis_bound` permits independent left/right arithmetic labels; `signedSum_bound` sums both complete dyadic grids. The same budget constants are selected before all three class members, so height-dependent members may be substituted without selecting new constants.

The [class-row record](../checks/class-rows-verification.json) records exact scoped compilation with dependency-cache provenance; the four new modules have nineteen standard-only theorem audits. These estimates retain the explicit finite `totalBudget`, rather than silently identifying it with the optimal moment error. **Still required:** original mass/time-space integration and optimal outer-budget absorption for these mixed profile rows, followed by the corresponding two-slot class-uniform AFE residual estimates and their substitution into the moment identity. The full profile-family moment theorem and public witness-input discharge are not claimed here.

### Mixed literal integrals and actual zeta-to-W error (8 November 2026)

[`PRZZMixedLiteral`](../lean/PRZZMixedLiteral.lean) identifies independent left/right coefficients with the original finite literal integrals and signed rows. The folding uses the coefficients only at finite arithmetic sample points; the auxiliary floor functions are never differentiated or asserted to belong to the smooth cutoff class.

[`PRZZClassLiteral.literal_absorbed`](../lean/PRZZClassLiteral.lean) integrates the class-uniform mixed row budget against the original source mass, removes empty original rows, and absorbs the allocations and both dyadic grids into `C*T^(delta+gamma)*lam*target/d`. Its constant precedes all three cutoff members. `literal_uniform_mass` also absorbs the time cutoff's weighted Mellin mass using its quantitative class cap. The original frequency, support, logarithmic-scale, separated-shift and loss-margin hypotheses remain explicit; this is not an unconditional estimate for arbitrary configurations.

[`PRZZMixedReplacement`](../lean/PRZZMixedReplacement.lean) evaluates the actual direct replacement error for independent coefficient slots using their common coefficient cap and the average of their two mean squares. The constant and eventual-height threshold precede both coefficient sequences, so they may depend on height. `family_target` supplies the actual radius-two witness basis family, without assuming 49 mixed-pair estimates.

[`PRZZMixedDefect.defect_target`](../lean/PRZZMixedDefect.lean) combines that estimate with the genuine dual Gamma multiplier and the evaluated Gaussian noncentral-residue bound through the existing exact AFE defect identity. For each positive `delta` it bounds the actual weighted integral of the zeta-product minus its two W-series by `C*P*T^delta*target`, uniformly in the two bounded coefficient slots and separated logarithmic shifts. This estimates the original zeta-to-W error integrand, not an unidentified residual budget.

The scoped records [class literal](../checks/class-literal-verification.json), [mixed replacement](../checks/mixed-replacement-verification.json) and [mixed defect](../checks/mixed-defect-verification.json) check closures of 328, 233 and 234 modules, respectively, with source/fingerprint-verified dependency reuse. The four new modules have seventeen standard-three-only theorem audits. These are not a full project or AF rebuild. **Still required:** uniformly supply and identify the mixed post-Poisson phase, freezing, boundary, tail and zero-frequency contributions in the original full moment decomposition. The full mixed `moment - diagonalMain` estimate, the 49-pair analytic supplier and the public witness-input discharge are not claimed by this milestone.

### Mixed exhaustive Poisson field in the original moment (8 November 2026)

[`PRZZMixedPoisson`](../lean/PRZZMixedPoisson.lean) applies four-rotation polarization to the **complete actual** `PRZZAllPoissonAFE.model`. It retains the two branches, central/tail/boundary/freeze/outside collective fields, `zeroPair` and `gammaDefect`. This is an explicit finite combination of the existing model evaluated at `c+d`, `c-d`, `c+i*d` and `c-i*d`, not an assertion that seven diagonal estimates control 49 mixed pairs. Collective integrals are preserved; no separate Fubini premise for an infinite Fourier component is introduced.

`defect_integrable` supplies time integrability before `defect_eq_lift` identifies the polarized error with the **actual independent-slot zeta-to-W defect integral**. `error_limit` connects the full model's cutoff limit to that exact integral, using the existing generic W-row and signed diagonal-correction limits. `scaled_error_limit` inserts the evaluated mixed defect bound, with the constant and height threshold before both bounded coefficient sequences. The Fourier cutoff `J(L)` may be arbitrary.

[`PRZZMixedMoment`](../lean/PRZZMixedMoment.lean) identifies the polarized Gamma diagonal main term with its actual mixed arithmetic double sum, then proves the finite-cutoff moment equation and convergence of the entire collective field. `decomposition_limit` gives

$$\mathrm{moment}(c,d)-\mathrm{arith}(K_{\rm diag};c,d)-\mathrm{collectivePoisson}_L(c,d)
\longrightarrow E,\qquad
|E|\le C P T^\delta\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

`family_decomposition_limit` actually inserts the height-dependent witness basis and its common cap `84` for all independent radius-two coordinate pairs, hence the 49 ordered basis pairs. This is a uniform bound for the **limiting AFE error**, not a uniform convergence rate in `L` across heights and coefficient families.

The [scoped record](../checks/mixed-poisson-moment-verification.json) covers the 342-module local closure with verified dependency-cache reuse and thirteen standard-only audits in the two new modules. It is not a full local or AF rebuild. **Remaining analytic boundary:** the collective Poisson term itself still needs its class-uniform mixed central-body, phase, tail, boundary, freezing and zero-frequency estimates and identification with the evaluated mixed literal suppliers. The present exact assembly and AFE limit do not establish a sharp bound for that collective term, the full mixed `moment - diagonalMain` estimate, or elimination of the public witness axiom.

### Actual mixed positive Poisson cell: evaluated sharp supplier (8 November 2026)

[`PRZZClassPoisson`](../lean/PRZZClassPoisson.lean) proves exact polarization of the original finite `PRZZAStar.literal` and identifies the polarized **actual** `PRZZCentralArithmeticJoin.positiveCell` with `PRZZMixedLiteral.literal`. The native shift-slot swap `beta,alpha` is retained. This equality involves finite coefficient sums and unchanged spatial integrals; no new integrability or model-identification premise is introduced.

`positive_absorbed` inserts the class-uniform Weil/DI estimate into this actual positive cell. `positive_target` chooses the positive loss parameters internally, giving, for every prescribed `tau>0`,

$$|\mathrm{positiveCell}(c,d)|\le C T^\tau\frac{\lambda}{d}
\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

The slots are the independent arithmetic labels `js,ks`, with arbitrary cutoff members of the stated quantitative classes. Constants precede all functions, scales, heights and the Fourier cutoff. `spatial_members` supplies one dimensionless jet sequence before every positive scale `M`; `partition_members` actually supplies it for the original telescoping spatial profile. `member_mono` permits combining this sequence with the arithmetic profile envelope.

**This milestone did not establish the optimal bound for the whole collective Poisson field.** Its narrow theorem retains local frequency inequalities, separated shifts, logarithmic spatial-scale conditions and supports `[Q1,2*Q1]`, `[Q2,2*Q2]`. The actual plateau-profile support can have ratio six. The fixed-profile frequency witness for that wider support already existed in `PRZZWideRowBudget` and `PRZZWideActiveRows`; the missing step here was its connection to the new mixed quantitative-class API, not a new proof of the wider frequency estimate. The next milestone makes that connection and sums the positive body cells. Negative modes, transfer bands, tails, freezing/boundary corrections and zero-frequency terms still require their mixed class-uniform aggregation. The public witness axiom remains external.

The [class-Poisson scoped record](../checks/class-poisson-verification.json) checks the 448-module local closure and eight standard-only target theorem audits, distinguishing fresh compilations from source/fingerprint-verified local dependency caches and fixed AF/Mathlib outputs. It is not a full project rebuild.

### Width-six mixed cells, outer sums and genuine dual time class (8 November 2026)

[`PRZZClassWideLiteral`](../lean/PRZZClassWideLiteral.lean) threads the mixed class-uniform row supplier through the **existing** `PRZZWideActiveRows.active_budget_absorbed`, with the actual arithmetic supports `[Q/2,3*Q]`. The fixed `16*c` inflation from `PRZZWideRowBudget.cutoff_frequency` stays in the constant. The narrow API is preserved unchanged.

[`PRZZClassWidePoisson`](../lean/PRZZClassWidePoisson.lean) supplies the same estimate for actual mixed positive Poisson cells. `window_target` substitutes the original `deltaCutoff`, the rounded arithmetic-window Fourier cutoff and their evaluated frequency/height envelopes. Empty strict index sets vanish. `body_target` also handles `Hraw<=1`, including equality, using the original `bodyCut=0` branch: its positive modes are empty, while the zero mode and subunit correction are not declared negligible. The displayed local height cost is exactly `tau+eD+eH`.

[`PRZZClassPositiveGrid`](../lean/PRZZClassPositiveGrid.lean) sums those actual cells over `d,Q,V,M`, for independent arithmetic labels, arbitrary height-varying cutoff families in the common class, and outer complex weights with an explicit unit norm cap. The existing harmonic/dyadic collector evaluates the outer mass; no new mass-bound premise is introduced. Spatial subsets lie in the stated polynomial `M` window and the constant is uniform in the exhaustion `L`. `grid_optimized` selects positive `eD<eH` internally and absorbs the cutoff and outer logarithmic costs into any prescribed `T^tau`.

[`PRZZClassDualProfile`](../lean/PRZZClassDualProfile.lean) converts the genuine Gamma-multiplied dual cutoff's existing all-order uniform jets into a quantitative Mellin class. `common_members` and `common_mass` supply a single class and weighted Mellin cap for the original and dual time profiles before height and bounded logarithmic shifts. [`PRZZClassPairedGrid.paired_grid_optimized`](../lean/PRZZClassPairedGrid.lean) actually substitutes this supplier into both positive outer sums with one common pair `eD,eH`, retaining the reflected shifts `(-B,-A)` and the real Gamma multiplier. Their sum is bounded by

$$C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)$$

for every positive `tau`, subject to the stated arithmetic/spatial class, support, polynomial-window, coefficient-weight and separated-shift conditions. This is an evaluated mixed **positive-body pair**, not the entire retained Poisson field. Negative modes, source/window transfer bands, Fourier tails, large-spatial configurations, boundary/freezing corrections and zero-frequency discrepancies still need their mixed class-uniform connection to the original exhaustive moment decomposition. The witness-only public analytic input has not been discharged.

The scoped records [positive grid](../checks/class-positive-grid-verification.json) and [paired grid](../checks/class-paired-grid-verification.json) cover 485 and 487 local modules respectively, retaining exact source/fingerprint and fresh/cache provenance. The five new modules have twelve standard-only theorem audits. These checks are not a whole-project or AF rebuild.

### Mixed negative body and common signed AFE grids (8 November 2026)

The five `PRZZClassSpatial*` modules supply class-uniform small, DI and free Type I sources, the three cases and mixed row sums with only a global norm cap on the spatial cutoff. The arithmetic estimates do not require that cutoff to have positive support. This permits the reflected spatial weight in the negative row without asserting that reflection preserves the positive-support Mellin class. The physical spatial cutoff in the subsequent integral still has the original smoothness and positive support.

[`PRZZClassNegativeLiteral`](../lean/PRZZClassNegativeLiteral.lean) inserts these suppliers into the actual negative row integral, excluding inactive original rows before applying frequency witnesses. [`PRZZClassNegativePoisson`](../lean/PRZZClassNegativePoisson.lean) identifies the mixed four-rotation lift of the original `negativeCell` with that literal integral, without conjugating or exchanging the independent coefficient slots. Its `window_target` and `body_target` substitute the rounded source cutoff and handle `Hraw<=1`: only the nonzero modes are empty there; no zero-frequency correction is dropped.

[`PRZZClassNegativeGrid`](../lean/PRZZClassNegativeGrid.lean) evaluates the negative outer `d,Q,V,M` sum. [`PRZZClassSignedGrid`](../lean/PRZZClassSignedGrid.lean) combines both nonzero frequency signs at one cutoff. [`PRZZClassPairedSignedGrid.paired_grid_optimized`](../lean/PRZZClassPairedSignedGrid.lean) then supplies the genuine Gamma-multiplied dual time profile and reflected shifts in the second AFE branch. One common pair `eD,eH` and one constant give the paired signed-body bound `C*T^tau*target N T` for every `tau>0`, uniformly in the exhaustion `L`. Common quantitative cutoff classes, the polynomial spatial window, support conditions, unit outer-weight cap and shift separation remain explicit.

**Remaining scope:** this evaluates both signs of the mixed central body, not the full exhaustive Poisson field. Mixed transfer-band/subunit corrections, Fourier tails, large-spatial configurations, boundary/freezing terms and zero-frequency discrepancies still require their suppliers and exact insertion into the original moment equality. The mixed zero-frequency discrepancy is evaluated in the next milestone; the other residual components remain open. The public witness-only axiom remains external.

The [paired signed-grid record](../checks/class-paired-signed-grid-verification.json) covers a 500-module local closure, with 14 fresh compilations and source/fingerprint-verified dependency caches. The ten new modules have 29 standard-only theorem audits, checked against their saved fresh compiler outputs; Weil and DI remain explicit hypotheses. This is not a full local or AF rebuild.

### Mixed original zero-frequency correction (9 November 2026)

[`PRZZClassZeroBoundary`](../lean/PRZZClassZeroBoundary.lean) inserts a common coefficient cap into the original primitive arithmetic mass, retaining its three harmonic sums. Both lower/upper spatial boundary sums have arbitrary power decay; the dual supplier uses the genuine height-dependent Gamma profile, not a fixed-profile constant applied to that family.

[`PRZZClassZeroTail`](../lean/PRZZClassZeroTail.lean) and [`PRZZClassZeroPrimalGap`](../lean/PRZZClassZeroPrimalGap.lean) evaluate the omitted signed-gap tails with the native strict masks, both complete arithmetic partitions and all retained spatial scales. Their constants precede the coefficient sequence, height and exhaustion. The spatial/cardinality costs are absorbed by choosing the IBP order before height, not by discarding the growing configurations.

[`PRZZClassZeroCorrection.actual_power`](../lean/PRZZClassZeroCorrection.lean) substitutes those actual suppliers into `mismatch_boundary_gaps` and bounds the original `PRZZCentralMainAssembly.zeroMismatch` by `C*T^(-rate)` for every nonnegative rate, eventually uniformly in all coefficients with the common cap and separated bounded logarithmic shifts. `mixed_power` then polarizes that evaluated result for two independent coefficient slots. `family_power` actually substitutes the seven height-dependent witness basis vectors and their radius-two coordinate boxes, using the proved common cap 84. Thus all 49 ordered basis pairs are included. The length window is `1 <= N <= T^(4/7)`; no general-profile PRZZ axiom is invoked.

`arithmetic_split` gives the exact polarized decomposition of the original `arithmeticResidual` into this zero discrepancy and its actual positive/negative/tail collectors. `arithmetic_bound` inserts the evaluated zero correction there, uniformly also in the Fourier cutoff `J`, leaving only those concrete nonzero collectors on the right.

The [zero-correction scoped record](../checks/class-zero-correction-verification.json) covers 453 local modules: its final run freshly compiles the target and reuses source/dependency/artifact-verified caches, including the newly compiled suppliers. All sixteen audits in the four new modules were checked against their saved compiler outputs and use only standard axioms. This closes the **mixed zero-frequency discrepancy**, including its spatial boundaries and omitted gaps, not the distinct nonzero Fourier tail, transfer/subunit, freezing, discarded or large-spatial remainder estimates. Their common mixed estimate and final insertion into the full moment bound remain open; the public witness-only analytic input is unchanged.

### Common-cap nonzero tails and active freezing rows (9 November 2026)

[`PRZZCappedPrefactor`](../lean/PRZZCappedPrefactor.lean) bounds the literal normalized prefactor for arbitrary coefficients under a common cap. The original `d*u,d*v` values, conjugation, scaled complex powers and inverse-residue phase remain present. Dyadic denominators pay the pair cardinality; the arithmetic cap is not replaced by a count of configurations. The same supplier evaluates the signed-gap coefficient mass used by freezing.

[`PRZZCappedTailMass`](../lean/PRZZCappedTailMass.lean) includes the actual dual Gamma quotient and dilation factor, and gives arbitrary power decay for the absolute pair tail with `1/d` retained. [`PRZZCappedWindowMass`](../lean/PRZZCappedWindowMass.lean) and [`PRZZCappedWindowTime`](../lean/PRZZCappedWindowTime.lean) sum every retained `d,j,l,Delta,M` configuration on the stated polynomial spatial window, uniformly in exhaustion `L`; the `Q>2T` region vanishes by the real cutoff support. [`PRZZCappedWindowField.mixed_time`](../lean/PRZZCappedWindowField.lean) evaluates the time integral of the norm of the actual complex tail field polarized in two independent coefficient slots, with bound `C*T^(-power)*integral(norm(phi))`. The constant precedes both slots and height; the true native gap filters and source-cutoff tail remain explicit. This is not yet the identity with every different common/body cutoff in the exhaustive model.

[`PRZZCappedFreezeMoment`](../lean/PRZZCappedFreezeMoment.lean) evaluates the additional `v^(1+eta)*(3M)^eta` arithmetic moment. It selects the first nonempty spatial scale, sums the full gcd/dyadic family, and absorbs the resulting `N^5/T^2` and logarithmic factors into the PRZZ target with `6*eps+2*eta<delta`. [`PRZZCappedFreezeBudget`](../lean/PRZZCappedFreezeBudget.lean) inserts that computed moment into the actual freezing row integrals. `mixed_scaled_bound` evaluates their full active complex sum under a common coefficient cap; `active_freeze_identity` identifies each row integral with its actual native `.freeze` component. `paired_mixed_bound` supplies continuity and a uniform norm cap for the genuine Gamma-weighted time profile and adds the reflected dual branch to the same `C*P*T^delta*target N T` budget. The physical cutoff profiles are fixed before the constants, not silently asserted to range over a height-dependent smooth class.

The scoped [window-field](../checks/capped-window-field-verification.json) and [freezing-budget](../checks/capped-freeze-budget-verification.json) records cover 458 and 456 local modules, with five and two fresh compilations respectively and source/dependency/artifact-verified caches. All 24 audits in the seven new modules were checked against the saved compiler outputs and use only standard axioms. These are scoped checks, not a whole-project rebuild. Remaining work includes the exact common/body-cutoff and transfer-band/subunit identifications, the strict same-mask freezing reconstruction and its outer arithmetic partition, discarded/large-spatial corrections, and final substitution into the complete mixed moment equality. The witness-only public input remains external.

### Strict source masks and common-cutoff transfer (9 November 2026)

[`PRZZCappedNativeTail`](../lean/PRZZCappedNativeTail.lean) supplies the lossless signed-gap and dyadic-pair reindex for arbitrary coefficients, including the out-of-range support-zero case. [`PRZZCappedStrictTail`](../lean/PRZZCappedStrictTail.lean) identifies the actual local tail of the reconstructed strict source mask and inserts the evaluated native mass. No endpoint of the strict mask is changed.

[`PRZZCappedBandOuter`](../lean/PRZZCappedBandOuter.lean) evaluates the actual common-minus-local central Fourier band, with original complex powers, native gap membership and Gamma multiplier. Its `central_row_difference` is an exact row equality; `native_mass` retains the signed-gap bijection and pair partitions without duplicated configurations. The full outer band mass and time integral have arbitrary power decay for `J>=commonCutoff`. [`PRZZCappedSameMask`](../lean/PRZZCappedSameMask.lean) supplies that bound on the very same strict mask used by reconstruction.

[`PRZZCappedTailBand`](../lean/PRZZCappedTailBand.lean) inserts both evaluated suppliers into the original `PRZZReconstructedAFE.tailBand`, retaining `4*N*T^4<=L`, the original `log_2 N+2` allocation grid and `eps<eH`. `mixed_tailBand_time` supplies the genuine paired Gamma branches under a common coefficient cap, and `mixed_tailBand_target` absorbs this actual component into `C*T^delta*target N T` for every nonnegative `delta`.

`mixed_remainder_split` and `original_moment_split` return the exact polarized decomposition to the original mixed moment and literal model. The RHS retains the actual AFE model defect, evaluated tailBand, strict freezing, discarded and collective large-spatial terms. **This equality does not estimate the last three terms.** The existing capped freezing budget must still be matched to that strict reconstruction and its outer arithmetic partition; mixed discarded/large-spatial suppliers and the final complete moment bound remain open. The public witness-only input is unchanged.

The [strict tail-band scoped record](../checks/capped-tail-band-verification.json) covers 462 local modules, with five fresh compilations and source/dependency/artifact-verified caches. All 26 audits in the five new modules were checked against the saved compiler outputs and use only standard axioms; no full local or AF rebuild is claimed. The following milestone supplies the three residual estimates left open at this stage.

### Common-cap strict freezing, discarded and large-spatial residuals (9 November 2026)

[`PRZZCappedStrictFreeze`](../lean/PRZZCappedStrictFreeze.lean) matches the original strict-small/source mask to the evaluated capped freezing mass, before taking norms. Zero cutoff values, signed native gaps and the unique dyadic pair partition are retained. `partition_bound` pays both complete outer arithmetic grids using explicit slack above `6*eps+2*eta`.

[`PRZZCappedFreezeCollector`](../lean/PRZZCappedFreezeCollector.lean) proves the finite time-integral exchange for the actual reconstructed `freezing` field. Its paired mixed bound contains the genuine dual Gamma multiplier and reflected shifts, not a separately postulated row error.

[`PRZZCappedDiscardedIBP`](../lean/PRZZCappedDiscardedIBP.lean), [`PRZZCappedDiscarded`](../lean/PRZZCappedDiscarded.lean) and [`PRZZCappedDiscardedFamily`](../lean/PRZZCappedDiscardedFamily.lean) generalize the original selected IBP family to arbitrary coefficient sequences under a common cap. The actual outer coefficient mass is bounded by `N^2*Hcap^2`; both valued arithmetic cutoffs, the strict spatial selector and genuine all-order Gamma jets are included before choosing the IBP order. Both branches, every original finite product cutoff and the full arithmetic partition are then returned to the original `discarded` field. Its paired mixed integral has arbitrary prescribed power decay, uniformly in `L,J`.

[`PRZZCappedLarge`](../lean/PRZZCappedLarge.lean) bounds the collective large-spatial field without counting its spatial pieces separately. The actual paired mixed `largeField` at threshold `T^4` is bounded by `C*T^(-2)` times the time-cutoff L1 mass, uniformly in both sharp cutoffs.

[`PRZZCappedRemainder.remainderPair_bound`](../lean/PRZZCappedRemainder.lean) combines these evaluated suppliers with the earlier strict tailBand bound. One constant precedes both coefficient slots, height and the exhaustion parameters, and bounds the actual mixed `remainderPair` by `C*T^delta*target N T`. It retains the common coefficient cap, bounded separated logarithmic shifts, `N<=T^(4/7)`, `4*N*T^4<=L`, `J>=commonCutoff`, `0<eps<1`, `eps<eH` and `6*eps+2*eta<delta` (with `0<eta<=1`). `original_moment_residual` is the exact return to the original mixed moment/literal-model equation: it does not set the actual AFE model defect to zero.

**Boundary:** this closes the displayed mixed reconstructed residual budget, not the complete class-uniform Weil/DI moment theorem or the public witness input. The actual AFE replacement/model limit and signed central/main-term estimates must still be composed with it. The scoped [verification record](../checks/capped-remainder-verification.json) checks 471 local modules. Its final run freshly compiles the target and verifies dependency source/fingerprint/artifact caches; all seven new modules were compiled in the preceding scoped stage, and all 41 saved compiler audits were individually checked against the exact standard-three registry. This is not a full local or AF rebuild.

### Mixed AFE replacement, exhaustion and density main term (9 November 2026)

[`PRZZCappedMomentBridge`](../lean/PRZZCappedMomentBridge.lean) combines the evaluated actual mixed AFE defect limit with `PRZZCappedRemainder.remainderPair_bound`. `eventually_total_bound` allows a Fourier sequence `J(L)` eventually above the common cutoff; only the exhaustion threshold, not the bound constant, may depend on the coefficients and height. `limit_total_bound` proves the actual spatial literal-model limit, and `full_total_bound` then removes the Fourier cutoff using the existing proved convergence. Its conclusion bounds the original mixed moment minus the explicit complete `PRZZLiteralFourierLimit.fullModel` by `C*T^delta*target N T`. No convergence is inferred from boundedness, and no AFE-error estimate remains a premise.

[`PRZZCappedMainTerm.mainterm_absorbed`](../lean/PRZZCappedMainTerm.lean) evaluates the actual Gamma-diagonal minus density-oriented gcd arithmetic pairing under a common coefficient cap, for every positive loss exponent. `density_reduction` inserts it into the cutoff-removed actual moment equation:

$$\left|\mathrm{moment}-\mathrm{arithmeticPairing}(K_{\rm density})-\mathrm{centralCorrection}\right|
\le C T^\delta\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

Here `centralCorrection` is exactly the complete literal model minus its Gamma diagonal. `centralCorrection_eq` writes it as the original arithmetic residual plus the integrated `gammaDefect`, for every finite central cutoff `J`. `zero_removed_reduction` also inserts the evaluated mixed `zeroMismatch` bound, leaving only the actual nonzero central collectors (including their explicit Fourier tail) and the separate integrated `gammaDefect`. This latter term is not confused with the Gamma-to-density main-kernel error. `family_density_reduction` substitutes the actual height-dependent seven-vector family and radius-two independent coefficient boxes using the common cap `84`, hence covers every ordered basis pair without freezing the basis.

**Boundary:** the actual nonzero collectors have not yet been identified with the class-uniform, windowed Weil/DI grids in this theorem, and the separate common-cap `gammaDefect` absorption remains to be supplied. Thus this is an evaluated AFE/main-term reduction, not the completed full class-uniform moment estimate or a discharge of the witness-only public input. The [scoped record](../checks/capped-main-term-verification.json) covers 474 local modules, with both new modules freshly compiled and dependencies reused only after source/fingerprint/artifact checks. All ten new compiler audits were individually checked against the exact standard-three registry; no full local or AF rebuild is claimed.

### Exact nonzero-central to signed-grid identification (9 November 2026)

[`PRZZCentralGridIdentity`](../lean/PRZZCentralGridIdentity.lean) identifies the original mixed nonzero collector, rather than assuming a decomposition equality. `common_eq_original` commutes the four polarization terms with the original finite collector. `body_eq_grid` identifies the row-dependent central body with the actual `PRZZClassSignedGrid.grid` already estimated by Weil/DI. `nonzero_eq_grid` puts both identities together for independent arithmetic labels `js,ks`:

$$\mathrm{nonzeroResidual}_{\rm mixed}
=\mathrm{grid}(A,B)+\mathrm{grid}_{\rm dual}(-B,-A)
+\mathrm{transfer}_{\rm paired}+\mathrm{tail}_{\rm paired}.$$

Every term uses the same strict spatial mask `2^s<T^4`, the full arithmetic dyadic grid and `d` sum, and the actual `deltaCutoff`. `transfer` is explicitly the sum of common-`J` minus row-`bodyCut` signed cells; it is not set to zero, including in the subunit case. The dual branch retains the actual Gamma profile and the same coefficient order. `nonzero_eq_body_transfer_tail` also supplies the exact decomposition for arbitrary mixed coefficient sequences, before specializing the body to fixed arithmetic labels.

**Boundary:** this is an exact identification, not a new bound for transfer or tail. Absorbing the actual seven height-dependent scalar profile weights into the two arithmetic cutoff slots, verifying the resulting grid-class hypotheses, and evaluating the displayed corrections with those same masks still remain before the full witness moment bound. The separate integrated `gammaDefect` also remains distinct. The [scoped verification record](../checks/central-grid-identity-verification.json) checks a 522-module local closure, freshly compiling the new target and verifying reused dependency sources, fingerprints and artifacts. All seven new audits contain exactly the standard three axioms. The eleven audit/registry regressions also pass; no full project or AF rebuild is claimed.

### Height-dependent basis profiles in the actual grid (9 November 2026)

[`PRZZBasisGridCutoff`](../lean/PRZZBasisGridCutoff.lean) absorbs all 49 ordered basis pairs into smooth arithmetic cutoff slots at the actual finite samples. The Mobius/Feng arithmetic labels stay fixed; no division by an arithmetic coefficient is used. The right scalar profile is conjugated and then identified with itself by `raw_star`. `central_absorb` holds for every row-cutoff map and `body_basis_grid` identifies the original basis body with the previously evaluated signed grid. `transfer_absorb` preserves the actual common-to-body transfer, including its sign and strict masks.

`parameters_doubled` covers the final arithmetic window `Q<=2Y`, not just `Q<=Y`. `normalized_members` supplies one dimensionless jet sequence before `Y,Q`, the basis label and every dilation. This supplies both the normalized left profile and the physically scaled right profile required by the grid, with support `[1/2,3]` and logarithmic width `log 6`.

[`PRZZBasisGridBound.body_optimized`](../lean/PRZZBasisGridBound.lean) inserts these actual profiles into Weil/DI and proves

$$|\mathrm{basisBody}_{i,j}|\le C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)$$

for every positive `tau`, with `eps=tau/16`, `eH=tau/8`. Its constant precedes height, the logarithmic profile length, both basis labels, the arithmetic and spatial cutoffs, and every time profile in the displayed Mellin class. The hypotheses retain `1<=log Y`, `N<=Y`, `N+1<=T`, `T>=72`, bounded separated logarithmic shifts and the spatial-grid envelope. This is an actual original signed body bound, not a premise about 49 unknown mixed errors.

**Remaining correction:** `tails_eventually` gives one common exhaustion threshold for all 49 common-`J` tails at each fixed height. This is not a height-uniform estimate at `bodyCut`. `transfer_tail_eq_bodyTail` shows that the retained transfer plus that tail is exactly the row-dependent `bodyTail`; `nonzero_eq_body_bodyTail` returns this identity to both original AFE branches with their actual Gamma dual profile. Thus taking `J` large does not dispose of the transfer. A height-uniform arithmetic/time bound for this merged body tail (including the subunit correction and both branches), and the separate `gammaDefect`, still need to be connected before claiming the full moment bound or discharging the public witness input.

The [scoped verification record](../checks/basis-grid-bound-verification.json) covers 524 local modules. Both new modules were freshly compiled during this stage; the final run freshly compiles the bound target and reuses dependency artifacts only after source/fingerprint/artifact checks. All 18 saved new compiler audits were individually checked against the exact standard-three registry, and all eleven audit/registry regression tests pass. No full local or AF rebuild is claimed.

### Height-uniform bound for the actual merged body tail (9 November 2026)

[`PRZZCappedWindowBand`](../lean/PRZZCappedWindowBand.lean) and [`PRZZCappedSubunitMass`](../lean/PRZZCappedSubunitMass.lean) supply the source-to-window transfer and subunit nonzero correction for arbitrary coefficient sequences under one common cap. The actual window cutoff, native gap domain and both Gamma branches are retained; neither supplier replaces the window by the larger common cutoff. `PRZZCappedBodyMass.mass_bound` combines these with the already evaluated common-cap source tail after an exact row-transport identity. Its `uniform` bounds the full absolute native mass, uniformly before the coefficient sequence, native exhaustion and height.

[`PRZZCappedBodyTail.mixed_bound`](../lean/PRZZCappedBodyTail.lean) returns this evaluated mass to the actual time-integrated body tail:

$$\left|\mathrm{bodyTail}_{c,e}(A,B)+
\mathrm{bodyTail}_{c,e,\rm dual}(-B,-A)\right|
\le C T^\delta\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

One constant precedes both coefficient slots, height and `N`; the paired tail uses the original strict spatial grid at `spatialLength T` and the original row-dependent `bodyCut`. The hypotheses retain a fixed smooth plateau seed `P`, a continuous compact time profile `Phi` supported in `[1,2]`, a nonnegative common coefficient cap, bounded separated logarithmic shifts, `1<=N<=T`, `0<=eps<1` and `eps<eH`. The native exhaustion is chosen after height; its rejected rectangle is proved eventually zero rather than assumed small. Time integration is exchanged with the actual finite sums only after the corresponding integrability proofs. No `bodyTail` bound or native-mass estimate remains a premise.

`family_bound` substitutes both actual height-dependent seven-vector families with the evaluated cap `84`, for independent radius-two coordinate boxes. `nonzero_reduction` inserts the same bound into the original mixed `nonzeroResidual` minus its paired body collector, uniformly in every original common Fourier cutoff `J`. Thus the merged body-tail obligation left in the preceding milestone is now evaluated, not disposed of by fixed-height Fourier convergence.

**Remaining scope:** the paired class-uniform central-body bound, the finite mixed-family assembly and the separate integrated `gammaDefect` must still be joined to the AFE/main-term reduction. This tail result does not by itself discharge the witness-only public input. The [scoped verification record](../checks/capped-body-tail-verification.json) checks a 549-module local closure, with all four new modules freshly compiled. All 31 saved new compiler audits were individually checked against the exact standard-three registry; all eleven audit/registry regression tests pass. Reused dependencies require source/fingerprint/artifact checks; no whole-project or AF rebuild is claimed.

### Full height-dependent finite-family moment bound (9 November 2026)

[`PRZZFamilyMomentOptimal.moment_bound`](../lean/PRZZFamilyMomentOptimal.lean) now combines the actual AFE/main-term reduction with both central-body branches, the evaluated body tail and the separate integrated `gammaDefect`. Under the explicit Weil/DI hypotheses, for **every** `tau>0`, it proves

$$\left|\mathrm{moment}(a_z,a_w)-\mathrm{arithmeticPairing}(K_{\rm density};a_z,a_w)\right|
\le C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr),\qquad
a_z(n)=\sum_{i=0}^6 z_i\,\mathrm{basis}(\theta,T,i,n).$$

The basis depends on the actual height, both coordinate vectors are independent and satisfy `norm(z_i),norm(w_i)<=2`, and the constant precedes height, `theta,N`, both vectors and all shifts. The theorem fixes the smooth monotone plateau seed `P`, the smooth compact time weight `Phi` supported in `[1,2]`, `K>=4`, the final positive loss and the bounded separated shift envelope. Its displayed variable-size conditions are `theta>0`, `1<=N`, `N+1<=T`, `N<=T^(4/7)`, `1<=log(length theta T)` and `N<=length theta T`. It does not assert a uniform theorem for arbitrary bounded arithmetic sequences outside this seven-dimensional family.

[`PRZZBasisPairedBody`](../lean/PRZZBasisPairedBody.lean) supplies both signed central-body AFE branches using one genuine Gamma-weighted time-profile class, with the coefficient order unchanged. [`PRZZCappedGammaDefect`](../lean/PRZZCappedGammaDefect.lean) supplies the actual correction arithmetic mass for arbitrary common-cap coefficients, retains the Gamma `1/T` gain and absorbs its time integral and logarithmic singularity losses into `C*target N T`. This integrated defect is kept distinct from the Gamma-to-density main-kernel comparison. Neither term is an estimate premise in the final moment theorem.

`basis_bound` proves all 49 ordered mixed errors after composing the complete AFE residual; `family_bound` uses the exact finite arithmetic/time pairing identities and the radius-two factor `49*4`, not seven diagonal-only estimates. `moment_bound` explicitly chooses all internal losses from `min(tau,1)`, so no positive lower bound on the available final loss is imposed by the decomposition.

`witness_bound` specializes the real numerical witness. `witness_uniform_normalized` then substitutes the actual natural cutoff at `theta=4/7-10^-6` and `tau=1/4000000`, proves the required cutoff geometry eventually, and obtains an error divided by `T` tending uniformly to zero over the displayed bounded separated shifts.

**Public-interface boundary:** these are actual compact-window moment estimates and a uniform normalized witness estimate, not an assertion that the `WuProportion` import graph has already been rewired. Identifying the all-real-time public `twistedMoment` and its exact interface quantifiers with this theorem, supplying the chosen plateau seed, and routing the resulting Weil/DI-conditional input through the headline chain remain explicit follow-up work. The witness-only external axiom in the public interface is unchanged. The [scoped verification record](../checks/family-moment-optimal-verification.json) checks 569 local modules. All three new modules were freshly compiled during this stage; the final run freshly compiles the target and checks reused dependency sources, fingerprints and artifacts. All fourteen saved new compiler audits were individually checked against the exact standard-three registry. The eleven audit/registry regression tests pass; no whole-project or AF rebuild is claimed.

### Exact 49-pair assembly and evaluated main-kernel defect (8 November 2026)

[`PRZZPrimitiveKernel`](../lean/PRZZPrimitiveKernel.lean) proves uniqueness of the primitive coordinates `d=gcd(n,m)`, `u=n/d`, `v=m/d` and evaluates the full primitive triple sum at those coordinates. In particular `u` carries `beta` and `v` carries `alpha`. No general-profile analytic axiom is used in this exact arithmetic simplification.

[`PRZZKernelComparison`](../lean/PRZZKernelComparison.lean) identifies the density-oriented gcd kernel with the direct primitive kernel plus its reflected kernel weighted by the height power. Its difference from the actual Gamma diagonal kernel is exactly the Gamma-minus-power time integral times the reflected primitive kernel. The former is uniformly `O(1)` after time integration; the separated logarithmic shift pole costs `O(log T)`. Consequently one constant, before height and all indices, gives

$$|K_{\rm diag}(n,m)-K_{\rm density}(n,m)|\le C\log T/\operatorname{lcm}(n,m).$$

`arithmetic_defect_bound` retains arbitrary bounded complex coefficient slots and evaluates their sum by `C U V log(T) N (1+log N)`. This sufficient elementary bound is not advertised as the sharper harmonic-cube bound. The [kernel record](../checks/kernel-comparison-verification.json) checks the 292-module closure, with four fresh compilations and source/fingerprint-verified dependency reuse; its eleven target audits contain only standard axioms. The three existing Gamma supplier proofs were moved without changing their statements or names to the low-dependency [`PRZZGammaMultiplier`](../lean/PRZZGammaMultiplier.lean), re-exported by `PRZZZeroGammaBound`.

[`PRZZFamilyMoment`](../lean/PRZZFamilyMoment.lean) expands the original `PRZZExhaustiveAFEError.moment - diagonalMain` into all 49 **ordered** witness-basis pair errors. Compact-window integrability is proved from continuity, including the actual shifted zeta product; no formal linearity of a nonintegrable Bochner integral is used. `component_error_family` inserts the same expansion into the existing exhaustive AFE equality, retaining both branches and every collective central, tail, boundary, freeze, outside, zero-pair and Gamma-defect contribution. `witness_mainterm_bound` supplies the actual coefficient cap in the kernel comparison; `witness_mainterm_absorbed` places that evaluated defect in `C T^tau target` for **every** positive `tau`.

The analytic supplier in `witness_error_bound` is explicitly a bound for **all 49 mixed pairs**, not the seven separate square bounds. The exact assembly does not establish that supplier. Extending the profile-weighted Weil/DI blocks through every row and AFE residual to supply those mixed-pair bounds remains necessary before replacing the witness-only public input. The [family record](../checks/family-moment-verification.json) checks the 338-module closure and twelve target audits, all standard-only, including compilation of the moved Gamma suppliers' existing consumers. This is scoped dependency verification, not a whole-project rebuild. The eleven fail-closed audit/registry regression tests pass; the reading-aid test remains blocked by its intentionally retained old whole-project-record guard.

## Original moment estimate (7 November 2026)

[`PRZZMomentOptimal.moment_bound`](../lean/PRZZMomentOptimal.lean) proves, under the explicit `WeilIncomplete` and `DeshouillersIwaniecLemma1` hypotheses,

$$\left|\mathrm{moment}-\mathrm{diagonalMain}\right|
\le C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr).$$

Here `moment` is the actual weighted mollifier/zeta-product time integral, not merely a literal proxy; `diagonalMain` is the stated coupled two-branch main term. The theorem fixes `K ≥ 4`, coefficient labels `js`, `tau > 0`, bounded-shift radius `S`, separation `r > 0`, a smooth monotone plateau seed `P` taking values in `[0,1]` (one below `1/2`, zero above `1`), and a smooth compact time cutoff `Phi` supported in `[1,2]`. Its constant precedes height, `N` and the shifts. The conclusion holds eventually in height for `1 ≤ N ≤ T^(4/7)`, `N+1 ≤ T`, `log T ≥ 1`, `‖A‖, ‖B‖ ≤ S` and `r ≤ ‖A+B‖`, with shifts `A/log T`, `B/log T`.

`PRZZBodyTailMass`, `PRZZBodyTailTime`, `PRZZTailRowIntegrable`, `PRZZNativeTailRectangle`, `PRZZBodyTailCollector` and `PRZZBodyTailOptimal` connect the actual `bodyCut` tail, transfer-band/subunit corrections, native residual masses and finite row/time integration. In particular the final moment theorem no longer assumes an unevaluated `actualTail` bound. The printed audit of `moment_bound` is standard-only (`propext`, `Classical.choice`, `Quot.sound`); Weil and DI are theorem parameters, not proved deep inputs.

**Historical boundary:** this fixed-label separated-shift theorem alone did not substitute for the witness-only input. The 9 November switch above uses the stronger full finite-family theorem and the exact public witness bridge. The numerical witness is unchanged; the manuscript now includes the shift-placement note above. Earlier development entries describing unfinished connections are historical, not the current scope of `moment_bound`.

### Clean dependency verification

The [AF clean-build record](../checks/clean-af-verification-2026-11-07.json) checks the pinned, unmodified transitive source closure of all 16 AF imports: 101 AF modules rebuilt in a detached worktree with no initial AF output directory. Only fixed Mathlib/package caches were reused; inherited `LEAN_PATH` and old AF outputs were excluded. Lake's 3,788 job total includes cached package jobs and must not be read as 3,788 source rebuilds. Unrelated AF working-tree edits were preserved.

The [full local verification record](../checks/clean-project-verification-2026-11-07.json) covers the 698 local Lean sources present at the time of that record and 3,971 printed axiom audits. Every source was freshly compiled in a new temporary local output directory against the freshly built AF closure (six worker slots). Successful compiler diagnostics were saved with source hashes. Clean verification exposed audit-registry defects: one non-topological module ordering, three misplaced coverage entries, and several exact axiom sets that unnecessarily expected `Classical.choice` or `Quot.sound`. After correcting the registry, the final verifier rechecked all 698 source hashes and those same fresh compiler outputs successfully. This is not replay of the historical baseline records. No mathematical Lean source was changed for these registry corrections, and `sorryAx` is absent. At the time of that record, the sole explicit local axiom declaration was the general-profile input `PRZZ.przz41_case3_K2_profiles`, since removed; it was not the later witness-only input (itself now a proved theorem). The recorded audit of `moment_bound` itself prints only the standard three axioms.

The witness-only interface milestone had 701 sources: the three modules added after the 698-module record were `PRZZCoefficientPolarization`, `PRZZFiniteFamilyRows` and `PRZZDiagonalKernel`. The basis/mass milestone had 703 after `PRZZWitnessBasis` and `PRZZWitnessMass`, and the smooth-profile milestone had 705 after `PRZZProfileSmooth` and `PRZZProfileScale`. The moment/kernel milestone had 709 after `PRZZPrimitiveKernel`, `PRZZGammaMultiplier`, `PRZZKernelComparison` and `PRZZFamilyMoment`. The Mellin-class milestone had 711 after `PRZZMellinInterval` and `PRZZProfileMellin`. The HB-source milestone had 714 after `PRZZClassSources`, `PRZZClassVariation` and `PRZZClassDI`. The row-class milestone had 718 after `PRZZClassFreeLength`, `PRZZClassTypeI`, `PRZZClassCases` and `PRZZClassRows`. The mixed literal/defect milestone had 722 after `PRZZMixedLiteral`, `PRZZClassLiteral`, `PRZZMixedReplacement` and `PRZZMixedDefect`. The mixed Poisson/moment milestone had 724 after `PRZZMixedPoisson` and `PRZZMixedMoment`. The first positive-cell milestone had 725 after `PRZZClassPoisson`. The positive paired-grid milestone had 730 after adding `PRZZClassWideLiteral`, `PRZZClassWidePoisson`, `PRZZClassPositiveGrid`, `PRZZClassDualProfile` and `PRZZClassPairedGrid`. The signed-grid milestone had 740 after the ten spatial-source/negative/signed-grid modules. The zero-correction milestone had 744 after `PRZZClassZeroBoundary`, `PRZZClassZeroTail`, `PRZZClassZeroPrimalGap` and `PRZZClassZeroCorrection`. The common-cap tail/freezing milestone had 751 after seven new modules. The strict tail-band milestone had 756 after `PRZZCappedNativeTail`, `PRZZCappedStrictTail`, `PRZZCappedBandOuter`, `PRZZCappedSameMask` and `PRZZCappedTailBand`. The common-cap residual milestone had 763 after seven strict-freezing/discarded/large-spatial residual modules. The moment/main-term milestone had 765 after `PRZZCappedMomentBridge` and `PRZZCappedMainTerm`. The grid-identity milestone had 766 after `PRZZCentralGridIdentity`. The basis-grid milestone had 768 after `PRZZBasisGridCutoff` and `PRZZBasisGridBound`. The common-cap body-tail milestone had 772 after `PRZZCappedWindowBand`, `PRZZCappedSubunitMass`, `PRZZCappedBodyMass` and `PRZZCappedBodyTail`. The full-family moment milestone had **775**, adding `PRZZCappedGammaDefect`, `PRZZBasisPairedBody` and `PRZZFamilyMomentOptimal`. The current dependency-switch milestone has **778**, adding `PRZZWitnessBridge`, `PRZZProvedInput` and `PRZZAsymptoticCore`. None of these eighty additions is covered by the historical 698-module record. Scoped records and verified cache reuse must not be confused with a fresh full-project rebuild.

## Strict proportion and the earlier witness-only verification

[`WuProportion.strict_proportion`](../lean/WuProportion.lean) proves that there exists a fixed real `b > 0.8845` such that, for every sufficiently large real height `X`, `b * Ncount 0 X ≤ N0 0 X`. These are AF's actual xi-prime zero counts, with analytic multiplicity. `ratio_eventually_gt` gives the literal quotient inequality; the fixed-margin theorem also gives a strict asymptotic lower bound, not merely a pointwise strict inequality converging to 0.8845.

The final chain returns the quotient logarithm to the original left line via reverse Fatou and the regular H factor, supplies actual safe contours and their finite zero sets, proves the local count, includes retained zeros in `(T, 2*T]`, and uses AF's dyadic-to-cumulative theorem for all terminal heights. Thus an arbitrary-window Riemann--von Mangoldt adapter is not needed and is not claimed proved here. No `LocalizedEstimate`, `EndpointTight`, supplied counting gate, or simplicity premise enters the headline theorem.

The preceding witness-only audit required `propext`, `Classical.choice`, `Quot.sound`, and `PRZZ.przz41_case3_K2_witness`. The current switch above removes that analytic axiom dependency and exposes Weil/DI as theorem parameters instead. Standard-only axiom lists do not discharge those parameters.

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

The L1 files [`PRZZL1Finite`](../lean/PRZZL1Finite.lean), [`PRZZL1Truncation`](../lean/PRZZL1Truncation.lean) and [`PRZZL1Poisson`](../lean/PRZZL1Poisson.lean) provide preliminary finite/truncation interfaces and exact Poisson summation for smooth compact weights, including its Jacobian and residue phase. Their historical scope does not supply the full analytic replacement of the headline theorem's witness-only external input.

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
