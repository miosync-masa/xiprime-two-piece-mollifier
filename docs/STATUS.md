# Proof status

Updated: 28 October 2026. The fixed witness is unchanged. This status describes the mathematical claims, not a promise of a completed theorem.

## Verification levels

| Level | Evidence in this repository | What it does not prove |
| --- | --- | --- |
| Finite numerical functional | `paper/verify.py`, interval arithmetic and `paper/certificate.json` | That the functional equals the required arithmetic asymptotic |
| Finite formal algebra | `lean/KernelAlgebra.lean` | Analytic inverse Mellin inversion, Euler-factor error estimates, or zero counting |
| Finite inverse, quotient and dual jets | `lean/FiniteJet.lean` | Exponential remainder bounds or the final interval inequality |
| Beta coefficients and K2 assembly | `lean/BetaKernel.lean` | Full equivalence of the integrated functional with the numerical evaluator |
| Exact integrated K2 evaluator | `lean/IntegralJet.lean` | Taylor-truncated Python evaluator semantics, rounding, interval certification, or arithmetic main-term identification |
| Full K2 Taylor error envelope | `lean/TaylorEnvelope.lean` | Equality with Python's sparse error envelope or the final numerical interval inequality |
| Finite beta-coefficient evaluator | `lean/CoefficientEvaluator.lean` | Python execution/rounding semantics, a numerical enclosure of the coefficient expression, or arithmetic main-term identification |
| Fixed exponential and aggregate-error bounds | `lean/NumericalGate.lean` | Its scalar helper requires the coefficient bound supplied by `FixedCertificate` |
| Executable rational coefficient semantics | `lean/RationalEvaluator.lean` | Arithmetic main-term identification or Python execution semantics |
| Kernel-checked fixed finite inequality | `lean/RationalBounds.lean`, `lean/FixedCertificate.lean` | Leading-pole asymptotics or zero counting |
| Analytic proof | `paper/manuscript.tex`, prepared as a draft for expert audit | A completed Lean proof or completed human peer review |

The reported proportion concerns zeros on the critical line counted with multiplicity. It is not a claim about simple zeros, and no global numerical optimality is asserted.

## Lean scope

`KernelAlgebra.lean` proves four K2 kernel expansions, the involution of the swapped exponential dual, the exact centered polynomial identity, profile endpoints, and rational length margins. Printed axiom dependencies are only `propext`, `Classical.choice` and `Quot.sound`.

`PRZZInterface.lean` contains exactly one explicit external analytic axiom, `XiPrime8845.PRZZ.przz41_case3_K2_profiles`. It specializes PRZZ Theorem 4.1, third case and its profile extension, to the needed coefficient family. It asserts a shifted moment estimate with the literal gcd/lcm double-sum main term. It does not assert the finite H-kernel or the final percentage.

The same file now proves the fixed witness's uniform coefficient bound and `Subpower` instance. The theorem `witness_przz_estimate` applies the external axiom without residual coefficient-growth hypotheses. Its only nonstandard axiom is the explicitly named PRZZ input. The coefficient proofs themselves do not depend on that axiom.

`AFProbe.lean` checks existing weighted rectangle argument-principle, Jensen and xi-prime counting APIs. These checks use a prebuilt pinned AF environment. They are not a clean rebuild of every AF theorem.

`FiniteJet.lean` proves exact polynomial integration by finite coefficient sums, identifies the Taylor-truncated inverse convolution with its integral, and represents that truncated inverse as a polynomial in the complex shift. Polynomial coefficients at a translated origin equal normalized iterated derivatives. The file also proves exponential, reciprocal-denominator, reflected-shift, dual Leibniz and separable two-variable jet identities. The orders are arbitrary natural numbers, so the witness's independent orders 0 through 6 are included. The verifier audits 30 printed theorem dependencies against the three standard axioms, including 17 quotient/dual/contraction results.

`reciprocal_mixed_jet` identifies the normalized mixed derivative of $1/(A+B)$, for $A+B\ne0$, with

$$
r_{ij}(A+B)=\frac{(-1)^{i+j}\binom{i+j}{i}}{(A+B)^{i+j+1}}.
$$

`quotient_contract₂_W` proves that the actual successive differential operators on $f(A)g(B)/(A+B)$ equal contraction of the separate jets with $W$. Its hypotheses are finite-order smoothness of $f,g$ and the nonzero denominator; the derivative identity is not a hypothesis. `W_eq_evaluator` proves the exact summation limits and coefficient expression used in `paper/numerical_interval.py`, for arbitrary finite order $D$.

`dual_op_contraction` derives the positive weights

$$
\operatorname{op}^{+}_i=i!\sum_{n=i}^{D}q_n\binom ni
$$

from local derivatives of $e^{-A}f(-A)$. `dual_contract₂` applies this in both variables, with explicit local slice-jet regularity. `dual_quotient_W` discharges those local regularity conditions for smooth separable quotient numerators and retains the swapped arguments. `dual_quotient_diagonal` then gives the evaluator's positive-side $W$ and exponential factor: at $A=-R$, the result uses $W(2R)$ and $e^{2R}$. The sign of the original dual numerator cancels the sign of the reflected denominator. `W_symm` and `W_profile_swap` justify exchanging the two derivative arrays after contraction, not merely exchanging undifferentiated values.

`BetaKernel.lean` proves the general integer beta integral by integration by parts and induction:

$$
\int_0^w x^j(w-x)^d\,dx=\frac{j!d!}{(j+d+1)!}w^{j+d+1}.
$$

Its `inverseJetEval_eq_integral` proves the finite coefficient sum used by the inverse branch `fs(P,-1,A)[a]`: this is the integral of the differentiated exponential integrand after Taylor truncation. `outer_beta_order` and `outer_polynomial` prove the outer beta coefficient formula and its polynomial extension. The parameter orders, profile coefficients and endpoints are arbitrary, not sampled fixtures.

The same file evaluates all four K2 coefficient sums under an arbitrary Laurent-monomial evaluation, defines their actual finite integrals and the swapped exponential dual functional, and proves `H02_swap`. The two ordered cross terms are combined only on the undifferentiated diagonal. A general finite-sum transposition and the binomial formula for the coefficients of `q(X+1)` also compile. The verifier audits 16 new theorem dependencies against the three standard axioms.

The order of operations matters: `FiniteJet.inverseShiftPoly` truncates the exponential before differentiating, whereas the numerical evaluator differentiates the exponential and then truncates the remaining exponential in each jet. The new `inverseJetEval` follows the latter order; the two finite polynomials are not identified with one another.

`IntegralJet.lean` proves differentiation under the inverse-operator and outer v-integrals. Its compact-interval dominated-derivative argument supplies the needed derivative bounds rather than assuming the interchange identity. `inverse_operator_jet` identifies the actual derivatives of the untruncated exponential convolution. Joint continuity, including the zero endpoint, and all-order complex smoothness are proved for the three K2 operators. `monomialIntegral_jet₂` then identifies the actual mixed derivatives of each outer integral with the integral of the two operator jets.

`quotient_general_W` extends the quotient contraction to a nonseparable numerator with a full mixed-jet array. The actual K2 numerator satisfies its regularity conditions. `K2_exact_evaluator` proves, for arbitrary finite order D, coefficient sequence q, polynomial profiles and complex shifts A+B != 0, that the successive differential operators applied to `BetaKernel.shiftedFunctional` equal `exactEvaluator`: the direct W contraction plus the reflected positive-op W contraction with its exponential factor. Its statement has no assumed derivative-interchange or evaluator-equivalence hypothesis. `contracted_fourTerms_diagonal` proves the integrated cross-term reduction after differentiation and W contraction, retaining both ordered cross terms until that step. All 31 printed dependencies in this module are audited against only `propext`, `Classical.choice` and `Quot.sound`; no PRZZ axiom is imported.

This is equivalence with an **exact, untruncated** evaluator. The next module supplies the truncation error; it does not formally verify Python dictionary accumulation or mpmath rounding.

### Taylor error enclosure

`TaylorEnvelope.lean` replaces the remaining exponential in each normalized inverse jet by its degree-N Taylor polynomial, **after** differentiation. For theta > 0, 0 <= w <= theta and norm(A) theta <= 1, `inverse_operator_error` proves

$$
\left\|D_{-1}^{[a]}(A,w)-D_{-1,N}^{[a]}(A,w)\right\|
\le B_a(F,\theta)\,\tau_N(\|A\|\theta),\qquad
B_a(F,\theta)=\frac{3C_F\theta^{a+1}}{a!(a+1)},\quad
\tau_N(r)=\frac{r^{N+1}}{(N+1)!},
$$

where $C_F$ is the sum of the absolute values of the profile coefficients. `inverse_operator_bound` proves the corresponding exact-jet bound $B_a$. The constant 3 comes from a proved complex exponential Taylor estimate, not an assumed remainder formula.

For each pair of jets, `product_error` propagates exact-factor bounds and errors as $E_fB_g+E_gB_f+E_fE_g$. `monomial_error` integrates the outer power weight to obtain the factor $\theta^n/n!$. Absolute coefficient sums then propagate these errors through the literal pole sum, all four ordered K2 terms, and the direct and reflected W contractions. The dual exponential is retained exactly, with its norm multiplying the reflected error.

The final theorem `K2_Taylor_enclosure`, assuming only $A+B\ne0$, $\theta>0$, $\|A\|\theta\le1$ and $\|B\|\theta\le1$, proves

$$
\left\|q(-\partial_A)q(-\partial_B)\mathcal I(A,B)
-\operatorname{finiteEvaluator}_N(A,B)\right\|
\le \operatorname{evaluatorError}_N(A,B).
$$

Here q is the finite coefficient sequence through the chosen order D. `finiteEvaluator` is defined using integrals of Taylor-polynomial jets; `evaluatorError` is an explicit finite expression in norms, coefficients, powers, factorials, W weights and the dual exponential. The theorem has no assumed derivative-interchange, evaluator-equivalence or error-bound hypothesis. All 13 printed theorem dependencies are audited against only `propext`, `Classical.choice` and `Quot.sound`.

The noninverse-operator bound is intentionally looser than the order-specific sparse bound in `paper/numerical_interval.py`. The two envelopes are not asserted to be identical. `NumericalGate.lean` certifies a coarse numerical bound on this Lean envelope; `FixedCertificate.lean` uses it to close the finite inequality below.

### Coefficient evaluator equivalence

`CoefficientEvaluator.lean` proves the beta formula for complex coefficients, with real endpoints. `inversePoly_eval` identifies each differentiated-then-truncated inverse jet with a polynomial in the remaining endpoint w. Its coefficient contributions are exactly

$$
\frac{p_d}{\theta^d}\frac{(-1)^a(-A)^j(a+j)!d!}{a!j!(d+1+a+j)!}
\quad\text{at degree }d+1+a+j.
$$

`inversePoly_coeff` proves accumulation when several contributions have the same output degree. `fsPoly_eval` covers all three K2 exponents, including the sparse zero/first derivative branches for the noninverse operators. `betaEval_integral` and `monomial_coefficients` replace the outer polynomial integrals by the exact coefficient sum

$$
\sum_d c_d\frac{\theta^{d+n}d!}{(d+n)!}.
$$

`fusedPoly_coeff` proves convolution of polynomial coefficients at degree da+db. `fusedPoly_cached` identifies the computation that first forms the W-weighted right-jet polynomial for each left jet. Linearity of the beta sum and `weighted_poleSum` justify moving these finite contractions before outer evaluation and the pole loops. `pairEvaluator_fused` connects the complete normalized profile-pair expression to this cached-polynomial order of computation.

`pair_cross_swap` proves the contracted cross symmetry using W symmetry and the swap of the two jet indices; it does not substitute an undifferentiated diagonal identity. The two ordered cross terms therefore reduce to one with weight 2. `coefficientEvaluator_diagonal` retains the negative-side op and the positive-side shifted op, together with the exact dual factor exp(2R).

The main equality `finiteEvaluator_cached` identifies the Taylor-polynomial integral expression with `cachedEvaluator`, a coefficient-only model of the two-sign, three-profile-pair computation in `paper/numerical_interval.py`. This model has no unevaluated integral or derivative; the dual exponential is retained exactly. `K2_cached_enclosure` carries the previous error bound all the way from the actual differentiated K2 functional to that coefficient expression, under R != 0, theta > 0 and |R| theta <= 1. All 18 printed theorem dependencies use only the standard three axioms, without the PRZZ input or `sorryAx`.

This completes the exact-arithmetic coefficient semantics and truncation bridge. It is not a formal verification of Python dictionary execution or mpmath outward rounding.

### Fixed exponential and aggregate-error certificate

`NumericalGate.lean` fixes exactly the existing q, R, theta and profiles; `profile_witness_matches`, `q_witness_matches` and `parameters_match` prove agreement with `KernelAlgebra.lean`. The scalar exponential bounds are

$$
e^{R(1-.8845)}>1.1282054105,\qquad
8.075224414565<e^{2R}<8.075224414566.
$$

The target lower bound uses a positive finite exponential sum. The dual bounds use a proved remainder at R/2 followed by a fourth power. All rational comparisons are checked by Lean proof terms, with no `native_decide`, external numerical axiom or JSON input.

`total_error_bound` certifies the **entire** degree-24 `evaluatorError` as at most $10^{-6}$. It uses coefficient norms at most 5, derivative coefficient norms at most 10, both op arrays bounded by 5000, coarse W bounds, the literal pole-coefficient absolute sums, and the dual exponential bound. This is a deliberately loose bound for the Lean envelope, not the sharper Python interval width.

`actual_sub_finite` combines that numerical bound with `K2_cached_enclosure`:

$$
\left|M_{\rm functional}-C_{24}\right|\le10^{-6},
$$

where `actual` is the differentiated complex K2 functional and `finiteValue` is the fixed cached coefficient expression. The scalar helper `fixed_finite_gate` takes the explicit premise `finiteValue.re <= 1.12820`; the following modules now prove it. The 26 printed theorem dependencies in `NumericalGate` are the standard three axioms only.

### Closed fixed finite gate

`RationalEvaluator.lean` implements polynomial addition, scalar multiplication, multiplication, inverse-jet coefficients, beta evaluation, W contraction and the literal pole sum over rational coefficient lists. Its interpretation theorems identify these operations with the existing complex polynomial model. `finiteValue_exact` proves the exact fixed-witness identity

$$
C_{24}=m+e^{2R}p,
$$

with executable rational values m and p. The original q, R, theta and both profiles are unchanged. The rational values are large and cancel; the calculation retains their exact rational arithmetic.

`RationalBounds.rational_bounds` proves, by `decide +kernel`,

$$
m\le-588381.5413543881,\qquad
0\le p\le72862.7019299614.
$$

`FixedCertificate.finiteValue_upper` combines these bounds with the proved dual-exponential upper bound to obtain `finiteValue.re <= 1.12820`. Adding the proved total error gives `actual_upper`:

$$
\operatorname{Re}M_{\rm functional}\le1.128201
<1.1282054105<e^{R(1-.8845)}.
$$

The theorem **`FixedCertificate.fixed_functional_gate` has no numerical premise**. Its printed dependencies are only `propext`, `Classical.choice` and `Quot.sound`. Neither `native_decide`, a numerical axiom, a trusted JSON value, nor the PRZZ axiom enters this finite certificate. It is coarser than the independent Python interval, and does not claim the Python interval's full decimal precision.

Remaining formal obligations include:

- analytic Mellin inversion and the uniform leading-pole asymptotic;
- the Wu auxiliary-function counting argument, boundary zeros and Littlewood connection;
- shift differentiation, exact-V comparison, smoothing and cumulative-count limits.

For the fixed profiles, the elementary paper bound is

$$
|\mu*\Lambda*\Lambda|(n)\le(\log n)^2,
\qquad |a_n(T)|\le 6.53474839.
$$

Both bounds are now Lean theorems. The coefficient bound holds uniformly for every real theta > 0, T >= 2 and natural n, including n = 0 and indices outside the support. The convolution bound is stated for n >= 1 and retains repeated prime factors. The profile estimates use their exact rational coefficients on [0,1].

`witness_normalized_error_tendsto_zero` proves that the literal PRZZ error envelope divided by T tends to zero for theta = 4/7 - 10^-6 and epsilon = 7/16000000. It is a limit theorem, not just a numerical exponent check. This does not evaluate the gcd/lcm main term or its shift derivatives.

The verifier audits the printed axiom sets of the convolution, profile, coefficient, Subpower and normalized-error theorems: only `propext`, `Classical.choice` and `Quot.sound` are allowed. It separately checks the additional PRZZ axiom in `witness_przz_estimate`.

The target numerator would be AF's `Zeta23.XiPrime.N0`, not `N0simple`; the manuscript denominator is the zeta zero count.

## Analytic review

The exact review questions are in [the audit guide](../paper/README.md#questions-requiring-analytic-review). In particular, the transition from PRZZ's coefficient sum to the finite leading-pole functional and the Wu counting interface must be checked independently of the numerical margin.

An eventual theorem relative only to PRZZ must have no other custom analytic axiom, no `sorryAx`, and no trusted numerical JSON input in its axiom dependencies.
