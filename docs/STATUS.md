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

This is equivalence with an **exact, untruncated** evaluator. Full equivalence with `paper/numerical_interval.py` remains open: the remaining exponential in each inverse jet must be replaced by its finite Taylor polynomial with a proved remainder bound, propagated through products, beta integration, kernel assembly and W contraction. The final Lean interval inequality also remains open. Python dictionary accumulation and mpmath rounding are not formally verified by the exact functional identity.

Remaining formal obligations include:

- connecting the exact integrated evaluator to the finite beta-coefficient evaluator with proved exponential remainder bounds, and closing the interval certificate in Lean;
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
