# Proof status

Updated: 28 October 2026. The fixed witness is unchanged. This status describes the mathematical claims, not a promise of a completed theorem.

## Three different verification levels

| Level | Evidence in this repository | What it does not prove |
| --- | --- | --- |
| Finite numerical functional | `paper/verify.py`, interval arithmetic and `paper/certificate.json` | That the functional equals the required arithmetic asymptotic |
| Finite formal algebra | `lean/KernelAlgebra.lean` | Analytic inverse Mellin inversion, Euler-factor error estimates, or zero counting |
| Analytic proof | `paper/manuscript.tex`, prepared as a draft for expert audit | A completed Lean proof or completed human peer review |

The reported proportion concerns zeros on the critical line counted with multiplicity. It is not a claim about simple zeros, and no global numerical optimality is asserted.

## Lean scope

`KernelAlgebra.lean` proves four K2 kernel expansions, the involution of the swapped exponential dual, the exact centered polynomial identity, profile endpoints, and rational length margins. Printed axiom dependencies are only `propext`, `Classical.choice` and `Quot.sound`.

`PRZZInterface.lean` contains exactly one explicit external analytic axiom, `XiPrime8845.PRZZ.przz41_case3_K2_profiles`. It specializes PRZZ Theorem 4.1, third case and its profile extension, to the needed coefficient family. It asserts a shifted moment estimate with the literal gcd/lcm double-sum main term. It does not assert the finite H-kernel or the final percentage.

The same file now proves the fixed witness's uniform coefficient bound and `Subpower` instance. The theorem `witness_przz_estimate` applies the external axiom without residual coefficient-growth hypotheses. Its only nonstandard axiom is the explicitly named PRZZ input. The coefficient proofs themselves do not depend on that axiom.

`AFProbe.lean` checks existing weighted rectangle argument-principle, Jensen and xi-prime counting APIs. These checks use a prebuilt pinned AF environment. They are not a clean rebuild of every AF theorem.

Remaining formal obligations include:

- finite inverse-operator evaluation, jets and the interval certificate in Lean;
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
