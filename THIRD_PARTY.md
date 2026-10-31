# External dependencies and attribution

Except for the explicitly attributed adaptation below, no AF, mathlib, mpmath or third-party action implementation is included in this distribution. Their licenses and notices remain with their respective upstream projects.

`lean/WuHorizontalIntegral.lean` adapts the horizontal partial-fraction integration proof from AF's `Zeta23/XiPrime/ZeroCount/Generic.lean` at the pin below. The adaptation permits arbitrary endpoints and separates the zero-mass and remainder constants. The source copyright notice (2026 Anthropic, PBC) is retained; this adapted file is distributed under Apache-2.0, whose text is included in `licenses/AF-Apache-2.0.txt`. This does not change the license status of other original project material.

| Dependency | Role | Pin or source |
| --- | --- | --- |
| mpmath | Numerical interval arithmetic | `1.3.0`, installed separately |
| AF Lean library | Analytic and xi-prime APIs | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` in [formal-math](https://github.com/anthropics/formal-math) |
| mathlib | Lean mathematical library | `51e6992efd06126df61a496bebf8f49482a4e129`, through AF |
| Lean | Proof checker | `v4.33.0-rc2` |
| GitHub Actions checkout/setup-python | Optional CI infrastructure | Commit pins in the workflow |

The paper cites Wu and PRZZ for the analytic inputs and distinguishes AF's simple-and-on-line result from the present multiplicity-counted claim. No third-party paper PDF is redistributed.

License selection for the original material in this directory is pending the maintainer's decision. This notice does not grant a new license or alter any upstream license.
