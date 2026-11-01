import Mathlib

/-! L0 specifications, NOT axioms and NOT proved estimates.

DI source: Deshouillers--Iwaniec, *Power mean-values for Dirichlet's
polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
305--312, Lemma 1 on p. 310, DOI 10.4064/aa-43-3-305-312.
Publisher scan: https://www.impan.pl/shop/en/publication/transaction/download/product/104164
PRZZ v3 reference [27] prints volume 48; the original scan/publisher is 43.

The incomplete Weil input below is a completion corollary, NOT a literal
theorem statement in Weil (1948). PRZZ v3 p. 21 invokes this corollary
together with partial summation. The weighted Type I and Type II adapters
are NOT supplied by these definitions. No implication to PRZZ 4.1 is asserted.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZKloostermanInputs

def e (x : ℝ) : ℂ := Complex.exp (2*Real.pi*Complex.I*(x:ℂ))

/-- Least nonnegative representative of the modular inverse. Every use in
the estimates is guarded by coprimality; this is not the real reciprocal. -/
def inverseResidue (q n : ℕ) : ℕ := ((n : ZMod q)⁻¹).val

def completeSum (q : ℕ) (a b : ℤ) : ℂ :=
  ∑ n ∈ (range q).filter (fun n => n.Coprime q),
    e (((a:ℝ)*n+(b:ℝ)*inverseResidue q n)/q)

/-- Prime-field form of Weil's bound (odd prime, both coefficients nonzero).
Weil, *On some exponential sums*, PNAS 34 (1948), 204--207, p. 207,
the prime-field display following the Kloosterman-sum display:
https://pmc.ncbi.nlm.nih.gov/articles/PMC1079093/
Paper (p,c,d,x) = Lean (p,a,b,n); coprimality expresses c,d nonzero mod p.
See also Harcos, *Weil's bound for Kloosterman sums*, Theorem 1, p. 1,
https://users.renyi.hu/~gharcos/weil.pdf.
This proposition is an input type, with no inhabitant supplied here. -/
def WeilPrime : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → ∀ a b : ℤ,
    a.natAbs.Coprime p → b.natAbs.Coprime p →
    ‖completeSum p a b‖ ≤ 2*Real.sqrt p

def incompleteSum (q : ℕ) (a : ℤ) (M H : ℕ) : ℂ :=
  ∑ n ∈ (Ioc M (M+H)).filter (fun n => n.Coprime q),
    e ((a:ℝ)*inverseResidue q n/q)

/-- Explicit unweighted completion obligation behind PRZZ's Type I step.
The q^eps loss absorbs divisor/log factors; the gcd is retained (not
silently set to one). M and H are unrestricted, hence the 1+H/q factor.
Proving WeilPrime -> this statement still requires prime-power estimates,
CRT and completion; it is intentionally NOT claimed as a theorem here. -/
def WeilIncomplete : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 1 ≤ q → ∀ a : ℤ, ∀ M H : ℕ,
      ‖incompleteSum q a M H‖ ≤
        C*Real.rpow q (1/2+ε)*(a.natAbs.gcd q)*(1+(H:ℝ)/q)

/-- The outer sums and inner absolute value are exactly those of DI Lemma 1.
Paper (C,D,U,V,rho,b(u,v)) = Lean (C,D,U,V,rho,b u v).
Real upper bounds are encoded using natural floors. -/
def diSum (C D U V : ℝ) (rho : ℕ) (b : ℕ → ℕ → ℂ) : ℝ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    ‖∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      b u v * e ((u:ℝ)*inverseResidue c (rho*v*d)/c)‖

def diBound (ε C D U V : ℝ) (rho : ℕ) : ℝ :=
  Real.rpow (C*D*U*V) (1/2+ε) *
    (Real.sqrt (C*D) + Real.rpow (U+V) (1/4) *
      Real.rpow (C*D*(U+(rho:ℝ)*V)*(C+(rho:ℝ)*V^2)+(rho:ℝ)*U*V^2*D^2) (1/4))

/-- DI Lemma 1, p. 310, with the implied constant quantified BEFORE rho,
the four length parameters and the coefficients. rho is a positive integer
(the rho introduced before (10) on the same page). No extra smoothness,
factorization of b(u,v), or coprimality of u is inserted. -/
def DeshouillersIwaniecLemma1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
    ∀ rho : ℕ, 1 ≤ rho → ∀ b : ℕ → ℕ → ℂ,
    (∀ u ∈ Icc 1 ⌊U⌋₊, ∀ v ∈ Icc 1 ⌊V⌋₊, ‖b u v‖ ≤ 1) →
      diSum C D U V rho b ≤ K*diBound ε C D U V rho

#print axioms WeilPrime
#print axioms WeilIncomplete
#print axioms DeshouillersIwaniecLemma1
end XiPrime8845.PRZZKloostermanInputs
