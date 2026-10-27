import Mathlib

/- Specification prototype: exactly ONE external analytic axiom below.
This is the K2/profile specialization of PRZZ Theorem 4.1, third case,
including the profile extension described in its proof (p. 18).
It is NOT a formal proof of that published theorem, a residue-asymptotic
axiom, or a certificate of the final zero proportion.
-/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Filter
namespace XiPrime8845.PRZZ

structure Profiles where
  conrey : Polynomial ℝ
  feng : Polynomial ℝ

def muReal : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ), by simp⟩

def fengArithmetic : ArithmeticFunction ℝ :=
  muReal * ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt

def length (theta T : ℝ) : ℝ := Real.rpow T theta
def cutoff (theta T : ℝ) : ℕ := ⌊length theta T⌋₊

def coefficient (P : Profiles) (theta T : ℝ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ (n : ℝ) ≤ length theta T then
    let u := Real.log (length theta T / n) / Real.log (length theta T)
    ((muReal n * P.conrey.eval u + fengArithmetic n * P.feng.eval u /
      (Real.log (length theta T))^2 : ℝ) : ℂ)
  else 0

/-- Uniform in T; this remains a proof obligation for our coefficient family. -/
def Subpower (a : ℝ → ℕ → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 1 ≤ n → ‖a T n‖ ≤ C * Real.rpow n eps

def dirichletPolynomial (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ)^s

def twistedMoment (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  ∫ t : ℝ,
    riemannZeta (1/2 + A/(Real.log T : ℂ) + t*I) *
    riemannZeta (1/2 + B/(Real.log T : ℂ) - t*I) *
    dirichletPolynomial (coefficient P theta T) (cutoff theta T) (1/2 + t*I) *
    star (dirichletPolynomial (coefficient Q theta T) (cutoff theta T) (1/2 + t*I)) *
    (Phi (t/T) : ℂ)

/-- Literal double-sum main term, only asserted away from A+B=0.
The two zeta terms are NOT replaced by their individual values at the pole. -/
def gcdMainTerm (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  let alpha := A/(Real.log T : ℂ)
  let beta := B/(Real.log T : ℂ)
  ∑ d ∈ Finset.Icc 1 (cutoff theta T), ∑ e ∈ Finset.Icc 1 (cutoff theta T),
    coefficient P theta T d * star (coefficient Q theta T e) / (Nat.lcm d e : ℂ) *
    (Nat.gcd d e : ℂ)^(alpha+beta) / ((d : ℂ)^alpha * (e : ℂ)^beta) *
    ∫ t : ℝ, (riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
      ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ)

def SmoothWeight (Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ Phi ∧ Function.support Phi ⊆ Set.Icc 1 2

/-- External published analytic input, restricted to the coefficient family
needed here. Cross terms use independently specified P and Q.
No use of squarefree truncation, no RH, no main-term H-kernel in the type.
Uniformity excludes A+B=0; a fixed bidisc about (-R,-R), radius <R/2,
suffices for our later Cauchy derivatives. The holomorphic differentiation
argument and the leading-pole reduction remain separate tasks. -/
axiom przz41_case3_K2_profiles
    (P Q : Profiles) (theta : ℝ) (hTheta0 : 0 < theta) (hTheta1 : theta < 4/7)
    (hP : Subpower (coefficient P theta)) (hQ : Subpower (coefficient Q theta))
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (shiftBound poleGap eps : ℝ) (hShift : 0 < shiftBound)
    (hGap : 0 < poleGap) (hEps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖twistedMoment P Q theta T Phi A B - gcdMainTerm P Q theta T Phi A B‖ ≤
        C * Real.rpow T eps *
          (Real.rpow (length theta T) (7/4) +
           Real.rpow (length theta T) (7/8) * Real.rpow T (1/2))

def witness : Profiles where
  conrey := Polynomial.C (-0.30528514) * Polynomial.X + Polynomial.C 2.50038954 * Polynomial.X^2 -
    Polynomial.C 1.12177152 * Polynomial.X^3 - Polynomial.C 0.07333288 * Polynomial.X^4
  feng := Polynomial.C 1.89779072 * Polynomial.X + Polynomial.C 0.56594804 * Polynomial.X^2 +
    Polynomial.C 0.07023055 * Polynomial.X^3

theorem witness_endpoints : witness.conrey.eval 0 = 0 ∧ witness.feng.eval 0 = 0 ∧
    witness.conrey.eval 1 = 1 := by
  norm_num [witness]

theorem witness_length : (0 : ℝ) < 4/7-1/1000000 ∧ (4/7-1/1000000 : ℝ) < 4/7 := by
  norm_num

theorem coefficient_support (P : Profiles) (theta T : ℝ) (n : ℕ)
    (hn : ¬(1 ≤ n ∧ (n : ℝ) ≤ length theta T)) : coefficient P theta T n = 0 := by
  simp [coefficient, hn]

#print axioms witness_endpoints
#print axioms przz41_case3_K2_profiles
end XiPrime8845.PRZZ
