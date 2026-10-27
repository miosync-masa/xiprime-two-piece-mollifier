import Mathlib

/- Finite algebra only. No PRZZ axiom and no analytic main-term claim. -/
namespace XiPrime8845
noncomputable section

def pairedKernel (l m : ℕ) (X Y h : ℂ) : ℂ :=
  X * Y / h * ∑ k ∈ Finset.range (min l m + 1),
    (Nat.choose l k : ℂ) * (m.descFactorial k : ℂ) / h ^ (2*k) *
      (1/h - 1/X) ^ (l-k) * (1/h - 1/Y) ^ (m-k)

theorem kernel00 (X Y h : ℂ) : pairedKernel 0 0 X Y h = X*Y/h := by
  simp [pairedKernel]

theorem kernel20 (X Y h : ℂ) (hX : X ≠ 0) (hh : h ≠ 0) :
    pairedKernel 2 0 X Y h = X*Y/h^3 - 2*Y/h^2 + Y/(X*h) := by
  simp [pairedKernel]
  field_simp
  ring

theorem kernel02 (X Y h : ℂ) (hY : Y ≠ 0) (hh : h ≠ 0) :
    pairedKernel 0 2 X Y h = X*Y/h^3 - 2*X/h^2 + X/(Y*h) := by
  simp [pairedKernel]
  field_simp
  ring

theorem kernel22 (X Y h : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (hh : h ≠ 0) :
    pairedKernel 2 2 X Y h =
      7*X*Y/h^5 - 6*(X+Y)/h^4 + (X/Y+Y/X+8)/h^3 -
      2*(X⁻¹+Y⁻¹)/h^2 + 1/(X*Y*h) := by
  norm_num [pairedKernel, Finset.sum_range_succ, Nat.descFactorial]
  field_simp
  ring

def swapNeg (p : ℂ × ℂ) : ℂ × ℂ := (-p.2, -p.1)

theorem swapNeg_involutive : Function.Involutive swapNeg := by
  intro p
  simp [swapNeg]

noncomputable def dual (H : ℂ → ℂ → ℂ) (A B : ℂ) : ℂ :=
  Complex.exp (-A-B) * H (-B) (-A)

theorem dual_involutive (H : ℂ → ℂ → ℂ) (A B : ℂ) :
    dual (dual H) A B = H A B := by
  simp only [dual, neg_neg]
  rw [← mul_assoc, ← Complex.exp_add]
  have h : -A - B + (- -B - -A) = 0 := by ring
  simp only [neg_neg] at h
  rw [h, Complex.exp_zero, one_mul]

def theta : ℚ := 4/7 - 1/1000000
def radiusParameter : ℚ := 1.04440033
def q (x : ℚ) : ℚ := 1 - 2.27043254*x + 0.304358115*x^2 + 0.16793368*x^3 +
  4.34152016*x^4 - 5.3105844*x^5 + 1.7701948*x^6
def p1 (x : ℚ) : ℚ := -0.30528514*x + 2.50038954*x^2 - 1.12177152*x^3 - 0.07333288*x^4
def p2 (x : ℚ) : ℚ := 1.89779072*x + 0.56594804*x^2 + 0.07023055*x^3

theorem profiles_endpoints : p1 0 = 0 ∧ p2 0 = 0 ∧ p1 1 = 1 := by
  norm_num [p1, p2]

theorem centered_q (u : ℚ) : q (1/2-u) =
    0.09491351 + 0.997010185*u + 2.089866*u^2 - 2.29671034*u^4 + 1.7701948*u^6 := by
  unfold q
  ring

theorem length_margin : 0 < theta ∧ theta < 4/7 ∧
    (7/4)*theta = 1-7/4000000 ∧ (7/8)*theta+1/2 = 1-7/8000000 ∧
    0 < radiusParameter*theta ∧ radiusParameter*theta < 1 := by
  norm_num [theta, radiusParameter]

theorem error_exponents_below_one :
    (7/4)*theta + 7/16000000 < 1 ∧
    (7/8)*theta+1/2+7/16000000 < 1 := by
  norm_num [theta]

#print axioms kernel22
#print axioms dual_involutive
#print axioms centered_q
#print axioms length_margin
end
end XiPrime8845
