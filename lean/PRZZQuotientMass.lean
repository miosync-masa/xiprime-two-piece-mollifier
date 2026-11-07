import PRZZGroupedTime

/-! Eliminate k from each actual fibre and retain an explicit polynomial
height envelope for the actual Gamma kernel. No optimal error exponent is claimed. -/
noncomputable section
open scoped BigOperators
open Finset Complex
namespace XiPrime8845.PRZZQuotientMass
open PRZZAFEIndices PRZZAFEProgression PRZZGroupedTime PRZZActualDirectSum
open PRZZL1Finite PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

def project (i : PRZZAFEIndices.Index) : ℕ × ℕ × ℕ := (i.1.1,i.2.1,i.2.2)

def restore (z : Label) (p : ℕ × ℕ × ℕ) : PRZZAFEIndices.Index :=
  let d := Nat.gcd p.2.1 p.2.2
  let u : ℤ := (p.2.1/d : ℕ)
  let v : ℤ := (p.2.2/d : ℕ)
  ((p.1,((p.1*u-z.2.1)/v).toNat),(p.2.1,p.2.2))

theorem restore_project (L N : ℕ) (z : Label) (i : PRZZAFEIndices.Index)
    (hi : i ∈ fibre L N z) : restore z (project i) = i := by
  have hq := (fibre_quotient L N z i hi).2.1
  unfold restore project
  dsimp only
  rw [← hq,Int.toNat_natCast]

/-- A genuine sum over three indices. Its image domain preserves every
original bound and label; the eliminated k is evaluated by the signed quotient. -/
theorem fibre_sum (L N : ℕ) (z : Label) (f : PRZZAFEIndices.Index → ℂ) :
    (∑ i ∈ fibre L N z, f i) =
      ∑ p ∈ (fibre L N z).image project, f (restore z p) := by
  classical
  rw [sum_image]
  · apply sum_congr rfl
    intro i hi
    rw [restore_project L N z i hi]
  · intro i hi j hj he
    rw [← restore_project L N z i hi,← restore_project L N z j hj,he]

theorem grouped_sum (L N : ℕ) (f : PRZZAFEIndices.Index → ℂ) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z, f i) =
      ∑ z ∈ labels L N, ∑ p ∈ (fibre L N z).image project, f (restore z p) := by
  apply sum_congr rfl
  intro z hz
  exact fibre_sum L N z f

/-- The constant is chosen before shifts, height, time and x. The singular
sum-of-shifts factor is retained, rather than hidden in the constant. -/
theorem kernel_height : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
    ‖PRZZAFEGamma.kernel a b x t‖ ≤
      C*T^2*(1+1/‖a+b‖^2)*x^(-2:ℝ) := by
  obtain ⟨C,hC,h⟩ := PRZZKernelUniform.difference_uniform
  obtain ⟨D,E,hD,hE,hw⟩ := PRZZSourceWDerivatives.source_all_decay 0 2 (by norm_num)
  refine ⟨48*C+D+E+1,by positivity,?_⟩
  intro a b ha hb hs T t x hT hT' ht ht2 hx
  let q := t/(2*Real.pi)
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := hT0.trans_le ht
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqT : q ≤ T := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hq2 : q^2 ≤ T^2 := by nlinarith
  have hexp : Real.exp (-T^2/64) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg T])
  have hfrac : q^2/T ≤ T^2 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith [sq_nonneg T]
  have hbr : q^2/T+(1+q^2)*Real.exp (-T^2/64) ≤ 3*T^2 := by
    have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1+q^2 by positivity)
    nlinarith
  have hh := h a b ha hb hs T t x hT hT' ht ht2 hx
  have hm := hw (a+b) hs (x/q) (div_pos hx hq0)
  simp only [iteratedDeriv_zero,pow_zero,div_one] at hm
  have heq : (x/q)^(-2:ℝ) = q^2*x^(-2:ℝ) := by
    rw [Real.rpow_neg (by positivity),Real.rpow_two,Real.rpow_neg hx.le,Real.rpow_two]
    field_simp
  rw [heq] at hm
  have hmain : ‖sourceW (a+b) (x/q)‖ ≤ (D+E/‖a+b‖^2)*T^2*x^(-2:ℝ) := by
    rw [← mul_assoc] at hm
    apply hm.trans
    gcongr
  have herr : ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/q)‖ ≤
      C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(3*T^2) := by
    exact hh.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
  apply (norm_le_norm_sub_add _ (sourceW (a+b) (x/q))).trans
  apply (add_le_add herr hmain).trans
  have hs0 : 0 ≤ 1/‖a+b‖^2 := by positivity
  have hx0 : 0 ≤ x^(-2:ℝ) := Real.rpow_nonneg hx.le _
  have hp : 0 ≤ (45*C+E+1+(D+1)*(1/‖a+b‖^2))*T^2*x^(-2:ℝ) := by positivity
  apply sub_nonneg.mp
  convert hp using 1 <;> first | rfl | ring_nf

#print axioms restore_project
#print axioms fibre_sum
#print axioms grouped_sum
#print axioms kernel_height
end XiPrime8845.PRZZQuotientMass
