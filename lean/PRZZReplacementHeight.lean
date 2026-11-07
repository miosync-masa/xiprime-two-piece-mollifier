import PRZZReplacementMass

/-! Height of the existing line-Re=2 replacement envelope. This is an audit
of that envelope, not a lower bound on the actual replacement error. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZReplacementHeight
open PRZZReplacementIntegral
set_option maxHeartbeats 2000000

theorem cost_lower (T : ℝ) (hT : 0 < T) :
    T/(4*Real.pi^2) ≤ cost T T := by
  have he : (T/(2*Real.pi))^2/T = T/(4*Real.pi^2) := by
    field_simp
    <;> ring
  unfold cost
  rw [he]
  exact le_add_of_nonneg_right (by positivity)

theorem cost_upper (T t : ℝ) (hT : 128 ≤ T) (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    cost T t ≤ 2*T := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hq0 : 0 ≤ t/(2*Real.pi) := by positivity
  have hq : t/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hq2 : (t/(2*Real.pi))^2 ≤ T^2 := by nlinarith
  have he : Real.exp (-T^2/64) ≤ 64/T^2 := by
    rw [show -T^2/64 = -(T^2/64) by ring,Real.exp_neg]
    have hh := Real.add_one_le_exp (T^2/64)
    have hh' : T^2/64 ≤ Real.exp (T^2/64) := by linarith
    calc
      _ = 1/Real.exp (T^2/64) := by simp
      _ ≤ 1/(T^2/64) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hh'
      _ = _ := by field_simp
  have hmain : (t/(2*Real.pi))^2/T ≤ T := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith
  have htail : (1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64) ≤ 128 := by
    calc
      _ ≤ (1+T^2)*(64/T^2) := mul_le_mul (by linarith) he
        (le_of_lt (Real.exp_pos _)) (by positivity)
      _ ≤ 128 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < T^2)).mpr
        <;> nlinarith
  unfold cost
  linarith

theorem weighted_cost (T : ℝ) (hT : 128 ≤ T) (phi : ℝ → ℂ)
    (hphi : Continuous phi) :
    (∫ t in Icc T (2*T), ‖phi t‖*cost T t) ≤
      2*T*(∫ t in Icc T (2*T), ‖phi t‖) := by
  rw [← integral_const_mul]
  have hc : Continuous (fun t => 2*T*‖phi t‖) := by fun_prop
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => by unfold cost; positivity))
    hc.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (mul_le_mul_of_nonneg_left (cost_upper T t hT ht.1 ht.2)
    (norm_nonneg _)).trans_eq (by ring)

/-- Substitute the height estimate into the actual coefficient-weighted
replacement integral. The remaining linear height cost is not hidden. -/
theorem integrated_source_height : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ js : List ℕ, ∀ N : ℕ, 1 ≤ N →
    ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t*difference a b t‖ ≤
      C*(1+16/‖a+b‖^2)*arithmeticMass *
        (4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js)) *
          (2*T*(∫ t in Icc T (2*T), ‖phi t‖)) := by
  obtain ⟨C,hC,h⟩ := PRZZReplacementMass.integrated_source
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T hT hT' js N hN phi hphi
  apply (h a b ha hb hs T hT hT' js N hN phi hphi).trans
  have hm : 0 ≤ arithmeticMass := tsum_nonneg (by intro p; positivity)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact mul_le_mul_of_nonneg_left (weighted_cost T hT' phi hphi) (by positivity)

#print axioms integrated_source_height
#print axioms cost_lower
#print axioms cost_upper
#print axioms weighted_cost
end XiPrime8845.PRZZReplacementHeight
