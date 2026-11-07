import PRZZCosineGapMellin
import PRZZGammaFar

/-! Bounds for the reflected diagonal kernel on the positive strip
1/8 <= Re s <= 5/4. The reflected definition is regular even where the
naive zeta/Gamma/cosine product has a removable singularity. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZReflectedEnvelope
open PRZZDyadicEnvelope PRZZDiagonalMellin
set_option maxHeartbeats 5000000

def kernel (sigma : ℂ) (X : ℝ) (s : ℂ) : ℂ := integrand (-sigma) X (-s)

theorem analytic (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (X : ℝ) (hX : 0 < X)
    (s : ℂ) (hs : 1/16 < s.re) : DifferentiableAt ℂ (kernel sigma X) s := by
  have hr := (abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)).1
  have hd := PRZZDiagonalContour.integrand_differentiable (-sigma) X hX (-s)
    (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
    (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
  exact hd.comp s (by fun_prop)

theorem reflection_factor (sigma : ℂ) (X : ℝ) (s : ℂ)
    (hz : 0 < (2*s+sigma).re) (hz1 : 2*s+sigma ≠ 1) :
    kernel sigma X s*((2*Real.pi:ℝ):ℂ)^(2*s+sigma) =
      ((X:ℂ)^(-s)*exp (s^2)*annihilator sigma s/s)*
        (2*riemannZeta (2*s+sigma)*Gamma (2*s+sigma)*
          cos ((Real.pi:ℂ)*(2*s+sigma-2)/2)) := by
  have he := PRZZZeroReflection.cosine_functional (2*s+sigma) hz hz1
  have ha : annihilator (-sigma) (-s) = annihilator sigma s := by
    unfold annihilator; simp only [neg_sq,mul_neg,neg_sq]
  unfold kernel integrand amplitude
  rw [ha,neg_sq,show 1+ -sigma+2*(-s) = 1-(2*s+sigma) by ring,he]
  ring

theorem cos_norm (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (exp (-z*I)) (exp (z*I))
  have he := congrArg norm (Complex.two_cos (x := z))
  simp only [norm_mul,Complex.norm_ofNat,norm_exp,mul_re,neg_re,neg_im,
    I_re,I_im,mul_zero,mul_one,zero_sub,neg_neg] at he h
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  rw [add_comm] at h
  linarith

theorem gamma_cap : ∃ G : ℝ, 0 < G ∧ ∀ z : ℂ,
    1/8 ≤ z.re → z.re ≤ 3 → ‖Gamma z‖ ≤ G := by
  have hc : ContinuousOn (fun r : ℝ => Gamma (r:ℂ)) (Icc (1/8:ℝ) 3) := by
    intro r hr
    exact ((PRZZGammaPath.gamma_analytic (r:ℂ) (by simp; linarith [hr.1])).continuousAt.comp
      (x := r) Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨G,hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max G 0+1,by positivity,?_⟩
  intro z hz hz'
  have hg := PRZZGammaFar.gamma_norm_le z (by linarith)
  have hre : Real.Gamma z.re ≤ ‖Gamma (z.re:ℂ)‖ := Complex.re_le_norm _
  exact hg.trans (hre.trans ((hG z.re ⟨hz,hz'⟩).trans (by linarith [le_max_left G 0])))

theorem tail_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/8 ≤ s.re → s.re ≤ 5/4 → 1 ≤ |s.im| →
      ‖kernel sigma X s‖ ≤ C*(1+|s.im|)^4*Real.exp (-s.im^2/2) := by
  obtain ⟨G,hG,hcap⟩ := gamma_cap
  let C := Real.exp (2*|Real.log X|)*(1+16/‖sigma‖^2)*
    (2*G*50)*Real.exp (4+Real.pi+Real.pi^2/2)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s hlo hhi him
  let V := 1+|s.im|
  let z := 2*s+sigma
  have hV : 1 ≤ V := by dsimp [V]; linarith [abs_nonneg s.im]
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  have hi := (abs_im_le_norm sigma).trans hn
  have hzr : 1/8 ≤ z.re ∧ z.re ≤ 3 := by
    dsimp [z]; simp only [add_re,mul_re]; norm_num
    constructor <;> linarith [hr.1,hr.2]
  have hzi : 1 ≤ |z.im| := by
    have hh := abs_add_le z.im (-sigma.im)
    have he : z.im + -sigma.im = 2*s.im := by simp [z]
    rw [he,abs_mul,abs_neg] at hh
    norm_num at hh
    linarith
  have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzi
  have hzN : ‖z‖ ≤ 6*V := by
    have hsN := norm_le_abs_re_add_abs_im s
    have hzN := (norm_add_le (2*s) sigma)
    norm_num [norm_mul] at hzN
    have hsabs : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
    dsimp [z,V]; linarith
  have hzeta : ‖riemannZeta z‖ ≤ 50*V := by
    have hz := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (by linarith : 0 < z.re) hz1
    have hd : ‖z‖/z.re ≤ 8*‖z‖ := (div_le_iff₀ (by linarith)).mpr (by nlinarith [norm_nonneg z])
    have hp : 1 ≤ ‖1-z‖ := hzi.trans (by simpa using abs_im_le_norm (1-z))
    have hv : 1/‖1-z‖ ≤ (1:ℝ) := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
    linarith
  have hg := hcap z hzr.1 hzr.2
  have hcos : ‖cos ((Real.pi:ℂ)*(z-2)/2)‖ ≤ Real.exp (Real.pi*V) := by
    apply (cos_norm _).trans
    apply Real.exp_le_exp.mpr
    have hzI : |z.im| ≤ 2*|s.im|+1/8 := by
      have hh := abs_add_le (2*s.im) sigma.im
      norm_num [abs_mul] at hh
      dsimp [z]; simp; linarith
    have he : (((Real.pi:ℂ)*(z-2)/2)).im = Real.pi*z.im/2 := by simp
    rw [he,abs_div,abs_mul,abs_of_pos Real.pi_pos]
    dsimp [V]; norm_num; nlinarith [Real.pi_pos]
  have hscale : ‖(X:ℂ)^(-s)‖ ≤ Real.exp (2*|Real.log X|) :=
    PRZZDifferenceDecay.power_bound X hX (-s) (by simpa using (abs_le.mpr
      (show -2 ≤ s.re ∧ s.re ≤ 2 by constructor <;> linarith)))
  have hsn : ‖s‖ ≤ 2*V := by
    have hh := norm_le_abs_re_add_abs_im s
    have hsabs : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
    dsimp [V]; linarith
  have han : ‖annihilator sigma s‖ ≤ (1+16/‖sigma‖^2)*V^2 := by
    have hh := annihilator_bound sigma s 1 ‖sigma‖ zero_lt_one (norm_pos_iff.mpr hs) (by simp)
    simp only [div_pow,one_pow,mul_one_div] at hh
    apply hh.trans
    calc
      _ ≤ 1+4*(2*V)^2/‖sigma‖^2 := by gcongr
      _ = 1+(16/‖sigma‖^2)*V^2 := by ring
      _ ≤ _ := by
        have hp : 1 ≤ V^2 := by nlinarith
        nlinarith
  have hinv : 1 ≤ ‖s‖ := him.trans (abs_im_le_norm s)
  have he : ‖exp (s^2)‖ ≤ Real.exp 4*Real.exp (-s.im^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,mul_re]
    nlinarith
  have hpow : 1 ≤ ‖((2*Real.pi:ℝ):ℂ)^z‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith [hzr.1])
  have hf := congrArg norm (reflection_factor sigma X s (by change 0 < z.re; linarith [hzr.1]) hz1)
  have hb : ‖kernel sigma X s‖ ≤
      (Real.exp (2*|Real.log X|)*(Real.exp 4*Real.exp (-s.im^2))*
        ((1+16/‖sigma‖^2)*V^2))*(2*(50*V)*G*Real.exp (Real.pi*V)) := by
    apply (le_mul_of_one_le_right (norm_nonneg _) hpow).trans
    rw [← norm_mul,hf]
    simp only [norm_mul,norm_div,Complex.norm_ofNat]
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact (div_le_self (by positivity) hinv).trans (by gcongr)
    · gcongr
  have hex : Real.exp (-s.im^2)*Real.exp (Real.pi*V) ≤
      Real.exp (Real.pi+Real.pi^2/2)*Real.exp (-s.im^2/2) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [V]
    nlinarith [sq_nonneg (|s.im|-Real.pi),sq_abs s.im]
  apply hb.trans
  let A := Real.exp (2*|Real.log X|)*(1+16/‖sigma‖^2)*(2*G*50)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ = A*V^3*Real.exp 4*(Real.exp (-s.im^2)*Real.exp (Real.pi*V)) := by dsimp [A]; ring
    _ ≤ A*V^3*Real.exp 4*(Real.exp (Real.pi+Real.pi^2/2)*Real.exp (-s.im^2/2)) :=
      mul_le_mul_of_nonneg_left hex (by positivity)
    _ = C*V^3*Real.exp (-s.im^2/2) := by
      dsimp [A,C]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (by norm_num : 3 ≤ 4))
          (show 0 ≤ C by dsimp [C]; positivity)) (by positivity)

#print axioms analytic
#print axioms reflection_factor
#print axioms cos_norm
#print axioms gamma_cap
#print axioms tail_bound
end XiPrime8845.PRZZReflectedEnvelope
