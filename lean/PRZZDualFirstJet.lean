import PRZZDualTimeIBP

/-! The first genuine Gamma jet. Cancellation is performed in the
logarithmic derivative before taking norms. Higher normalized Gamma jets
are not inferred from this first-order estimate or from smoothness. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZDualFirstJet
set_option maxHeartbeats 5000000

theorem digamma_difference (T : ℝ) (z d : ℂ) (hT : 2 ≤ T)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 0 < (z+(u:ℂ)*d).re)
    (hi : ∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |(z+(u:ℂ)*d).im|) :
    ‖digamma (z+d)-digamma z‖ ≤ (100+4*‖d‖)/T := by
  have hT0 : 0 < T := by linarith
  have h0 := PRZZAFEGamma.digamma_error T z hT (by simpa using hr 0 (by norm_num))
    (by simpa using hi 0 (by norm_num))
  have h1 := PRZZAFEGamma.digamma_error T (z+d) hT
    (by simpa using hr 1 (by norm_num)) (by simpa using hi 1 (by norm_num))
  have hl := PRZZGammaCentral.log_segment_bound z d (T/4) (by positivity)
    (fun u hu => mem_slitPlane_iff.mpr (Or.inl (hr u hu)))
    (fun u hu => (hi u hu).trans (abs_im_le_norm _))
  have he : digamma (z+d)-digamma z =
      (digamma (z+d)-log (z+d))+(log (z+d)-log z)-(digamma z-log z) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (((add_le_add ((norm_add_le _ _).trans (add_le_add h1 hl)) h0)).trans_eq (by ring))

theorem gamma_line_derivative (c k : ℂ) (t : ℝ) (hc : 0 < (c+(t:ℂ)*k).re) :
    HasDerivAt (fun u : ℝ => Gamma (c+(u:ℂ)*k))
      (Gamma (c+(t:ℂ)*k)*digamma (c+(t:ℂ)*k)*k) t := by
  have hg := (PRZZGammaPath.gamma_analytic _ hc).differentiableAt.hasDerivAt
  have hd : deriv Gamma (c+(t:ℂ)*k) = Gamma (c+(t:ℂ)*k)*digamma (c+(t:ℂ)*k) := by
    rw [Complex.digamma_def,logDeriv_apply]
    field_simp [Gamma_ne_zero_of_re_pos hc]
  rw [hd] at hg
  simpa only [smul_eq_mul,mul_comm,Function.comp_def,id_eq,Complex.ofReal_one,mul_one] using
    hg.scomp t ((((hasDerivAt_id t).ofReal_comp).mul_const k).const_add c)

theorem ratio_derivative (c e k : ℂ) (t : ℝ)
    (hc : 0 < (c+(t:ℂ)*k).re) (he : 0 < (e+(t:ℂ)*k).re) :
    HasDerivAt (fun u : ℝ => Gamma (c+(u:ℂ)*k)/Gamma (e+(u:ℂ)*k))
      ((Gamma (c+(t:ℂ)*k)/Gamma (e+(t:ℂ)*k))*
        (digamma (c+(t:ℂ)*k)-digamma (e+(t:ℂ)*k))*k) t := by
  convert (gamma_line_derivative c k t hc).div (gamma_line_derivative e k t he)
    (Gamma_ne_zero_of_re_pos he) using 1 <;>
    (first | rfl | (field_simp <;> ring))

theorem line_conditions (T t e : ℝ) (a d : ℂ) (hT : 2 ≤ T) (ht : T ≤ t)
    (he : |e| = 1) (ha : ‖a‖ ≤ 1/16) (hd : ‖d‖ ≤ 1/16) :
    (∀ u ∈ Icc (0:ℝ) 1, 0 < ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+(u:ℂ)*d).re) ∧
    (∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+(u:ℂ)*d).im|) := by
  have har := (abs_re_le_norm a).trans ha
  have hai := (abs_im_le_norm a).trans ha
  have hud (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : ‖(u:ℂ)*d‖ ≤ 1/16 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg d)).trans (by simpa using hd)
  constructor
  · intro u hu
    have hr := (abs_le.mp ((abs_re_le_norm ((u:ℂ)*d)).trans (hud u hu))).1
    have hre : ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+(u:ℂ)*d).re =
        (1/2+a.re)/2+((u:ℂ)*d).re := by simp
    rw [hre]
    linarith [(abs_le.mp har).1]
  · intro u hu
    have hp : |a.im/2+((u:ℂ)*d).im| ≤ 3/32 :=
      (abs_add_le _ _).trans (by
        have hh := (abs_im_le_norm ((u:ℂ)*d)).trans (hud u hu)
        rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
        linarith)
    have hx : |t*e/2| = t/2 := by
      rw [abs_div,abs_mul,he,abs_of_nonneg (by linarith : 0 ≤ t)]
      norm_num
    have hh := abs_sub (a.im/2+t*e/2+((u:ℂ)*d).im) (a.im/2+((u:ℂ)*d).im)
    rw [show a.im/2+t*e/2+((u:ℂ)*d).im-(a.im/2+((u:ℂ)*d).im) = t*e/2 by ring,hx] at hh
    have him : ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+(u:ℂ)*d).im =
        a.im/2+t*e/2+((u:ℂ)*d).im := by simp; ring
    rw [him]
    linarith

/-- First derivative of an actual vertical Gamma quotient, with a
height-independent numerical constant. -/
theorem ratio_first_bound (T t e : ℝ) (a d : ℂ) (hT : 2 ≤ T) (ht : T ≤ t)
    (he : |e| = 1) (ha : ‖a‖ ≤ 1/16) (hd : ‖d‖ ≤ 1/16) :
    ‖deriv (fun u : ℝ => Gamma ((1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2)+d)/
      Gamma ((1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2))) t‖ ≤
      ‖Gamma ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+d)/
        Gamma ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2))‖*(51/T) := by
  obtain ⟨hr,hi⟩ := line_conditions T t e a d hT ht he ha hd
  let z := (1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)
  have hc : 0 < (z+d).re := by simpa [z] using hr 1 (by norm_num)
  have hz : 0 < z.re := by simpa [z] using hr 0 (by norm_num)
  have hder := ratio_derivative ((1/2+a)/2+d) ((1/2+a)/2) ((e:ℂ)*I/2) t
    (by simpa [z,add_right_comm] using hc) hz
  have hf : (fun u : ℝ => Gamma ((1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2)+d)/
      Gamma ((1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2))) =
      (fun u : ℝ => Gamma ((1/2+a)/2+d+(u:ℂ)*((e:ℂ)*I/2))/
        Gamma ((1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2))) := by
    funext u; rw [add_right_comm _ d]
  rw [hf,hder.deriv]
  have hp := digamma_difference T z d hT hr hi
  have hk : ‖(e:ℂ)*I/2‖ = 1/2 := by simp [norm_div,norm_mul,he]
  simp only [norm_mul,hk]
  have hcost : (100+4*‖d‖)/T*(1/2) ≤ 51/T := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 1/2)
  have hh := mul_le_mul_of_nonneg_left (hb.trans hcost) (norm_nonneg (Gamma (z+d)/Gamma z))
  simpa only [z,add_right_comm,mul_assoc] using hh

def factor (a d : ℂ) (e t : ℝ) : ℂ :=
  Gamma ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)+d)/
    Gamma ((1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2))

theorem multiplier_factors (a b : ℂ) (t : ℝ) :
    PRZZAFEDual.dualMultiplier a b t =
      (Real.pi:ℂ)^(a+b)*(factor a (-(a+b)/2) 1 t*factor b (-(a+b)/2) (-1) t) := by
  rw [PRZZAFEDual.dualMultiplier_formula]
  unfold factor PRZZAFEDual.leftArg PRZZAFEDual.rightArg
  have hl : (1/2+a)/2+(t:ℂ)*((1:ℂ)*I/2)+(-(a+b)/2) = (1/2+-b+(t:ℂ)*I)/2 := by ring
  have hr : (1/2+b)/2+(t:ℂ)*((-1:ℂ)*I/2)+(-(a+b)/2) = (1/2+-a-(t:ℂ)*I)/2 := by ring
  have hl' : (1/2+a)/2+(t:ℂ)*((1:ℂ)*I/2) = (1/2+a+(t:ℂ)*I)/2 := by ring
  have hr' : (1/2+b)/2+(t:ℂ)*((-1:ℂ)*I/2) = (1/2+b-(t:ℂ)*I)/2 := by ring
  simp only [ofReal_one,ofReal_neg,hl,hr,hl',hr']
  ring

theorem multiplier_first_bound (T t : ℝ) (a b : ℂ) (hT : 2 ≤ T) (ht : T ≤ t)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) :
    ‖deriv (PRZZAFEDual.dualMultiplier a b) t‖ ≤
      ‖PRZZAFEDual.dualMultiplier a b t‖*(102/T) := by
  let d := -(a+b)/2
  have hd : ‖d‖ ≤ 1/16 := by
    dsimp [d]; rw [norm_div,norm_neg]
    norm_num only [Complex.norm_ofNat]
    have hh := norm_add_le a b
    linarith
  have hf (c : ℂ) (e : ℝ) (hc : ‖c‖ ≤ 1/16) (he : |e| = 1) :
      DifferentiableAt ℝ (factor c d e) t := by
    obtain ⟨hr,hi⟩ := line_conditions T t e c d hT ht he hc hd
    have h := ratio_derivative ((1/2+c)/2+d) ((1/2+c)/2) ((e:ℂ)*I/2) t
      (by simpa only [ofReal_one,one_mul,add_right_comm] using hr 1 (by norm_num))
      (by simpa using hr 0 (by norm_num))
    have heq : factor c d e = fun u : ℝ =>
        Gamma ((1/2+c)/2+d+(u:ℂ)*((e:ℂ)*I/2))/
          Gamma ((1/2+c)/2+(u:ℂ)*((e:ℂ)*I/2)) := by
      funext u; unfold factor; rw [add_right_comm _ d]
    rw [heq]; exact h.differentiableAt
  have hL := hf a 1 ha (by norm_num)
  have hR := hf b (-1) hb (by norm_num)
  have heq : PRZZAFEDual.dualMultiplier a b = fun u : ℝ =>
      (Real.pi:ℂ)^(a+b)*(factor a d 1 u*factor b d (-1) u) := funext (multiplier_factors a b)
  have hl := ratio_first_bound T t 1 a d hT ht (by norm_num) ha hd
  have hr := ratio_first_bound T t (-1) b d hT ht (by norm_num) hb hd
  change ‖deriv (factor a d 1) t‖ ≤ ‖factor a d 1 t‖*(51/T) at hl
  change ‖deriv (factor b d (-1)) t‖ ≤ ‖factor b d (-1) t‖*(51/T) at hr
  have hdp := ((hL.hasDerivAt.mul hR.hasDerivAt).const_mul ((Real.pi:ℂ)^(a+b))).deriv
  simp only [Pi.mul_apply] at hdp
  rw [heq,hdp,norm_mul,norm_mul,norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hh := add_le_add (mul_le_mul_of_nonneg_right hl (norm_nonneg (factor b d (-1) t)))
    (mul_le_mul_of_nonneg_left hr (norm_nonneg (factor a d 1 t)))
  simpa only [norm_mul] using hh.trans_eq (by ring)

/-- A height-independent constant for the actual first normalized jet.
This supplies order one, not an all-order Gamma-jet predicate. -/
theorem first_scaled_cap (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ t ∈ Icc T (2*T),
      T*‖deriv (PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) t‖ ≤
        102*Real.exp (2*S+7) := by
  filter_upwards [PRZZDualError.multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hcap hsmall hT
  intro A B ha hb t ht
  have hh := multiplier_first_bound T t _ _ hT ht.1 (hsmall.2 A ha) (hsmall.2 B hb)
  have hg := hcap A B ha hb t ht
  have hT0 : 0 < T := by linarith
  have hh' := mul_le_mul_of_nonneg_left hh hT0.le
  have hg' := mul_le_mul_of_nonneg_right hg (show 0 ≤ 102/T by positivity)
  have h := hh'.trans (mul_le_mul_of_nonneg_left hg' hT0.le)
  convert h using 1 <;> first | rfl | (field_simp <;> ring)

/-- Transfer a multiplier-jet cap only on the genuine time support.
Outside that support the differentiated cutoff amplitude vanishes. -/
theorem mixed_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (T k C : ℝ) (a b sigma : ℂ)
    (hT : 0 < T) (hk : 0 < k) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : sigma ≠ 0) (i j : ℕ)
    (hcap : ∀ t ∈ Icc T (2*T), ‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖ ≤ C) :
    (∫ t : ℝ, ‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖*
      ‖iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t‖) ≤
        C*(∫ t : ℝ, ‖iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t‖) := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    ((PRZZTimeAmplitude.jet_integrable F hF hsF T k sigma hT hk hs j).norm.const_mul C)
  apply Filter.Eventually.of_forall; intro t
  by_cases ht : t ∈ Icc T (2*T)
  · exact mul_le_mul_of_nonneg_right (hcap t ht) (norm_nonneg _)
  · have hz : iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t = 0 := by
      by_contra hh
      exact ht (PRZZTimeAmplitude.jet_support F hsF T k sigma hT j (subset_closure hh))
    simp only [hz,norm_zero,mul_zero,le_refl]

/-- The complete first Leibniz mass, with both constants chosen before
height, product scale and shifts. The source singularity is displayed in
the convolution; no all-order uniform Gamma bound is assumed. -/
theorem first_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (S rate : ℝ) (hS : 0 ≤ S) (hr : 0 < rate) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        ∀ (k : ℝ) (sigma : ℂ), 0 < k → sigma ≠ 0 →
        PRZZDualTimeIBP.jetMass F T k (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) sigma 1 ≤
          Real.exp (2*S+7)*
            (PRZZFullWeightJets.convolution C (fun j => D j+E j/‖sigma‖^2) 1+
              102*PRZZFullWeightJets.convolution C (fun j => D j+E j/‖sigma‖^2) 0)*
                (k/(2*T))^(-rate) := by
  obtain ⟨C,D,E,hpos,hm⟩ := PRZZTimeAmplitude.mass F hF hcF rate hr
  refine ⟨C,D,E,hpos,?_⟩
  filter_upwards [PRZZDualError.multiplier_scaled_cap S hS,first_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hzero hone hsmall hT
  intro A B hA hB k sigma hk hs
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  let V := fun n => PRZZFullWeightJets.convolution C (fun j => D j+E j/‖sigma‖^2) n
  have hT0 : 0 < T := by linarith
  have h0 := mixed_mass F hF hsF T k (Real.exp (2*S+7)) a b sigma hT0 hk
    (hsmall.2 A hA) (hsmall.2 B hB) hs 0 1 (by
      intro t ht; simpa only [iteratedDeriv_zero] using hzero A B hA hB t ht)
  have h1 := mixed_mass F hF hsF T k (102*Real.exp (2*S+7)/T) a b sigma hT0 hk
    (hsmall.2 A hA) (hsmall.2 B hB) hs 1 0 (by
      intro t ht
      have h := hone A B hA hB t ht
      simpa only [iteratedDeriv_one] using (le_div_iff₀ hT0).mpr (by simpa [mul_comm] using h))
  have hm0 := hm 0 T k sigma hT0 hk hs
  have hm1 := hm 1 T k sigma hT0 hk hs
  rw [← PRZZTimeAmplitude.mass_window F hsF T k sigma hT0 0] at hm0
  rw [← PRZZTimeAmplitude.mass_window F hsF T k sigma hT0 1] at hm1
  have hm0' : (∫ t : ℝ, ‖iteratedDeriv 0 (PRZZTimeAmplitude.amplitude F T k sigma) t‖) ≤
      V 0*(k/(2*T))^(-rate)*T := by simpa [V] using hm0
  have hm1' : (∫ t : ℝ, ‖iteratedDeriv 1 (PRZZTimeAmplitude.amplitude F T k sigma) t‖) ≤
      V 1*(k/(2*T))^(-rate) := by simpa [V,hT0.ne'] using hm1
  have hh := add_le_add
    (h0.trans (mul_le_mul_of_nonneg_left hm1' (Real.exp_pos _).le))
    (h1.trans (mul_le_mul_of_nonneg_left hm0' (by positivity)))
  have he : Real.exp (2*S+7)*(V 1*(k/(2*T))^(-rate))+
      102*Real.exp (2*S+7)/T*(V 0*(k/(2*T))^(-rate)*T) =
      Real.exp (2*S+7)*(V 1+102*V 0)*(k/(2*T))^(-rate) := by
    field_simp
    <;> ring
  simpa only [PRZZDualTimeIBP.jetMass,Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.choose_zero_right,Nat.choose_self,Nat.sub_zero,Nat.sub_self,Nat.cast_one,
    one_mul,zero_add,V] using hh.trans_eq he

#print axioms mixed_mass
#print axioms first_mass
#print axioms multiplier_factors
#print axioms multiplier_first_bound
#print axioms first_scaled_cap
#print axioms line_conditions
#print axioms ratio_first_bound
#print axioms digamma_difference
#print axioms gamma_line_derivative
#print axioms ratio_derivative
end XiPrime8845.PRZZDualFirstJet
