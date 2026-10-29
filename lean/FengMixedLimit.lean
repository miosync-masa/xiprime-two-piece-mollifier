import FengMixedAbel

/-! Endpoint-safe Abel transfer for the signed mixed arithmetic moment.
The scalar supplier is proved, and the two reflected bidiscs are both covered.
This is a weighted main-term profile, not yet the actual Conrey/Feng product. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.FengMixedLimit
open FengMixedMoment FengMixedAbel LogProfileSum
set_option maxHeartbeats 1000000

/-- The scalar error is one power below the cubic main term. -/
theorem summatory_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
    |summatory (Real.exp X)+X^3/6| ≤ C*(1+X)^2 := by
  obtain ⟨A,hA⟩ := primeSum_error_polynomial
  obtain ⟨B,hB,h⟩ := FengMertensModels.smooth_error 2 (by norm_num)
  norm_num at h
  refine ⟨max A 0+B,add_nonneg (le_max_right _ _) hB,fun X hX => ?_⟩
  have ha := (hA X hX).trans (mul_le_mul_of_nonneg_right (le_max_left A 0) (sq_nonneg _))
  have hb := h X hX
  have he : summatory (Real.exp X)+X^3/6 =
      -((primeSum ⌊Real.exp X⌋₊-FengMertensModels.smooth 2 X)+
        (FengMertensModels.smooth 2 X-X^3/6)) := by
    rw [summatory_reindex]
    ring
  rw [he,abs_neg]
  exact (abs_add_le _ _).trans (by nlinarith)

def cumulative (L v : ℝ) : ℝ := summatory (Real.exp (L*v))/L^3

/-- A common bound on the entire closed cutoff interval, including v=0. -/
theorem cumulative_error_bound (C L U : ℝ) (hC : 0 ≤ C) (hL : 0 < L)
    (h : ∀ X : ℝ, 0 ≤ X → |summatory (Real.exp X)+X^3/6| ≤ C*(1+X)^2)
    (v : ℝ) (hv : v ∈ Set.Icc 0 U) :
    |cumulative L v-(-1/6:ℝ)*v^3| ≤ C*(1+L*U)^2/L^3 := by
  have he : cumulative L v-(-1/6:ℝ)*v^3 =
      (summatory (Real.exp (L*v))+(L*v)^3/6)/L^3 := by
    unfold cumulative
    field_simp
    ring
  rw [he,abs_div,abs_of_pos (pow_pos hL 3)]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hL.le 3)
  apply (h (L*v) (mul_nonneg hL.le hv.1)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact pow_le_pow_left₀ (add_nonneg zero_le_one (mul_nonneg hL.le hv.1))
    (by nlinarith [hv.2]) 2

theorem cumulative_uniform (U : ℝ) (hU : 0 ≤ U) :
    TendstoUniformlyOn (fun L v => cumulative L v) (fun v => (-1/6:ℝ)*v^3)
      atTop (Set.Icc 0 U) := by
  obtain ⟨C,hC,h⟩ := summatory_error
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hb : Tendsto (fun L : ℝ => C*(1+L*U)^2/L^3) atTop (nhds 0) := by
    have hh := (((hi.add_const U).pow 2).const_mul C).mul hi
    simp only [zero_add,mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    field_simp
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),
    hb.eventually (gt_mem_nhds heps)] with L hL hsmall
  intro v hv
  rw [dist_comm,Real.dist_eq]
  exact (cumulative_error_bound C L U hC hL h v hv).trans_lt hsmall

theorem reference_rescale (L U c : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (H : ℝ → ℂ) (hc : Continuous H) :
    (∫ t in 1..Real.exp (L*U), H (coordinate L U t)*(3*c*(Real.log t)^2/t:ℝ))/(L:ℂ)^3 =
      ∫ u in 0..U, (3*c*(U-u)^2:ℝ)*H u := by
  rw [← intervalIntegral.integral_div]
  have h := log_rescale L U hL hU (fun u => (3*c*(U-u)^2:ℝ)*H u) (by fun_prop)
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [coordinate]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_sub]
  ring

/-- Quantitative transfer: the right side has no shift parameter. -/
theorem profile_error (L U c eps M D : ℝ) (H H' : ℝ → ℂ)
    (hL : 0 < L) (hU : 0 ≤ U) (heps : 0 ≤ eps)
    (hd : ∀ u, HasDerivAt H (H' u) u) (hc : Continuous H')
    (hM : ‖H 0‖ ≤ M) (hD : ∀ u ∈ Set.Icc 0 U, ‖H' u‖ ≤ D)
    (herr : ∀ v ∈ Set.Icc 0 U, |cumulative L v-c*v^3| ≤ eps) :
    ‖profileSum L U H-∫ u in 0..U, (3*c*(U-u)^2:ℝ)*H u‖ ≤ eps*(M+U*D) := by
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le hU)
  have hH : Continuous H := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  let F := fun t => H (coordinate L U t)
  let F' := fun t => (-(t⁻¹/L):ℝ) • H' (coordinate L U t)
  have hder : ∀ t ∈ Set.Icc 1 (Real.exp (L*U)), HasDerivAt F (F' t) t := by
    intro t ht
    exact (hd _).scomp t (((Real.hasDerivAt_log (by linarith [ht.1])).div_const L).const_sub U)
  have hcoord : ContinuousOn (coordinate L U) (Set.Icc 1 (Real.exp (L*U))) :=
    continuousOn_const.sub ((continuousOn_id.log (fun t ht =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).div_const L)
  have hcont : ContinuousOn F' (Set.Icc 1 (Real.exp (L*U))) :=
    (((continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).div_const L).neg).smul
      (hc.comp_continuousOn hcoord)
  have hE : ∀ t ∈ Set.Icc 1 (Real.exp (L*U)), |summatory t-c*(Real.log t)^3| ≤ L^3*eps := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hv := ShiftWeights.normalized_log_mem t L U ht.1 hL
      ((Real.log_le_iff_le_exp ht0).mpr ht.2)
    have hh := herr (Real.log t/L) hv
    have he : summatory t-c*(Real.log t)^3 = L^3*(cumulative L (Real.log t/L)-c*(Real.log t/L)^3) := by
      unfold cumulative
      rw [mul_div_cancel₀ _ hL.ne',Real.exp_log ht0]
      field_simp
    rw [he,abs_mul,abs_of_pos (pow_pos hL 3)]
    exact mul_le_mul_of_nonneg_left hh (pow_nonneg hL.le 3)
  have hb := weighted_error_bound _ c (L^3*eps) hx F F' hder hcont hE
  have hn : (∫ t in 1..Real.exp (L*U), ‖F' t‖) = ∫ u in 0..U, ‖H' u‖ := by
    rw [← log_rescale L U hL hU (fun u => ‖H' u‖) hc.norm]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 ≤ t := (by norm_num : (0:ℝ)≤1).trans ht.1
    simp only [F',norm_smul,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (div_nonneg (inv_nonneg.mpr ht0) hL.le),smul_eq_mul]
  have hint : (∫ u in 0..U, ‖H' u‖) ≤ U*D := by
    calc
      _ ≤ ∫ u in 0..U, D := intervalIntegral.integral_mono_on hU
        (hc.norm.intervalIntegrable _ _) intervalIntegrable_const hD
      _ = _ := by simp
  have hend : F (Real.exp (L*U)) = H 0 := by simp [F,coordinate,Real.log_exp,hL.ne']
  rw [profileSum,← reference_rescale L U c hL hU H hH,← sub_div,
    norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL 3)).mpr
  apply hb.trans
  rw [hn,hend]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hM hint) (mul_nonneg (pow_nonneg hL.le 3) heps)
  convert hh using 1; ring

theorem profile_family_uniform {ι : Type*} (s : Set ι) (H H' : ι → ℝ → ℂ)
    (U M D : ℝ) (hU : 0 ≤ U) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hd : ∀ p ∈ s, ∀ u, HasDerivAt (H p) (H' p u) u)
    (hc : ∀ p ∈ s, Continuous (H' p))
    (hval : ∀ p ∈ s, ‖H p 0‖ ≤ M)
    (hder : ∀ p ∈ s, ∀ u ∈ Set.Icc 0 U, ‖H' p u‖ ≤ D) :
    TendstoUniformlyOn (fun L p => profileSum L U (H p))
      (fun p => ∫ u in 0..U, (3*(-1/6:ℝ)*(U-u)^2:ℝ)*H p u) atTop s := by
  have h := cumulative_uniform U hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps/(M+U*D+1) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),Metric.tendstoUniformlyOn_iff.mp h _ he] with L hL hbound
  intro p hp
  rw [dist_comm,dist_eq_norm]
  apply (profile_error L U (-1/6) _ M D (H p) (H' p) hL hU he.le (hd p hp) (hc p hp)
    (hval p hp) (hder p hp) (by
      intro v hv
      have hh := hbound v hv
      rw [dist_comm,Real.dist_eq] at hh
      exact hh.le)).trans_lt
  have hpos : 0 < M+U*D+1 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hpos).mpr
  nlinarith

theorem density_integral_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, (3*(-1/6:ℝ)*(θ-u)^2:ℝ)*OuterProfile.profile θ P G A B u) =
      -BetaKernel.monomialIntegral A B θ P G 1 1 3 := by
  have he : (fun v : ℝ => (3*(-1/6:ℝ)*(θ-(θ-v))^2:ℝ)*OuterProfile.profile θ P G A B (θ-v)) =
      (fun v : ℝ => (-1:ℂ)*((v:ℂ)^2/(2:ℂ)*BetaKernel.D 1 A θ (θ-v) P*BetaKernel.D 1 B θ (θ-v) G)) := by
    funext v
    simp only [OuterProfile.profile,ShiftedMobius.mainTerm,BetaKernel.D,↓reduceIte]
    push_cast
    ring
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (3*(-1/6:ℝ)*(θ-u)^2:ℝ)*OuterProfile.profile θ P G A B u) θ (a:=0) (b:=θ)
  simp only [sub_self,sub_zero] at h
  rw [← h,he,intervalIntegral.integral_const_mul]
  norm_num [BetaKernel.monomialIntegral,Nat.factorial]

theorem mixed_profile_twoBidiscs (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => profileSum L PRZZAsymptotic.theta
        (OuterProfile.profile PRZZAsymptotic.theta P G p.1 p.2))
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  let θ := PRZZAsymptotic.theta
  let C := 5*PRZZAsymptotic.R/4
  have hθ : 0 < θ := by norm_num [θ,PRZZAsymptotic.theta]
  have hC : 0 ≤ C := by dsimp [C]; have := PRZZAsymptotic.radius_pos; positivity
  have hcap (F : Polynomial ℂ) : 0 ≤ WeightDerivatives.firstCap F θ C θ :=
    WeightDerivatives.firstCap_nonneg F θ C θ hθ hC hθ.le
  have hM : 0 ≤ OuterProfile.valueCap P G θ C θ := mul_nonneg (hcap P) (hcap G)
  have hD : 0 ≤ OuterProfile.derivativeCap P G θ C θ := by
    unfold OuterProfile.derivativeCap
    exact add_nonneg (mul_nonneg (div_nonneg (hcap P.derivative) hθ.le) (hcap G))
      (mul_nonneg (hcap P) (div_nonneg (hcap G.derivative) hθ.le))
  have h := profile_family_uniform ElementaryGcd.twoBidiscs
    (fun p => OuterProfile.profile θ P G p.1 p.2)
    (fun p => OuterProfile.profileDeriv θ P G p.1 p.2) θ
    (OuterProfile.valueCap P G θ C θ) (OuterProfile.derivativeCap P G θ C θ)
    hθ.le hM hD
    (fun p _ u => OuterProfile.profile_hasDerivAt u θ P G p.1 p.2)
    (fun p _ => OuterProfile.profileDeriv_continuous θ P G p.1 p.2)
    (fun p hp => OuterProfile.profile_bound θ C θ 0 P G p.1 p.2 hθ
      (ShiftedMobius.twoBidiscs_norm p hp).1 (ShiftedMobius.twoBidiscs_norm p hp).2 ⟨le_rfl,hθ.le⟩)
    (fun p hp u hu => OuterProfile.profileDeriv_bound θ C θ u P G p.1 p.2 hθ
      (ShiftedMobius.twoBidiscs_norm p hp).1 (ShiftedMobius.twoBidiscs_norm p hp).2 hu)
  simpa only [density_integral_kernel] using h


/-- Swapped reflected shifts, obtained by restricting the union theorem. -/
theorem mixed_profile_reflected (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => profileSum L PRZZAsymptotic.theta
        (OuterProfile.profile PRZZAsymptotic.theta P G (-p.2) (-p.1)))
      (fun p => -BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 1 3)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (mixed_profile_twoBidiscs P G)

#print axioms summatory_error
#print axioms cumulative_error_bound
#print axioms cumulative_uniform
#print axioms reference_rescale
#print axioms profile_error
#print axioms profile_family_uniform
#print axioms density_integral_kernel
#print axioms mixed_profile_twoBidiscs
#print axioms mixed_profile_reflected
end XiPrime8845.FengMixedLimit
