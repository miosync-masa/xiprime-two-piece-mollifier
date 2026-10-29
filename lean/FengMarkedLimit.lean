import FengMarkedAbel
import OuterProfile

/-! From one scalar marked summatory asymptotic to uniform profile integrals.
The scalar premise is NOT discharged here. It involves the actual arithmetic
weight, including non-squarefree integers, and is not a PRZZ axiom. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.FengMarkedLimit
open FengMarkedAbel FengMarkedProfile LogProfileSum
set_option maxHeartbeats 1000000

def cumulative (L v : ℝ) : ℝ := summatory (Real.exp (L*v))/L^5

theorem summatory_nonneg (x : ℝ) : 0 ≤ summatory x :=
  sum_nonneg (fun n _ => weight_nonneg n)

theorem summatory_mono : Monotone summatory := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy))
  exact fun n _ _ => weight_nonneg n

theorem cumulative_nonneg (L v : ℝ) (hL : 0 ≤ L) : 0 ≤ cumulative L v :=
  div_nonneg (summatory_nonneg _) (pow_nonneg hL _)

/-- Uniform mass control is unconditional. It does not supply the constant
7/120 required by the subsequent scalar asymptotic. -/
theorem cumulative_bound (L U : ℝ) (hL : 0 < L) (hU : 0 ≤ U) :
    cumulative L U ≤ U^4*(SupportTail.harmonic (CoprimeEndpoint.cutoff L U)/L)*
      (1+2*SupportProductTail.productConstant) := by
  have hsum : summatory (Real.exp (L*U)) ≤ (L*U)^4*
      ∑ g ∈ Ioc 0 (CoprimeEndpoint.cutoff L U), (1/(g:ℝ))*SupportTail.eulerMass g 0^2 := by
    unfold summatory CoprimeEndpoint.cutoff
    rw [mul_sum]
    apply sum_le_sum
    intro g hg
    have hg0 : g ≠ 0 := (mem_Ioc.mp hg).1.ne'
    have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hg).1
    have hlog : Real.log g ≤ L*U := (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hg1)).mpr
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2)
    exact (weight_bound g hg0).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.log_nonneg hg1) hlog 4) (by positivity))
  have hav := mul_le_mul_of_nonneg_left
    (FengSharedInterior.euler_square_average (CoprimeEndpoint.cutoff L U))
    (pow_nonneg (mul_nonneg hL.le hU) 4)
  apply (div_le_div_of_nonneg_right (hsum.trans hav) (pow_nonneg hL.le 5)).trans_eq
  field_simp

/-- Endpoint-safe uniformity follows from scalar asymptotics and positivity;
no rate, shift-uniform premise or uniform convergence at infinity is added. -/
theorem cumulative_uniform_of_scalar (c U : ℝ) (hU : 0 ≤ U)
    (hscalar : Tendsto (fun t : ℝ => summatory (Real.exp t)/t^5) atTop (nhds c)) :
    TendstoUniformlyOn (fun L v => cumulative L v) (fun v => c*v^5)
      atTop (Set.Icc 0 U) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have heta : 0 < eps/(2*(U^5+1)) := by positivity
  obtain ⟨K₀,hK₀⟩ := Metric.tendsto_atTop.mp hscalar _ heta
  let K := max K₀ 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let B := summatory (Real.exp K)+|c| * K^5
  have hsmall : Tendsto (fun L : ℝ => B/L^5) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,inv_pow,mul_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using
      (tendsto_inv_atTop_zero.pow 5).const_mul B
  filter_upwards [eventually_gt_atTop (0:ℝ), hsmall.eventually (gt_mem_nhds heps)] with L hL hsmallL
  intro v hv
  rw [dist_comm,Real.dist_eq]
  by_cases hbig : K ≤ L*v
  · have ht0 : 0 < L*v := hK.trans_le hbig
    have hv0 : v ≠ 0 := by intro hv0; simp [hv0] at ht0
    have hh := hK₀ (L*v) ((le_max_left _ _).trans hbig)
    rw [Real.dist_eq] at hh
    have he : cumulative L v-c*v^5 = (summatory (Real.exp (L*v))/(L*v)^5-c)*v^5 := by
      unfold cumulative
      field_simp [hL.ne',hv0]
    rw [he,abs_mul,abs_of_nonneg (pow_nonneg hv.1 5)]
    have hpow := pow_le_pow_left₀ hv.1 hv.2 5
    have hh' := mul_le_mul (le_of_lt hh) hpow (pow_nonneg hv.1 5) heta.le
    apply hh'.trans_lt
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0<2*(U^5+1))).mpr
    nlinarith [pow_nonneg hU 5]
  · have ht : L*v ≤ K := (lt_of_not_ge hbig).le
    have hs := summatory_mono (Real.exp_le_exp.mpr ht)
    have hp := pow_le_pow_left₀ (mul_nonneg hL.le hv.1) ht 5
    rw [mul_pow] at hp
    have hbound : |cumulative L v-c*v^5| ≤ B/L^5 := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (cumulative_nonneg L v hL.le),abs_mul,
        abs_of_nonneg (pow_nonneg hv.1 5)]
      apply (le_div_iff₀ (pow_pos hL 5)).mpr
      dsimp only [cumulative,B]
      have hLn : L^5 ≠ 0 := (pow_pos hL 5).ne'
      rw [add_mul,div_mul_cancel₀ _ hLn]
      nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg c)]
    exact hbound.trans_lt hsmallL

theorem reference_rescale (L U c : ℝ) (hL : 0 < L) (hU : 0 ≤ U)
    (H : ℝ → ℂ) (hc : Continuous H) :
    (∫ t in 1..Real.exp (L*U), H (coordinate L U t)*(5*c*(Real.log t)^4/t:ℝ))/(L:ℂ)^5 =
      ∫ u in 0..U, (5*c*(U-u)^4:ℝ)*H u := by
  rw [← intervalIntegral.integral_div]
  have h := log_rescale L U hL hU (fun u => (5*c*(U-u)^4:ℝ)*H u) (by fun_prop)
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
    (herr : ∀ v ∈ Set.Icc 0 U, |cumulative L v-c*v^5| ≤ eps) :
    ‖markedProfileSum L U H-∫ u in 0..U, (5*c*(U-u)^4:ℝ)*H u‖ ≤ eps*(M+U*D) := by
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
  have hE : ∀ t ∈ Set.Icc 1 (Real.exp (L*U)), |summatory t-c*(Real.log t)^5| ≤ L^5*eps := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hv := ShiftWeights.normalized_log_mem t L U ht.1 hL
      ((Real.log_le_iff_le_exp ht0).mpr ht.2)
    have hh := herr (Real.log t/L) hv
    have he : summatory t-c*(Real.log t)^5 = L^5*(cumulative L (Real.log t/L)-c*(Real.log t/L)^5) := by
      unfold cumulative
      rw [mul_div_cancel₀ _ hL.ne',Real.exp_log ht0]
      field_simp
    rw [he,abs_mul,abs_of_pos (pow_pos hL 5)]
    exact mul_le_mul_of_nonneg_left hh (pow_nonneg hL.le 5)
  have hb := weighted_error_bound _ c (L^5*eps) hx F F' hder hcont hE
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
  rw [markedProfileSum_eq,← reference_rescale L U c hL hU H hH,← sub_div,
    norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL 5)).mpr
  apply hb.trans
  rw [hn,hend]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hM hint) (mul_nonneg (pow_nonneg hL.le 5) heps)
  convert hh using 1; ring

/-- The arithmetic supplier remains precisely one scalar asymptotic. -/
theorem profile_family_uniform {ι : Type*} (s : Set ι) (H H' : ι → ℝ → ℂ)
    (c U M D : ℝ) (hU : 0 ≤ U) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hscalar : Tendsto (fun t : ℝ => summatory (Real.exp t)/t^5) atTop (nhds c))
    (hd : ∀ p ∈ s, ∀ u, HasDerivAt (H p) (H' p u) u)
    (hc : ∀ p ∈ s, Continuous (H' p))
    (hval : ∀ p ∈ s, ‖H p 0‖ ≤ M)
    (hder : ∀ p ∈ s, ∀ u ∈ Set.Icc 0 U, ‖H' p u‖ ≤ D) :
    TendstoUniformlyOn (fun L p => markedProfileSum L U (H p))
      (fun p => ∫ u in 0..U, (5*c*(U-u)^4:ℝ)*H p u) atTop s := by
  have h := cumulative_uniform_of_scalar c U hU hscalar
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps/(M+U*D+1) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),Metric.tendstoUniformlyOn_iff.mp h _ he] with L hL hbound
  intro p hp
  rw [dist_comm,dist_eq_norm]
  apply (profile_error L U c _ M D (H p) (H' p) hL hU he.le (hd p hp) (hc p hp)
    (hval p hp) (hder p hp) (by
      intro v hv
      have hh := hbound v hv
      rw [dist_comm,Real.dist_eq] at hh
      exact hh.le)).trans_lt
  have hpos : 0 < M+U*D+1 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hpos).mpr
  nlinarith

/-- The exact outstanding arithmetic statement. This is a definition of a
proposition, not an axiom and not a claim that the proposition is proved. -/
def MarkedScalarAsymptotic : Prop :=
  Tendsto (fun t : ℝ => summatory (Real.exp t)/t^5) atTop (nhds (7/120))

/-- The proposed density matches the 7*E(1,1,5) component before theta^-4.
This identity alone makes no arithmetic asymptotic assertion. -/
theorem density_integral_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, (5*(7/120:ℝ)*(θ-u)^4:ℝ)*OuterProfile.profile θ P G A B u) =
      7*BetaKernel.monomialIntegral A B θ P G 1 1 5 := by
  have he : (fun v : ℝ => (5*(7/120:ℝ)*(θ-(θ-v))^4:ℝ)*OuterProfile.profile θ P G A B (θ-v)) =
      (fun v : ℝ => (7:ℂ)*((v:ℂ)^4/(24:ℂ)*BetaKernel.D 1 A θ (θ-v) P*BetaKernel.D 1 B θ (θ-v) G)) := by
    funext v
    simp only [OuterProfile.profile,ShiftedMobius.mainTerm,BetaKernel.D,↓reduceIte]
    push_cast
    ring
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (5*(7/120:ℝ)*(θ-u)^4:ℝ)*OuterProfile.profile θ P G A B u) θ (a:=0) (b:=θ)
  simp only [sub_self,sub_zero] at h
  rw [← h,he,intervalIntegral.integral_const_mul]
  norm_num [BetaKernel.monomialIntegral,Nat.factorial]

/-- Uniform on BOTH reflected bidiscs, conditional only on the scalar
marked arithmetic asymptotic named above. No PRZZ premise is used. -/
theorem marked_profile_twoBidiscs (P G : Polynomial ℂ) (hs : MarkedScalarAsymptotic) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => markedProfileSum L PRZZAsymptotic.theta
        (OuterProfile.profile PRZZAsymptotic.theta P G p.1 p.2))
      (fun p => 7*BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 5)
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
    (fun p => OuterProfile.profileDeriv θ P G p.1 p.2) (7/120) θ
    (OuterProfile.valueCap P G θ C θ) (OuterProfile.derivativeCap P G θ C θ)
    hθ.le hM hD hs
    (fun p _ u => OuterProfile.profile_hasDerivAt u θ P G p.1 p.2)
    (fun p _ => OuterProfile.profileDeriv_continuous θ P G p.1 p.2)
    (fun p hp => OuterProfile.profile_bound θ C θ 0 P G p.1 p.2 hθ
      (ShiftedMobius.twoBidiscs_norm p hp).1 (ShiftedMobius.twoBidiscs_norm p hp).2 ⟨le_rfl,hθ.le⟩)
    (fun p hp u hu => OuterProfile.profileDeriv_bound θ C θ u P G p.1 p.2 hθ
      (ShiftedMobius.twoBidiscs_norm p hp).1 (ShiftedMobius.twoBidiscs_norm p hp).2 hu)
  simpa only [density_integral_kernel] using h

#print axioms density_integral_kernel
#print axioms marked_profile_twoBidiscs
#print axioms summatory_mono
#print axioms summatory_nonneg
#print axioms cumulative_nonneg
#print axioms cumulative_bound
#print axioms cumulative_uniform_of_scalar
#print axioms reference_rescale
#print axioms profile_error
#print axioms profile_family_uniform
end XiPrime8845.FengMarkedLimit
