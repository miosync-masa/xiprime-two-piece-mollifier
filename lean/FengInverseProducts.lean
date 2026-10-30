import FengOutsidePartner

/-! Abel limits for inverse/inverse and signed main/inverse profiles.
These concern the explicit arithmetic profile sums. Identification of the
remaining actual proxies with these sums is not assumed here. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.FengInverseProducts
open BetaKernel FengInverseProfile WeightDerivatives LogProfileSum
set_option maxHeartbeats 1000000

def doubleProfile (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  D (-1) A θ u P * D (-1) B θ u G

def doubleDeriv (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  (P.eval ((u/θ:ℝ):ℂ)-A*D (-1) A θ u P)*D (-1) B θ u G+
    D (-1) A θ u P*(G.eval ((u/θ:ℝ):ℂ)-B*D (-1) B θ u G)

theorem double_hasDerivAt (θ u : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    HasDerivAt (doubleProfile θ P G A B) (doubleDeriv θ P G A B u) u :=
  (inverse_hasDerivAt A θ u P).mul (inverse_hasDerivAt B θ u G)

theorem doubleDeriv_continuous (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    Continuous (doubleDeriv θ P G A B) := by
  unfold doubleDeriv
  have hp := inverse_continuous A θ P
  have hg := inverse_continuous B θ G
  fun_prop

def doubleValueCap (P G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  inverseCap P θ C U*inverseCap G θ C U

def inverseDerivCap (P : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  polyCap P (U/θ)+C*inverseCap P θ C U

def doubleDerivCap (P G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  inverseDerivCap P θ C U*inverseCap G θ C U+
    inverseCap P θ C U*inverseDerivCap G θ C U

theorem inverse_deriv_bound (P : Polynomial ℂ) (A : ℂ) (θ C U u : ℝ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖P.eval ((u/θ:ℝ):ℂ)-A*D (-1) A θ u P‖ ≤ inverseDerivCap P θ C U := by
  have hp : ‖P.eval ((u/θ:ℝ):ℂ)‖ ≤ polyCap P (U/θ) := by
    apply eval_bound
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hu.1 hθ.le)]
    exact div_le_div_of_nonneg_right hu.2 hθ.le
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add hp (mul_le_mul hA (inverse_bound P A θ C U u hθ hA hu)
    (norm_nonneg _) ((norm_nonneg A).trans hA))

theorem double_bound (θ C U u : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖doubleProfile θ P G A B u‖ ≤ doubleValueCap P G θ C U := by
  rw [doubleProfile,norm_mul]
  exact mul_le_mul (inverse_bound P A θ C U u hθ hA hu)
    (inverse_bound G B θ C U u hθ hB hu) (norm_nonneg _)
    (inverseCap_nonneg P θ C U hθ (hu.1.trans hu.2))

theorem doubleDeriv_bound (θ C U u : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖doubleDeriv θ P G A B u‖ ≤ doubleDerivCap P G θ C U := by
  have hp := inverse_deriv_bound P A θ C U u hθ hA hu
  have hg := inverse_deriv_bound G B θ C U u hθ hB hu
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  exact add_le_add
    (mul_le_mul hp (inverse_bound G B θ C U u hθ hB hu) (norm_nonneg _) ((norm_nonneg _).trans hp))
    (mul_le_mul (inverse_bound P A θ C U u hθ hA hu) hg (norm_nonneg _)
      (inverseCap_nonneg P θ C U hθ (hu.1.trans hu.2)))

theorem double_integral_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, doubleProfile θ P G A B u) =
      monomialIntegral A B θ P G (-1) (-1) 1 := by
  have h := intervalIntegral.integral_comp_sub_left (doubleProfile θ P G A B) θ (a:=0) (b:=θ)
  simp only [sub_self,sub_zero] at h
  rw [← h]
  simp only [monomialIntegral,Nat.sub_self,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
  rfl

theorem double_zero_uniform (P G : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (hU : 0 ≤ U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => zeroSum L U (doubleProfile θ P G p.1 p.2))
      (fun p => ∫ u in 0..U, doubleProfile θ P G p.1 p.2 u) atTop
      {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have hlim : Tendsto (fun L : ℝ => TotientHarmonic.errorConstant*
      (doubleValueCap P G θ C U+U*doubleDerivCap P G θ C U)/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul
      (TotientHarmonic.errorConstant*(doubleValueCap P G θ C U+U*doubleDerivCap P G θ C U))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),hlim.eventually (gt_mem_nhds heps)] with L hL he
  intro p hp
  rw [dist_comm,dist_eq_norm]
  exact (zeroSum_error L U _ _ _ _ hL hU (fun u => double_hasDerivAt θ u P G p.1 p.2)
    (doubleDeriv_continuous θ P G p.1 p.2)
    (double_bound θ C U 0 P G p.1 p.2 hθ hp.1 hp.2 ⟨le_rfl,hU⟩)
    (fun u hu => doubleDeriv_bound θ C U u P G p.1 p.2 hθ hp.1 hp.2 hu)).trans_lt he

theorem double_profile_twoBidiscs (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => zeroSum L PRZZAsymptotic.theta
        (doubleProfile PRZZAsymptotic.theta P G p.1 p.2))
      (fun p => monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) (-1) 1)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  simpa only [double_integral_kernel] using
    (double_zero_uniform P G PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4) PRZZAsymptotic.theta
      hθ hθ.le).mono (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

/-- The signed marked arithmetic measure applied to D1 times D(-1). -/
theorem mixed_inverse_uniform (P G : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => FengMixedAbel.profileSum L U (profile θ P G p.1 p.2))
      (fun p => ∫ u in 0..U, (3*(-1/6:ℝ)*(U-u)^2:ℝ)*profile θ P G p.1 p.2 u)
      atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have hM : 0 ≤ valueCap P G θ C U :=
    mul_nonneg (firstCap_nonneg P θ C U hθ hC hU) (inverseCap_nonneg G θ C U hθ hU)
  have hD : 0 ≤ derivativeCap P G θ C U := by
    unfold derivativeCap
    have h1 := firstCap_nonneg P θ C U hθ hC hU
    have h2 := firstCap_nonneg P.derivative θ C U hθ hC hU
    have h3 := inverseCap_nonneg G θ C U hθ hU
    have h4 := polyCap_nonneg G (U/θ) (div_nonneg hU hθ.le)
    positivity
  exact FengMixedLimit.profile_family_uniform _ _ _ U (valueCap P G θ C U)
    (derivativeCap P G θ C U) hU hM hD
    (fun p _ u => profile_hasDerivAt θ u P G p.1 p.2)
    (fun p _ => profileDeriv_continuous θ P G p.1 p.2)
    (fun p hp => profile_bound θ C U 0 P G p.1 p.2 hθ hp.1 hp.2 ⟨le_rfl,hU⟩)
    (fun p hp u hu => profileDeriv_bound θ C U u P G p.1 p.2 hθ hp.1 hp.2 hu)

theorem mixed_inverse_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, (3*(-1/6:ℝ)*(θ-u)^2:ℝ)*profile θ P G A B u) =
      -monomialIntegral A B θ P G 1 (-1) 3 := by
  have he : (fun v : ℝ => (3*(-1/6:ℝ)*(θ-(θ-v))^2:ℝ)*profile θ P G A B (θ-v)) =
      (fun v : ℝ => (-1:ℂ)*((v:ℂ)^2/(2:ℂ)*D 1 A θ (θ-v) P*D (-1) B θ (θ-v) G)) := by
    funext v
    simp only [profile,ShiftedMobius.mainTerm,D,↓reduceIte]
    push_cast
    ring
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (3*(-1/6:ℝ)*(θ-u)^2:ℝ)*profile θ P G A B u) θ (a:=0) (b:=θ)
  simp only [sub_self,sub_zero] at h
  rw [← h,he,intervalIntegral.integral_const_mul]
  norm_num [monomialIntegral,Nat.factorial]

theorem mixed_inverse_twoBidiscs (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => FengMixedAbel.profileSum L PRZZAsymptotic.theta
        (profile PRZZAsymptotic.theta P G p.1 p.2))
      (fun p => -monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 (-1) 3)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hC : 0 ≤ 5*PRZZAsymptotic.R/4 := by have := PRZZAsymptotic.radius_pos; positivity
  simpa only [mixed_inverse_kernel] using
    (mixed_inverse_uniform P G PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4) PRZZAsymptotic.theta
      hθ hC hθ.le).mono (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

#print axioms double_hasDerivAt
#print axioms doubleDeriv_continuous
#print axioms inverse_deriv_bound
#print axioms double_bound
#print axioms doubleDeriv_bound
#print axioms double_integral_kernel
#print axioms double_zero_uniform
#print axioms double_profile_twoBidiscs
#print axioms mixed_inverse_uniform
#print axioms mixed_inverse_kernel
#print axioms mixed_inverse_twoBidiscs

/-- Transposed signed profile, with both the profile and shift exchanged. -/
theorem inverse_mixed_twoBidiscs (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => FengMixedAbel.profileSum L PRZZAsymptotic.theta
        (profile PRZZAsymptotic.theta G P p.2 p.1))
      (fun p => -monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  have h := mixed_inverse_twoBidiscs G P
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  have hs : (p.2,p.1) ∈ ElementaryGcd.twoBidiscs := by
    rcases hp with hp | hp
    · exact Or.inl ⟨hp.2,hp.1⟩
    · apply Or.inr
      rw [ElementaryGcd.reflectedBidisc_center] at hp ⊢
      exact ⟨hp.2,hp.1⟩
  simpa only [monomialIntegral_swap _ _ _ G P] using hL (p.2,p.1) hs

#print axioms inverse_mixed_twoBidiscs

end XiPrime8845.FengInverseProducts

