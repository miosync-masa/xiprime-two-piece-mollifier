import FengOutsidePrime
import OuterProfile

/-! Regularity and Abel transfer for the concrete D1/D(-1) profile.
No arithmetic replacement is assumed in these analytic statements. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.FengInverseProfile
open BetaKernel WeightDerivatives ShiftWeights ShiftedMobius LogProfileSum
set_option maxHeartbeats 1000000

theorem inverse_primitive (B : ℂ) (θ u : ℝ) (G : Polynomial ℂ) :
    D (-1) B θ u G = Complex.exp (-B*u) *
      ∫ v in 0..u, Complex.exp (B*v)*G.eval ((v/θ:ℝ):ℂ) := by
  simp only [D,↓reduceIte]
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_left
    (fun v : ℝ => Complex.exp (-B*v)*G.eval (((u-v)/θ:ℝ):ℂ)) u (a:=0) (b:=u)
  simp only [sub_self,sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [sub_sub_cancel,← mul_assoc,← Complex.exp_add]
  push_cast
  congr 2
  ring

theorem inverse_hasDerivAt (B : ℂ) (θ u : ℝ) (G : Polynomial ℂ) :
    HasDerivAt (fun u => D (-1) B θ u G)
      (G.eval ((u/θ:ℝ):ℂ)-B*D (-1) B θ u G) u := by
  let f := fun v : ℝ => Complex.exp (B*v)*G.eval ((v/θ:ℝ):ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    (hc.stronglyMeasurableAtFilter volume (nhds u)) hc.continuousAt
  have he : HasDerivAt (fun v : ℝ => Complex.exp (-B*v))
      (-B*Complex.exp (-B*u)) u := by
    simpa only [id_eq,mul_one,mul_comm] using (((hasDerivAt_id (u:ℂ)).const_mul (-B)).cexp).comp_ofReal
  simp_rw [inverse_primitive]
  convert! he.mul hi using 1
  dsimp [f]
  rw [← mul_assoc (Complex.exp _) (Complex.exp _),← Complex.exp_add]
  simp only [neg_mul,neg_add_cancel,Complex.exp_zero,one_mul]
  ring

theorem inverse_continuous (B : ℂ) (θ : ℝ) (G : Polynomial ℂ) :
    Continuous (fun u => D (-1) B θ u G) :=
  continuous_iff_continuousAt.mpr (fun u => (inverse_hasDerivAt B θ u G).continuousAt)

def inverseCap (G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  U*(Real.exp (C*U)*polyCap G (U/θ))

theorem inverseCap_nonneg (G : Polynomial ℂ) (θ C U : ℝ) (hθ : 0 < θ) (hU : 0 ≤ U) :
    0 ≤ inverseCap G θ C U :=
  mul_nonneg hU (mul_nonneg (Real.exp_pos _).le (polyCap_nonneg _ _ (div_nonneg hU hθ.le)))

theorem inverse_bound (G : Polynomial ℂ) (B : ℂ) (θ C U u : ℝ)
    (hθ : 0 < θ) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖D (-1) B θ u G‖ ≤ inverseCap G θ C U := by
  change ‖∫ t in 0..u, weight B u θ G t‖ ≤ _
  apply (intervalIntegral.norm_integral_le_integral_norm hu.1).trans
  calc
    _ ≤ ∫ t in 0..u, Real.exp (C*U)*polyCap G (U/θ) :=
      intervalIntegral.integral_mono_on hu.1 ((weight_smooth B u θ G).continuous.norm.intervalIntegrable _ _)
        intervalIntegrable_const (fun t ht => weight_interval_bound B u θ t C U G hθ hB hu.2 ht)
    _ ≤ inverseCap G θ C U := by
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,inverseCap]
      exact mul_le_mul_of_nonneg_right hu.2
        (mul_nonneg (Real.exp_pos _).le (polyCap_nonneg _ _ (div_nonneg (hu.1.trans hu.2) hθ.le)))

def profile (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  mainTerm u θ P A * D (-1) B θ u G

def profileDeriv (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  (mainTerm u θ P.derivative A/θ)*D (-1) B θ u G+
    mainTerm u θ P A*(G.eval ((u/θ:ℝ):ℂ)-B*D (-1) B θ u G)

theorem profile_hasDerivAt (θ u : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    HasDerivAt (profile θ P G A B) (profileDeriv θ P G A B u) u :=
  (OuterProfile.mainTerm_hasDerivAt u θ P A).mul (inverse_hasDerivAt B θ u G)

theorem profileDeriv_continuous (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    Continuous (profileDeriv θ P G A B) := by
  unfold profileDeriv
  have hc := inverse_continuous B θ G
  unfold mainTerm
  fun_prop

def valueCap (P G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  firstCap P θ C U*inverseCap G θ C U

def derivativeCap (P G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  (firstCap P.derivative θ C U/θ)*inverseCap G θ C U+
    firstCap P θ C U*(polyCap G (U/θ)+C*inverseCap G θ C U)

theorem profile_bound (θ C U u : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖profile θ P G A B u‖ ≤ valueCap P G θ C U := by
  rw [profile,norm_mul]
  exact mul_le_mul (ShiftedEndpoint.mainTerm_bound P A u θ C U hθ hA hu)
    (inverse_bound G B θ C U u hθ hB hu) (norm_nonneg _)
    (firstCap_nonneg _ _ _ _ hθ ((norm_nonneg A).trans hA) (hu.1.trans hu.2))

theorem profileDeriv_bound (θ C U u : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖profileDeriv θ P G A B u‖ ≤ derivativeCap P G θ C U := by
  have hC := (norm_nonneg A).trans hA
  have hU := hu.1.trans hu.2
  have hi := inverse_bound G B θ C U u hθ hB hu
  have hp : ‖G.eval ((u/θ:ℝ):ℂ)‖ ≤ polyCap G (U/θ) := by
    apply eval_bound
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hu.1 hθ.le)]
    exact div_le_div_of_nonneg_right hu.2 hθ.le
  have hd : ‖G.eval ((u/θ:ℝ):ℂ)-B*D (-1) B θ u G‖ ≤
      polyCap G (U/θ)+C*inverseCap G θ C U := (norm_sub_le _ _).trans (add_le_add hp
    (by simpa only [norm_mul] using mul_le_mul hB hi (norm_nonneg _) hC))
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hθ]
  exact add_le_add
    (mul_le_mul (div_le_div_of_nonneg_right
      (ShiftedEndpoint.mainTerm_bound P.derivative A u θ C U hθ hA hu) hθ.le) hi
      (norm_nonneg _) (div_nonneg (firstCap_nonneg _ _ _ _ hθ hC hU) hθ.le))
    (mul_le_mul (ShiftedEndpoint.mainTerm_bound P A u θ C U hθ hA hu) hd
      (norm_nonneg _) (firstCap_nonneg _ _ _ _ hθ hC hU))

theorem integral_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, profile θ P G A B u) = monomialIntegral A B θ P G 1 (-1) 1 := by
  have h := intervalIntegral.integral_comp_sub_left (profile θ P G A B) θ (a:=0) (b:=θ)
  simp only [sub_self,sub_zero] at h
  rw [← h]
  simp only [monomialIntegral,Nat.sub_self,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
  congr 1
  funext u
  simp only [profile,mainTerm,D,↓reduceIte]
  ring

theorem zero_profile_uniform (P G : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (_hC : 0 ≤ C) (hU : 0 ≤ U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => zeroSum L U (profile θ P G p.1 p.2))
      (fun p => ∫ u in 0..U, profile θ P G p.1 p.2 u) atTop
      {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have hlim : Tendsto (fun L : ℝ => TotientHarmonic.errorConstant*
      (valueCap P G θ C U+U*derivativeCap P G θ C U)/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul
      (TotientHarmonic.errorConstant*(valueCap P G θ C U+U*derivativeCap P G θ C U))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),hlim.eventually (gt_mem_nhds heps)] with L hL he
  intro p hp
  rw [dist_comm,dist_eq_norm]
  exact (zeroSum_error L U _ _ _ _ hL hU (fun u => profile_hasDerivAt θ u P G p.1 p.2)
    (profileDeriv_continuous θ P G p.1 p.2)
    (profile_bound θ C U 0 P G p.1 p.2 hθ hp.1 hp.2 ⟨le_rfl,hU⟩)
    (fun u hu => profileDeriv_bound θ C U u P G p.1 p.2 hθ hp.1 hp.2 hu)).trans_lt he

#print axioms inverse_primitive
#print axioms inverse_hasDerivAt
#print axioms inverse_bound
#print axioms profileDeriv_bound
#print axioms integral_kernel
#print axioms zero_profile_uniform
end XiPrime8845.FengInverseProfile
