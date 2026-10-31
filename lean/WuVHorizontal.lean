import WuGammaPhase

/-! Horizontal phase for V alone. The Landau normalization multiplies V
by the fixed (for each disc) scalar psi_T(2+it); its logarithmic derivative
is still exactly that of V. No auxiliary-product phase is reused as V phase. -/
noncomputable section
open scoped BigOperators
open Filter Topology Set Metric Complex
namespace XiPrime8845.WuVHorizontal
open WuAuxiliary WuStirling WuGammaJets WuDiskGrowth WuLittlewood
set_option maxHeartbeats 2000000

def growthConstant : ℝ := 2+14*(Real.pi^2/6)*vCap
def logConstant : ℝ := Real.log growthConstant+2
def phaseConstant : ℝ :=
  (Real.pi/Real.log ((24/25:ℝ)/(22/25))+3*(44795000/(19/10:ℝ)))*logConstant

theorem growthConstant_pos : 0 < growthConstant := by
  unfold growthConstant; have := vCap_nonneg; positivity

theorem V_analytic (T t : ℝ) (hT : 4 ≤ T) (ht : t ∈ Icc T (2*T)) :
    AnalyticOnNhd ℂ (V T) (closedBall (center t) (19/10)) := by
  intro s hs
  have hr := disc_strip T t _ s hT ht (by norm_num : (19/10:ℝ)<2)
    (by simpa only [mem_closedBall,dist_eq_norm] using hs)
  exact ((eta_entire _).analyticAt _).div (H_analytic _ hr.1)
    (H_ne_zero _ hr.1 hr.2.2.2.2)

theorem horizontal_bound : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    ∀ a b : ℝ, 7/16 ≤ a → a ≤ b → b ≤ 3 →
    (∀ σ ∈ Icc a b, V T (point σ t) ≠ 0) →
    |(∫ σ in a..b, logDeriv (V T) (point σ t)).im| ≤
      phaseConstant*Real.log T := by
  filter_upwards [WuDiskCenter.center_lower,eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hlower hT hL
  intro t ht a b ha hab hb hn
  let f := fun s => V T s*psi T (center t)
  let B := growthConstant*T^2
  have hc : 1/2 ≤ ‖f (center t)‖ := hlower t ht
  have hgc : 2 ≤ growthConstant := by
    unfold growthConstant
    exact le_add_of_nonneg_right (by have := vCap_nonneg; positivity)
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hcpsi : psi T (center t) ≠ 0 := by
    intro hz
    simp [f,hz] at hc
    linarith
  have hn' : ∀ σ ∈ Icc a b, f (point σ t) ≠ 0 :=
    fun σ hσ => mul_ne_zero (hn σ hσ) hcpsi
  have hfa : AnalyticOnNhd ℂ f (closedBall (center t) (19/10)) :=
    fun s hs => (V_analytic T t hT ht s hs).mul analyticAt_const
  obtain ⟨Z,hZ,hcount,hpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (by norm_num : (0:ℝ)<19/10) hfa
    (norm_ne_zero_iff.mp (by linarith : ‖f (center t)‖ ≠ 0)) hB (by
      intro s hs
      have hsd : ‖s-center t‖ ≤ 19/10 := by
        rw [mem_closedBall,dist_eq_norm] at hs
        linarith
      have he : ‖f s‖ ≤ (7*(Real.pi^2/6)*vCap)*T^2 := by
        rw [norm_mul]
        have hh := mul_le_mul (V_disk_bound T t hT hL ht s hsd)
          (WuRightMollifier.psi_bound T (by linarith) (center t) (by simp [WuGammaJets.center]))
          (norm_nonneg _) (mul_nonneg vCap_nonneg (by linarith))
        have hlin : vCap*T*(7*(Real.pi^2/6)) ≤ (7*(Real.pi^2/6)*vCap)*T^2 := by
          have hpp : 0 ≤ 7*(Real.pi^2/6)*vCap := by have := vCap_nonneg; positivity
          calc
            _ = (7*(Real.pi^2/6)*vCap)*T := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (show T ≤ T^2 by nlinarith) hpp
        exact hh.trans hlin
      have hx := mul_le_mul_of_nonneg_left hc (show 0 ≤ B by linarith)
      apply he.trans
      dsimp [B,growthConstant] at hx ⊢
      nlinarith [sq_nonneg T])
  have hseg (σ : ℝ) (hσ : σ ∈ Icc a b) :
      point σ t ∈ closedBall (center t) ((83/100)*(19/10)) := by
    rw [mem_closedBall,dist_eq_norm]
    have he : point σ t-center t = ((σ-2:ℝ):ℂ) := by
      simp [point,WuGammaJets.center]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [hσ.1,hσ.2]
  have hphase := WuHorizontalIntegral.horizontal_of_partial_fraction f a b t _ _ Z hab
    (fun σ hσ => hfa _ (closedBall_subset_closedBall (by norm_num) (hseg σ hσ))) hn'
    (by
      intro ρ hρ σ hσ he
      have hz : ρ ∈ (↑Z:Set ℂ) := hρ
      rw [hZ] at hz
      apply hn' σ hσ
      change f ((σ:ℂ)+t*I) = 0
      rw [he]
      exact hz.2) hcount
    (fun σ hσ => hpf _ (hseg σ hσ) (hn' σ hσ))
  have hlog : Real.log B ≤ logConstant*Real.log T := by
    have hTp : 0 < T := by linarith
    have he : Real.log B = Real.log growthConstant+2*Real.log T := by
      rw [show B = growthConstant*T^2 from rfl,Real.log_mul growthConstant_pos.ne' (pow_ne_zero _ hTp.ne'),Real.log_pow]
      norm_num
    have hglog : 0 ≤ Real.log growthConstant := Real.log_nonneg (by linarith)
    rw [he]
    dsimp [logConstant]
    nlinarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hd : 0 < Real.log ((24/25:ℝ)/(22/25)) := Real.log_pos (by norm_num)
  have hphase' : |(∫ σ in a..b, logDeriv (V T) (point σ t)).im| ≤
      Real.pi*(1/Real.log ((24/25:ℝ)/(22/25))*Real.log B)+
        (b-a)*(44795000/(19/10:ℝ)*Real.log B) := by
    simpa only [f,point,logDeriv_mul_const _ _ hcpsi] using hphase
  apply hphase'.trans
  have he : Real.pi*(1/Real.log ((24/25:ℝ)/(22/25))*Real.log B)+
      (b-a)*(44795000/(19/10:ℝ)*Real.log B) ≤
      (Real.pi/Real.log ((24/25:ℝ)/(22/25))+3*(44795000/(19/10:ℝ)))*Real.log B := by
    have hlen : b-a ≤ 3 := by linarith
    have hh := mul_le_mul_of_nonneg_right hlen
      (show 0 ≤ 44795000/(19/10:ℝ)*Real.log B by positivity)
    calc
      _ ≤ Real.pi*(1/Real.log ((24/25:ℝ)/(22/25))*Real.log B)+
          3*(44795000/(19/10:ℝ)*Real.log B) := add_le_add le_rfl hh
      _ = _ := by ring
  exact he.trans ((mul_le_mul_of_nonneg_left hlog (by positivity)).trans_eq (by
    unfold phaseConstant; ring))

theorem phaseConstant_pos : 0 < phaseConstant := by
  have hg : 0 ≤ Real.log growthConstant := Real.log_nonneg (by
    unfold growthConstant
    have hh : 0 ≤ 14*(Real.pi^2/6)*vCap := by have := vCap_nonneg; positivity
    linarith)
  have hd : 0 < Real.log ((24/25:ℝ)/(22/25)) := Real.log_pos (by norm_num)
  unfold phaseConstant logConstant
  positivity


theorem right_real_pos : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    0 < (V T (point 3 t)).re := by
  let e := (2-Real.pi^2/6)/2
  have he : 0 < e := by dsimp [e]; linarith [Zeta23.RvM.pi_sq_div_six_sub_one_lt_one]
  have hd : Tendsto (fun T : ℝ => WuRightBoundary.differenceCap/Real.log T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul WuRightBoundary.differenceCap
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    hd.eventually (gt_mem_nhds he)] with T hT hL hdT
  intro t ht
  have hz := Zeta23.RvM.norm_riemannZeta_sub_one_le (s := point 3 t) (by norm_num [point])
  have hr := (Complex.abs_re_le_norm (riemannZeta (point 3 t)-1)).trans hz
  have hv := (Complex.abs_re_le_norm (V T (point 3 t)-riemannZeta (point 3 t))).trans_lt
    ((WuRightBoundary.V_sub_zeta_bound T t hT hL ht).trans_lt hdT)
  simp only [Complex.sub_re,Complex.one_re] at hr hv
  have hz' := (abs_le.mp hr).1
  have hv' := (abs_lt.mp hv).1
  dsimp [e] at hv' he
  linarith

theorem right_phase_bound : ∀ᶠ T : ℝ in atTop, ∀ u v : ℝ,
    T ≤ u → u ≤ v → v ≤ 2*T →
      |WuContourCounting.verticalPhase (V T) 3 u v| ≤ Real.pi := by
  filter_upwards [right_real_pos] with T hh
  intro u v hu huv hv
  have ha (t : ℝ) : AnalyticAt ℂ (V T) (point 3 t) :=
    ((eta_entire _).analyticAt _).div (H_analytic _ (by norm_num [point]))
      (H_ne_zero _ (by norm_num [point]) (by
        intro he; have := congrArg Complex.re he; norm_num [point] at this))
  simpa only [WuContourCounting.verticalPhase,point,mul_comm I] using
    Zeta23.XiPrime.ZeroCount.abs_im_integral_logDeriv_vertical_le_pi huv
      (fun t _ => ha t) (fun t ht => hh t ⟨hu.trans ht.1,ht.2.trans hv⟩)

#print axioms V_analytic
#print axioms horizontal_bound
#print axioms phaseConstant_pos
#print axioms right_real_pos
#print axioms right_phase_bound
end XiPrime8845.WuVHorizontal

