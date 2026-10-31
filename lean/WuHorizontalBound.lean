import WuDiskCenter
import WuHorizontalIntegral

/-! A single constant for the actual moving family V_T psi_T.
The estimate is for horizontal phase variation on zero-free segments, not
for an arbitrarily chosen branch of argument or for the full H factor. -/
noncomputable section
open scoped BigOperators
open Filter Topology Set Metric Complex
namespace XiPrime8845.WuHorizontalBound
open WuAuxiliary WuStirling WuGammaJets WuDiskGrowth WuLittlewood
set_option maxHeartbeats 2000000

def growthConstant : ℝ := 2+14*vCap
def logConstant : ℝ := Real.log growthConstant+2
def phaseConstant : ℝ :=
  (Real.pi/Real.log ((24/25:ℝ)/(22/25))+3*(44795000/(19/10:ℝ)))*logConstant

theorem growthConstant_pos : 0 < growthConstant := by
  unfold growthConstant; linarith [vCap_nonneg]

theorem product_analytic (T t : ℝ) (hT : 4 ≤ T) (ht : t ∈ Icc T (2*T)) :
    AnalyticOnNhd ℂ (fun s => V T s*psi T s) (closedBall (center t) (19/10)) := by
  intro s hs
  have hr := disc_strip T t _ s hT ht (by norm_num : (19/10:ℝ)<2)
    (by simpa only [mem_closedBall,dist_eq_norm] using hs)
  exact (((eta_entire _).analyticAt _).div (H_analytic _ hr.1)
    (H_ne_zero _ hr.1 hr.2.2.2.2)).mul ((psi_entire T).analyticAt _)

theorem horizontal_bound : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    ∀ a b : ℝ, 7/16 ≤ a → a ≤ b → b ≤ 3 →
    (∀ σ ∈ Icc a b, V T (point σ t)*psi T (point σ t) ≠ 0) →
    |(∫ σ in a..b, logDeriv (fun s => V T s*psi T s) (point σ t)).im| ≤
      phaseConstant*Real.log T := by
  filter_upwards [WuDiskCenter.center_lower,eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hlower hT hL
  intro t ht a b ha hab hb hn
  let f := fun s => V T s*psi T s
  let B := growthConstant*T^2
  have hc : 1/2 ≤ ‖f (center t)‖ := hlower t ht
  have hgc : 2 ≤ growthConstant := by unfold growthConstant; linarith [vCap_nonneg]
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hfa := product_analytic T t hT ht
  obtain ⟨Z,hZ,hcount,hpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (by norm_num : (0:ℝ)<19/10) hfa
    (norm_ne_zero_iff.mp (by linarith : ‖f (center t)‖ ≠ 0)) hB (by
      intro s hs
      have hsd : ‖s-center t‖ ≤ 19/10 := by
        rw [mem_closedBall,dist_eq_norm] at hs
        linarith
      have he := product_disk_bound T t hT hL ht s hsd
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
    (fun σ hσ => hfa _ (closedBall_subset_closedBall (by norm_num) (hseg σ hσ))) hn
    (by
      intro ρ hρ σ hσ he
      have hz : ρ ∈ (↑Z:Set ℂ) := hρ
      rw [hZ] at hz
      apply hn σ hσ
      change f ((σ:ℂ)+t*I) = 0
      rw [he]
      exact hz.2) hcount
    (fun σ hσ => hpf _ (hseg σ hσ) (hn σ hσ))
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
  apply hphase.trans
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
    unfold growthConstant; linarith [vCap_nonneg])
  have hd : 0 < Real.log ((24/25:ℝ)/(22/25)) := Real.log_pos (by norm_num)
  unfold phaseConstant logConstant
  positivity

/-- Freeze T, then use either independently selected safe horizontal edge.
The same constant works for every subsegment down to Re s = 7/16. -/
theorem horizontal_safe : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    t ∉ WuSafeEndpoints.badHeights (WuAuxiliaryBoundary.auxiliary T) →
    ∀ a b : ℝ, 7/16 ≤ a → a ≤ b → b ≤ 3 →
    |(∫ σ in a..b, logDeriv (fun s => V T s*psi T s) (point σ t)).im| ≤
      phaseConstant*Real.log T := by
  filter_upwards [horizontal_bound,eventually_ge_atTop (4:ℝ)] with T hh hT
  intro t ht hsafe a b ha hab hb
  apply hh t ht a b ha hab hb
  intro σ hσ hz
  have hne := WuSafeEndpoints.horizontal_nonzero _ t hsafe σ
  have hr : 0 < (point σ t).re := by
    simp only [point,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
    linarith [hσ.1]
  have hs1 : point σ t ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp [point] at hi
    linarith [ht.1]
  rw [WuAuxiliaryBoundary.auxiliary_factor T _ (H_ne_zero _ hr hs1),hz,mul_zero] at hne
  exact hne rfl

#print axioms product_analytic
#print axioms horizontal_bound
#print axioms phaseConstant_pos
#print axioms horizontal_safe
end XiPrime8845.WuHorizontalBound
