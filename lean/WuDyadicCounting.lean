import WuLocalCounting
import WuXiBands
import Zeta23.XiPrime.ZeroCount

/-! Counts on the retained window are included in the original dyadic
window. This inclusion avoids charging endpoint zeros twice, and avoids
any change of mollifier height. The retained width is fixed before T. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology Complex
namespace XiPrime8845.WuDyadicCounting
open WuAuxiliary WuStirling WuLocalCounting Zeta23.XiPrime
set_option maxHeartbeats 2000000

def proportion : ℝ := 1-Real.log WitnessMomentBound.countingCap/PRZZAsymptotic.R
def leading (ε : ℝ) : ℝ := proportion-2*ε/PRZZAsymptotic.R

theorem proportion_gt : (0.8845:ℝ) < proportion := by
  simpa only [proportion,WitnessMomentBound.radius_match] using WitnessMomentBound.countingCap_budget

/-- The final intended strict proportion assertion, for the literal AF
counts. This definition records a target, not a new assumption or axiom. -/
def StrictProportion : Prop :=
  ∃ b : ℝ, (0.8845:ℝ) < b ∧ ∀ᶠ X : ℝ in atTop,
    b*(Ncount 0 X:ℝ) ≤ (N0 0 X:ℝ)

theorem closed_sum_le_dyadic (T u v : ℝ) (hu : T < u) (hv : v ≤ 2*T)
    (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ critical '' Icc u v ∧ xiDeriv s = 0) :
    (∑ s ∈ S, (analyticOrderNatAt xiDeriv s:ℝ)) ≤ (N0 T (2*T):ℝ) := by
  classical
  have hsub : (↑S:Set ℂ) ⊆ WuXiBands.zeros.window T (2*T) ∩ {s | s.re=1/2} := by
    intro s hs
    obtain ⟨⟨t,ht,rfl⟩,hz⟩ := hS s hs
    refine ⟨⟨hz,?_,?_⟩,?_⟩
    · simpa [critical] using hu.trans_le ht.1
    · simpa [critical] using ht.2.trans hv
    · norm_num [critical]
  have hh := WuXiBands.zeros.finsum_mult_mono T (2*T) hsub inter_subset_left
  rw [finsum_mem_coe_finset] at hh
  change (∑ s ∈ S, xiDerivMult s) ≤ N0 T (2*T) at hh
  simpa only [Nat.cast_sum,analyticOrderNatAt_xiDeriv] using
    (show ((∑ s ∈ S, xiDerivMult s):ℝ) ≤ (N0 T (2*T):ℝ) by exact_mod_cast hh)

def budget (δ ε T : ℝ) : ℝ :=
  ((1-2*δ)*T-2)*Real.log T/2*leading ε-firstConstant*T-
    2*WuVHorizontal.phaseConstant*Real.log T-2*Real.pi-1-
    (1+3*Real.pi+6*WuHorizontalBound.phaseConstant*Real.log T)*Real.log T/PRZZAsymptotic.R

theorem countLower_eq (T u v ε : ℝ) :
    countLower T u v ε =
      (v-u)*Real.log T/2*leading ε-firstConstant*(v-u)-
        2*WuVHorizontal.phaseConstant*Real.log T-2*Real.pi-1-
        (1+3*Real.pi+6*WuHorizontalBound.phaseConstant*Real.log T)*Real.log T/PRZZAsymptotic.R := by
  unfold countLower boundaryBudget leading proportion
  ring

theorem budget_le (δ ε T u v : ℝ) (hT : 1 < T) (hδ : 0 < δ)
    (hu : u ∈ Icc ((1+δ)*T) ((1+δ)*T+1))
    (hv : v ∈ Icc ((2-δ)*T-1) ((2-δ)*T)) (he : 0 ≤ leading ε) :
    budget δ ε T ≤ countLower T u v ε := by
  rw [countLower_eq]
  have hlen : (1-2*δ)*T-2 ≤ v-u ∧ v-u ≤ T := by
    constructor <;> nlinarith [hu.1,hu.2,hv.1,hv.2]
  have hm := mul_le_mul_of_nonneg_right hlen.1
    (show 0 ≤ Real.log T/2*leading ε by positivity [Real.log_pos hT])
  have hc := mul_le_mul_of_nonneg_left hlen.2 firstConstant_pos.le
  unfold budget
  nlinarith

/-- Actual multiplicity count, with all auxiliary safety conditions now
discharged by the independent inward endpoint supplier. -/
theorem budget_eventually_le (δ ε : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hε : 0 < ε) (he : 0 ≤ leading ε) :
    ∀ᶠ T : ℝ in atTop, budget δ ε T ≤ Real.pi*(N0 T (2*T):ℝ) := by
  obtain ⟨ρ,hρ,hsafe⟩ := WuBoundaryZeros.safe_window_log_input
  filter_upwards [closed_count_lower δ ε hδ hd hε,hsafe δ hδ hd,eventually_gt_atTop (1:ℝ)]
    with T hcount hs hT
  obtain ⟨u,hu,v,hv,huv,hsu,hsv,_⟩ := hs
  have hu' : u ∈ Icc ((1+δ)*T) ((1+δ)*T+1) := ⟨hu.1.le,hu.2.le⟩
  have hv' : v ∈ Icc ((2-δ)*T-1) ((2-δ)*T) := ⟨hv.1.le,hv.2.le⟩
  obtain ⟨S,hS,hbound⟩ := hcount u hu' v hv' huv.le hsu hsv
  exact (budget_le δ ε T u v hT hδ hu' hv' he).trans (hbound.trans
    (mul_le_mul_of_nonneg_left (closed_sum_le_dyadic T u v
      (by nlinarith [hu.1]) (by nlinarith [hv.2]) S (fun s hs => (hS s).mp hs)) Real.pi_pos.le))

theorem budget_normalized_tendsto (δ ε : ℝ) :
    Tendsto (fun T => budget δ ε T/(T*Real.log T)) atTop
      (nhds ((1-2*δ)*leading ε/2)) := by
  have hi := tendsto_inv_atTop_zero (𝕜:=ℝ)
  have hl := hi.comp Real.tendsto_log_atTop
  have hlog : Tendsto (fun T : ℝ => Real.log T/T) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1 := (tendsto_const_nhds (x := (1-2*δ)*leading ε/2)).sub
    (hl.const_mul firstConstant)
  have h2 := h1.sub (hi.const_mul (leading ε))
  have h3 := h2.sub (hi.const_mul (2*WuVHorizontal.phaseConstant))
  have h4 := h3.sub ((hi.mul hl).const_mul (2*Real.pi+1))
  have h5 := h4.sub (hi.const_mul ((1+3*Real.pi)/PRZZAsymptotic.R))
  have h := h5.sub (hlog.const_mul (6*WuHorizontalBound.phaseConstant/PRZZAsymptotic.R))
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have ht : T ≠ 0 := by linarith
  have hl : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  dsimp only [Function.comp_def]
  unfold budget
  field_simp
  ring

#print axioms proportion_gt
#print axioms closed_sum_le_dyadic
#print axioms countLower_eq
#print axioms budget_le
#print axioms budget_eventually_le
#print axioms budget_normalized_tendsto
end XiPrime8845.WuDyadicCounting
