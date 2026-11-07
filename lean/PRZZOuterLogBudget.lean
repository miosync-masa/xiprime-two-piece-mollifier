import PRZZWindowOptimalCell
import PRZZWindowGrids

/-! The actual outer d,Q,V,M multiplicity costs only log^4 T.
The divisor denominator is retained; the exhaustion length never enters
the spatial count. Positive weights are summed before power absorption. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZOuterLogBudget
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem spatial_log_card (L : ℕ) (T b : ℝ) (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T) (hb : 0 ≤ b) :
    ((PRZZWindowGrids.spatial L T b).card:ℝ) ≤ (b/Real.log 2+1)*Real.log T := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let R := b*Real.log T/Real.log 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsub : PRZZWindowGrids.spatial L T b ⊆ range (⌊R⌋₊+1) := by
    intro s hs
    have hsp := (mem_filter.mp hs).2
    have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^s) hsp
    rw [Real.log_pow,Real.log_rpow ht] at hh
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ((le_div_iff₀ h2).mpr hh)))
  have hc := card_le_card hsub
  have hc' : ((PRZZWindowGrids.spatial L T b).card:ℝ) ≤ (⌊R⌋₊:ℝ)+1 := by
    simpa only [card_range,Nat.cast_add,Nat.cast_one] using (Nat.cast_le.mpr hc : ((PRZZWindowGrids.spatial L T b).card:ℝ) ≤ ((range (⌊R⌋₊+1)).card:ℝ))
  have hf := Nat.floor_le hR
  dsimp [R] at hf hc'
  calc
    _ ≤ b*Real.log T/Real.log 2+1 := by linarith
    _ ≤ b*Real.log T/Real.log 2+Real.log T := by linarith
    _ = _ := by ring

theorem reciprocal_cell (N j : ℕ) :
    (∑ d ∈ PRZZDyadic.cell N j, 1/(d:ℝ)) ≤ 2 := by
  have hp : (0:ℝ) < (2:ℝ)^j := by positivity
  have hsub : PRZZDyadic.cell N j ⊆ Icc 1 (2^(j+1)) := by
    intro d hd
    have hh := (PRZZDyadic.mem_cell N j d).mp hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hh.1).1,hh.2.2.le⟩
  have hc : ((PRZZDyadic.cell N j).card:ℝ) ≤ (2:ℝ)^(j+1) := by
    exact_mod_cast (show (PRZZDyadic.cell N j).card ≤ 2^(j+1) by
      simpa using card_le_card hsub)
  calc
    _ ≤ ∑ _d ∈ PRZZDyadic.cell N j, 1/(2:ℝ)^j := by
      apply sum_le_sum; intro d hd
      have hh : (2:ℝ)^j ≤ d := by exact_mod_cast ((PRZZDyadic.mem_cell N j d).mp hd).2.1
      exact one_div_le_one_div_of_le hp hh
    _ = ((PRZZDyadic.cell N j).card:ℝ)/(2:ℝ)^j := by simp [div_eq_mul_inv]
    _ ≤ (2:ℝ)^(j+1)/(2:ℝ)^j := div_le_div_of_nonneg_right hc hp.le
    _ = 2 := by rw [pow_succ]; field_simp

theorem reciprocal_sum (N : ℕ) :
    (∑ d ∈ Icc 1 N, 1/(d:ℝ)) ≤ 2*(Nat.log 2 N+1:ℝ) := by
  have he : (∑ d ∈ Icc 1 N, 1/(d:ℝ)) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ d ∈ PRZZDyadic.cell N j, 1/(d:ℝ) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro d hd
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hd).2))
  rw [he]
  calc
    _ ≤ ∑ _j ∈ range (Nat.log 2 N+1), (2:ℝ) := sum_le_sum (fun j hj => reciprocal_cell N j)
    _ = _ := by simp; ring

def weight (L N : ℕ) (T b : ℝ) : ℝ :=
  ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
    ∑ _s ∈ PRZZWindowGrids.spatial L T b, ∑ d ∈ Icc 1 N, 1/(d:ℝ)

theorem weight_log (L N : ℕ) (T b : ℝ) (hN : 1 ≤ N) (hNT : (N:ℝ) ≤ T)
    (hlog : 1 ≤ Real.log T) (hb : 0 ≤ b) :
    weight L N T b ≤
      ((1/Real.log 2+2)^2*(b/Real.log 2+1)*(2*(1/Real.log 2+1)))*(Real.log T)^4 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj := PRZZDyadicBudget.cell_count N T hN hNT hlog
  have hj' : (Nat.log 2 N+2:ℝ) ≤ (1/Real.log 2+2)*Real.log T := by linarith
  have hs := spatial_log_card L T b ((by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT) hlog hb
  have hd := (reciprocal_sum N).trans (mul_le_mul_of_nonneg_left hj (by norm_num : (0:ℝ) ≤ 2))
  unfold weight
  simp only [sum_const,nsmul_eq_mul,card_product,card_range]
  push_cast
  calc
    _ ≤ ((1/Real.log 2+2)*Real.log T)*((1/Real.log 2+2)*Real.log T)*
        (((b/Real.log 2+1)*Real.log T)*(2*((1/Real.log 2+1)*Real.log T))) := by
      gcongr
    _ = _ := by ring

theorem absorbed (b a gamma : ℝ) (hb : 0 ≤ b) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (T : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T →
      (∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∑ _s ∈ PRZZWindowGrids.spatial L T b,
          ∑ d ∈ Icc 1 N, T^a*PRZZOptimalPowers.target N T/(d:ℝ)) ≤
        C*T^(a+gamma)*PRZZOptimalPowers.target N T := by
  let B := (1/Real.log 2+2)^2*(b/Real.log 2+1)*(2*(1/Real.log 2+1))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨D,hD,hpow⟩ := PRZZOptimalOuter.power_log_absorbed 4 a (a+gamma) (by linarith)
  refine ⟨B*D+1,by positivity,?_⟩
  intro L N T hN hNT hlog
  have ht : 1 ≤ T := (by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT
  have htarg : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have he : (∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
      ∑ _s ∈ PRZZWindowGrids.spatial L T b,
        ∑ d ∈ Icc 1 N, T^a*PRZZOptimalPowers.target N T/(d:ℝ)) =
      T^a*PRZZOptimalPowers.target N T*weight L N T b := by
    unfold weight
    simp only [mul_sum,div_eq_mul_inv,one_mul,mul_assoc]
  rw [he]
  have hw := mul_le_mul_of_nonneg_left (weight_log L N T b hN hNT hlog hb)
    (show 0 ≤ T^a*PRZZOptimalPowers.target N T by positivity)
  have hp := mul_le_mul_of_nonneg_left (hpow T ht) (mul_nonneg hB htarg)
  have hz : 0 ≤ T^(a+gamma)*PRZZOptimalPowers.target N T := by positivity
  dsimp only [B] at *
  nlinarith only [hw,hp,hz]

#print axioms spatial_log_card
#print axioms reciprocal_cell
#print axioms reciprocal_sum
#print axioms weight_log
#print axioms absorbed
end XiPrime8845.PRZZOuterLogBudget
