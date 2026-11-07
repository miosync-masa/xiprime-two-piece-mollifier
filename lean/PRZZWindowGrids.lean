import PRZZResolvedTailMass

/-! Uniform outer-grid bounds for the source-localized polynomial M
window. The original exhaustion L is not used as a counting bound. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZWindowGrids
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

def spatial (L : ℕ) (T b : ℝ) : Finset ℕ :=
  (range (L+2)).filter (fun s => (2:ℝ)^s ≤ T^b)

def gaps (T b eD : ℝ) : Finset ℤ :=
  Icc (-⌈2*T^(b+eD)⌉) ⌈2*T^(b+eD)⌉

theorem spatial_card (L : ℕ) (T b : ℝ) (hT : 1 ≤ T) (hb : 0 ≤ b) :
    ((spatial L T b).card:ℝ) ≤ 2*T^b := by
  have hpow : 1 ≤ T^b := Real.one_le_rpow hT hb
  have hn (s : ℕ) : (s:ℝ) ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih =>
      push_cast
      rw [pow_succ]
      have hp : 1 ≤ (2:ℝ)^s := one_le_pow₀ (by norm_num)
      linarith
  have hsub : spatial L T b ⊆ range (⌊T^b⌋₊+1) := by
    intro s hs
    have hs' := (mem_filter.mp hs).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ((hn s).trans hs')))
  have hh := card_le_card hsub
  rw [card_range] at hh
  have hh' : ((spatial L T b).card:ℝ) ≤ (⌊T^b⌋₊:ℝ)+1 := by exact_mod_cast hh
  have hf := Nat.floor_le (show 0 ≤ T^b by positivity)
  linarith

theorem gaps_card (T b eD : ℝ) (hT : 1 ≤ T) (hb : 0 ≤ b) (he : 0 ≤ eD) :
    ((gaps T b eD).card:ℝ) ≤ 7*T^(b+eD) := by
  have hp : 1 ≤ T^(b+eD) := Real.one_le_rpow hT (by linarith)
  have hc : (0:ℤ) ≤ ⌈2*T^(b+eD)⌉ := Int.ceil_nonneg (by positivity)
  have heq : (gaps T b eD).card = (2*⌈2*T^(b+eD)⌉+1).toNat := by
    simp only [gaps,Int.card_Icc]
    congr 1
    ring
  have hz : (0:ℤ) ≤ 2*⌈2*T^(b+eD)⌉+1 := by omega
  have hcast : (((2*⌈2*T^(b+eD)⌉+1).toNat:ℕ):ℝ) = ((2*⌈2*T^(b+eD)⌉+1:ℤ):ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz)
  rw [heq,hcast]
  push_cast
  have hceil := Int.ceil_lt_add_one (2*T^(b+eD))
  linarith

theorem source_gap (T M Q b eD : ℝ) (d : ℕ) (delta : ℤ)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hMT : M ≤ T^b) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T)
    (hd : 1 ≤ d)
    (hg : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d) :
    delta ∈ gaps T b eD := by
  have hT0 : 0 < T := by linarith
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 ≤ M*Q/T^(1-eD) := by positivity
  have hdiv : M*Q/T^(1-eD)/(d:ℝ) ≤ 2*T^(b+eD) := by
    calc
      _ ≤ M*Q/T^(1-eD) := div_le_self hp hd'
      _ ≤ T^b*(2*T)/T^(1-eD) := by gcongr
      _ = 2*T^(b+eD) := by
        rw [show T^b*(2*T)/T^(1-eD) = 2*(T^b*T/T^(1-eD)) by ring]
        congr 1
        calc
          T^b*T/T^(1-eD) = T^b*T^(1:ℝ)/T^(1-eD) := by rw [Real.rpow_one]
          _ = T^(b+eD) := by
            rw [← Real.rpow_add hT0,← Real.rpow_sub hT0]
            congr 1
            ring
  have hh := hg.trans hdiv
  have hceil : 2*T^(b+eD) ≤ (⌈2*T^(b+eD)⌉:ℝ) := Int.le_ceil _
  have hab := abs_le.mp (hh.trans hceil)
  apply mem_Icc.mpr
  constructor
  · exact_mod_cast hab.1
  · exact_mod_cast hab.2

theorem dyadic_card (N : ℕ) (T : ℝ) (hN : 1 ≤ N) (hNT : (N:ℝ) ≤ T) :
    ((range (Nat.log 2 N+1)).card:ℝ) ≤ 2*T := by
  rw [card_range]
  have hl : Nat.log 2 N ≤ N := Nat.log_le_self _ _
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl' : (Nat.log 2 N:ℝ) ≤ N := by exact_mod_cast hl
  push_cast
  linarith

#print axioms spatial_card
#print axioms gaps_card
#print axioms source_gap
#print axioms dyadic_card
end XiPrime8845.PRZZWindowGrids
