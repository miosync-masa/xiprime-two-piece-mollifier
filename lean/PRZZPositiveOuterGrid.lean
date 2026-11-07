import PRZZOuterLogBudget
import PRZZWindowMoment

/-! Sum the actual positive fixed-window literal cells over d,Q,V,M.
Any spatial subset is allowed, including the original strict window.
The test-function Mellin mass is displayed; no replacement by a dual
height-uniform mass is made in this module. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZPositiveOuterGrid
open PRZZMellinSeparation PRZZCentralArithmeticJoin
set_option maxHeartbeats 10000000

theorem sum_bound (b a gamma : ℝ) (hb : 0 ≤ b) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (T B : ℝ) (ss : Finset ℕ)
      (f : (ℕ × ℕ) → ℕ → ℕ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B →
      ss ⊆ PRZZWindowGrids.spatial L T b →
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N,
        ‖f p s d‖ ≤ B*(T^a*PRZZOptimalPowers.target N T/(d:ℝ))) →
      ‖∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∑ s ∈ ss, ∑ d ∈ Icc 1 N, f p s d‖ ≤
        (C*B)*T^(a+gamma)*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZOuterLogBudget.absorbed b a gamma hb hgamma
  refine ⟨C,hC,?_⟩
  intro L N T B ss f hN hNT hlog hB hss hf
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one ((by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT)
  have hnon (s : ℕ) : 0 ≤ ∑ d ∈ Icc 1 N, B*(T^a*PRZZOptimalPowers.target N T/(d:ℝ)) := by
    apply sum_nonneg; intro d hd
    unfold PRZZOptimalPowers.target
    positivity
  calc
    _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∑ s ∈ ss, ∑ d ∈ Icc 1 N, B*(T^a*PRZZOptimalPowers.target N T/(d:ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro p hp
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro s hs
      exact (norm_sum_le _ _).trans (sum_le_sum (fun d hd => hf p hp s hs d hd))
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∑ _s ∈ PRZZWindowGrids.spatial L T b,
          ∑ d ∈ Icc 1 N, B*(T^a*PRZZOptimalPowers.target N T/(d:ℝ)) := by
      apply sum_le_sum; intro p hp
      exact sum_le_sum_of_subset_of_nonneg hss (fun s hs hns => hnon s)
    _ = B*(∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∑ _s ∈ PRZZWindowGrids.spatial L T b,
          ∑ d ∈ Icc 1 N, T^a*PRZZOptimalPowers.target N T/(d:ℝ)) := by simp only [mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (h L N T hN hNT hlog) hB).trans_eq (by ring)

def grid (F0 F2 FM Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ) (ss : Finset ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    positiveCell N d (PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) T ((2:ℝ)^s)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) FM
      (scaledCutoff F0 ((2:ℝ)^p.1)) (scaledCutoff F2 ((2:ℝ)^p.2)) Phi
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

theorem dyadic_scale (N k : ℕ) (hN : 1 ≤ N) (hk : k ∈ range (Nat.log 2 N+2)) :
    (2:ℝ)^k ≤ 2*(N:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  calc
    _ ≤ (2:ℝ)^(Nat.log 2 N+1) := pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
    _ = 2*(2:ℝ)^(Nat.log 2 N) := by rw [pow_succ]; ring
    _ ≤ _ := by linarith

/-- Full positive outer grid with arbitrarily small height loss, not a
sum of assumed optimized cell bounds. Constants and cutoff exponents
are selected before height, all windows, and both shift parameters. -/
theorem optimized
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hFM : Continuous FM) (hcM : HasCompactSupport FM)
    (hs0 : Function.support F0 ⊆ Icc (1/2:ℝ) 3)
    (hs2 : Function.support F2 ⊆ Icc (1/2:ℝ) 3)
    (hsM : Function.support FM ⊆ Icc (1/2:ℝ) 3) :
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < eH ∧ 0 < C ∧
      ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖grid F0 F2 FM Phi js N ss T eD eH A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T*
          (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨eD,eH,C,hD,hDH,hC,hcell⟩ := PRZZWindowOptimalCell.positive_body_epsilon
    hWeil hDI K hK js (tau/2) S r geom (by linarith) hS hr hgeom
    F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  obtain ⟨Co,hCo,houter⟩ := sum_bound geom (tau/2) (tau/2) hgeom (by linarith)
  refine ⟨eD,eH,Co*C,hD,hDH,by positivity,?_⟩
  intro L N ss T A B Phi hN hT hNT hlog hss hA hB hsep hPhi hsPhi
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  have hh := houter L N T (C*J) ss
    (fun p s d => positiveCell N d (PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) T ((2:ℝ)^s)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) FM
      (scaledCutoff F0 ((2:ℝ)^p.1)) (scaledCutoff F2 ((2:ℝ)^p.2)) Phi
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
    hN (by linarith) hlog (mul_nonneg hC.le hJ) hss (by
      intro p hp s hs d hd
      have hsp := (mem_filter.mp (hss hs)).2
      have hq := (dyadic_scale N p.1 hN (mem_product.mp hp).1).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hv := (dyadic_scale N p.2 hN (mem_product.mp hp).2).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hc := hcell N d s T ((2:ℝ)^p.1) ((2:ℝ)^p.2) B A Phi
        (by omega) (Finset.mem_Icc.mp hd).1 hT hNT
        ((by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)) hlog
        (by positivity) (by positivity) hq hv hsp hB hA (by simpa only [add_comm] using hsep) hPhi hsPhi
      have hscale : (fun y : ℝ => FM (((2:ℝ)^s)⁻¹*y)) =
          scaledCutoff FM ((2:ℝ)^s) := rfl
      calc
        _ ≤ C*T^(tau/2)*PRZZOptimalPowers.target N T/(d:ℝ)*J := by
          simpa only [positiveCell,hscale,← add_div,add_comm,J] using hc
        _ = _ := by ring)
  change ‖grid F0 F2 FM Phi js N ss T eD eH A B‖ ≤ _ at hh
  convert hh using 1
  dsimp only [J]
  ring_nf
  simp only [mul_comm]

#print axioms sum_bound
#print axioms dyadic_scale
#print axioms optimized
end XiPrime8845.PRZZPositiveOuterGrid
