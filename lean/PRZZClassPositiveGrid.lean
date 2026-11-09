import PRZZClassWidePoisson
import PRZZPositiveOuterGrid

/-! Actual mixed positive body cells summed over d,Q,V,M. The strict
source cutoffs and the subunit bodyCut branch are retained. Coefficient
weights have a displayed common unit cap; no outer mass bound is assumed.
This does not estimate the other collective Poisson components. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZClassPositiveGrid
open PRZZMellinSeparation PRZZClassPoisson
set_option maxHeartbeats 10000000

def grid (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (js ks : List ℕ)
    (N : ℕ) (ss : Finset ℕ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    w p s d*positiveCell N d (PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) T ((2:ℝ)^s)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F
      (scaledCutoff (F0 p.1) ((2:ℝ)^p.1)) (scaledCutoff (F2 p.2) ((2:ℝ)^p.2)) Phi
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

/-- Uniform before all height-dependent cutoff families and the outer
exhaustion L. The d harmonic sum and three dyadic counts are evaluated by
the existing logarithmic collector, not supplied as a new mass premise. -/
theorem grid_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eD eH tau gamma S r geom : ℝ)
    (heD : 0 ≤ eD) (heH : 0 ≤ eH) (htau : 0 < tau) (hgamma : 0 < gamma)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ)
      (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets (F0 k)) →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets
        (scaledCutoff (F2 k) ((2:ℝ)^k))) →
      (∀ s ∈ ss, PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s))) →
      (∀ k, Function.support (F0 k) ⊆ Icc (1/2:ℝ) 3) →
      (∀ k, Function.support (F2 k) ⊆ Icc (1/2:ℝ) 3) →
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N, ‖w p s d‖ ≤ 1) →
      ‖grid F0 F2 F Phi js ks N ss w T eD eH A B‖ ≤
        C*T^(tau+eD+eH+gamma)*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hcell⟩ := PRZZClassWidePoisson.body_target hWeil hDI K hK js ks eD eH tau S r geom
    heD heH htau hS hr hgeom width jets hjets widthPhi hwPhi jetsPhi hjPhi
  obtain ⟨D,hD,houter⟩ := PRZZPositiveOuterGrid.sum_bound geom (tau+eD+eH) gamma hgeom hgamma
  refine ⟨D*C,by positivity,?_⟩
  intro L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  apply houter L N T C ss _ hN (by linarith) hlog hC.le hss
  intro p hp s hs d hd
  have hq := mem_product.mp hp
  have hQ := (PRZZPositiveOuterGrid.dyadic_scale N p.1 hN hq.1).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
  have hV := (PRZZPositiveOuterGrid.dyadic_scale N p.2 hN hq.2).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
  have hh := hcell (F0 p.1) (scaledCutoff (F2 p.2) ((2:ℝ)^p.2)) F N d s T
    ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B Phi (hf0 p.1 hq.1) (hf2 p.2 hq.2) (hfM s hs)
    hN (mem_Icc.mp hd).1 hT hNT
    ((by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)) hlog hST
    (by positivity) (by positivity) hQ hV (mem_filter.mp (hss hs)).2
    (hs0 _) (PRZZWindowScaleSupply.scaled_support _ _ (by positivity) (hs2 _)) hsF
    hA hB hsep hPhi hsPhi
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right (hw p hp s hs d hd) (norm_nonneg _)).trans
  simpa only [one_mul,mul_div_assoc,mul_assoc] using hh

theorem grid_optimized
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < eH ∧ 0 < C ∧ ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ)
      (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets (F0 k)) →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets
        (scaledCutoff (F2 k) ((2:ℝ)^k))) →
      (∀ s ∈ ss, PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s))) →
      (∀ k, Function.support (F0 k) ⊆ Icc (1/2:ℝ) 3) →
      (∀ k, Function.support (F2 k) ⊆ Icc (1/2:ℝ) 3) →
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N, ‖w p s d‖ ≤ 1) →
      ‖grid F0 F2 F Phi js ks N ss w T eD eH A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := grid_target hWeil hDI K hK js ks (tau/16) (tau/8) (tau/4) (tau/4)
    S r geom (by linarith) (by linarith) (by linarith) (by linarith) hS hr hgeom
    width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨tau/16,tau/8,C,by linarith,by linarith,hC,?_⟩
  intro L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  have hh := h L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF
    hA hB hsep hPhi hsPhi hw
  apply hh.trans
  have htar : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (by linarith : tau/4+tau/16+tau/8+tau/4 ≤ tau)) hC.le) htar

#print axioms grid_optimized
#print axioms grid_target
end XiPrime8845.PRZZClassPositiveGrid
