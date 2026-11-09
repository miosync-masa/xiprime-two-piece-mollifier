import PRZZBasisGridBound
import PRZZClassDualProfile

/-! Both genuine AFE branches of every ordered height-dependent basis
body, in one uniform time-profile class and at one fixed pair of losses. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Filter Topology
namespace XiPrime8845.PRZZBasisPairedBody
set_option maxHeartbeats 10000000

def paired (G F Phi : ℝ → ℂ) (theta T : ℝ) (i j : Fin 7)
    (N : ℕ) (ss : Finset ℕ) (eps eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair (fun Phi a b =>
    PRZZCentralGridIdentity.central (fun _ => G) (fun _ => G) F Phi (Nat.log 2 N+2) N ss
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)
      (PRZZCentralGridIdentity.body T eH) T eps a b)
    Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

theorem bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (G F Phi : ℝ → ℂ)
    (hG : ContDiff ℝ ∞ G) (hF : ContDiff ℝ ∞ F)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (eps eH tau gamma S r geom : ℝ) (heps : 0 ≤ eps) (heH : 0 ≤ eH)
    (htau : 0 < tau) (hgamma : 0 < gamma) (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (theta : ℝ) (L N : ℕ) (ss : Finset ℕ) (i j : Fin 7) (A B : ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖paired G F Phi theta T i j N ss eps eH A B‖ ≤
        C*T^(tau+eps+eH+gamma)*PRZZOptimalPowers.target N T := by
  obtain ⟨jets,hjets,hplain,hdual⟩ := PRZZClassDualProfile.common_members Phi hPhi hcPhi hsPhi S hS
  obtain ⟨C,hC,h⟩ := PRZZBasisGridBound.body_target hWeil hDI K hK G F hG hF hsG hsF
    eps eH tau gamma S r geom heps heH htau hgamma hS hr hgeom
    (Real.log 6) (Real.log_nonneg (by norm_num)) jets hjets
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hdual] with T hdual
  intro theta L N ss i j A B hN hT hNT hlog hST hY hNY hss hA hB hsep
  have hp := h theta T L N ss i j Phi A B hN hT hNT hlog hST hY hNY hss
    hplain hsPhi hA hB hsep
  have hsdual : Function.support (PRZZKeptLiteral.dualProfile Phi T
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) ⊆ Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact hsPhi (fun hz => hx (by simp [PRZZKeptLiteral.dualProfile,hz]))
  have hsep' : r ≤ ‖-B + -A‖ := by
    simpa only [show -B + -A = -(A+B) by ring,norm_neg] using hsep
  have hq := h theta T L N ss i j _ (-B) (-A) hN hT hNT hlog hST hY hNY hss
    (hdual A B hA hB) hsdual (by simpa using hB) (by simpa using hA) hsep'
  unfold paired PRZZCentralMainAssembly.branchPair
  simp only [neg_div] at hq
  exact (norm_add_le _ _).trans ((add_le_add hp hq).trans_eq (by ring))

theorem strict_spatial_subset (L : ℕ) (T : ℝ) :
    PRZZCentralGridIdentity.spatial L T ⊆ PRZZWindowGrids.spatial L T 4 := by
  intro s hs
  obtain ⟨hs,hm⟩ := mem_filter.mp hs
  exact mem_filter.mpr ⟨hs,hm.le⟩

#print axioms bound
#print axioms strict_spatial_subset
end XiPrime8845.PRZZBasisPairedBody
