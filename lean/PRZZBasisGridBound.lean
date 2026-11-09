import PRZZBasisGridCutoff

/-! One Weil/DI constant for the 49 ordered, height-dependent basis cells.
The original common-J Fourier tail tends to zero simultaneously for all
pairs at each fixed height. This is not a uniform bodyCut-tail estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Filter Topology
namespace XiPrime8845.PRZZBasisGridBound
open PRZZBasisGridCutoff PRZZMellinSeparation
set_option maxHeartbeats 10000000

theorem body_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (G F : ℝ → ℂ)
    (hG : ContDiff ℝ ∞ G) (hF : ContDiff ℝ ∞ F)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (eps eH tau gamma S r geom : ℝ)
    (heps : 0 ≤ eps) (heH : 0 ≤ eH) (htau : 0 < tau) (hgamma : 0 < gamma)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi)
    (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta T : ℝ) (L N : ℕ) (ss : Finset ℕ)
      (i j : Fin 7) (Phi : ℝ → ℂ) (A B : ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi →
      Function.support Phi ⊆ Set.Icc (1:ℝ) 2 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralGridIdentity.central (fun _ => G) (fun _ => G) F Phi
        (Nat.log 2 N+2) N ss (PRZZWitnessBasis.basis theta T i)
        (PRZZWitnessBasis.basis theta T j) (PRZZCentralGridIdentity.body T eH)
        T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(tau+eps+eH+gamma)*PRZZOptimalPowers.target N T := by
  obtain ⟨jg,hjg,hg⟩ := normalized_members G hG hsG
  obtain ⟨jf,hjf,hf⟩ := PRZZClassPoisson.spatial_members F hF hsF
  let jets := fun n => jg n+jf n
  have hj : ∀ n, 0 ≤ jets n := fun n => add_nonneg (hjg n) (hjf n)
  choose C hC h using fun (i j : Fin 7) => PRZZClassSignedGrid.grid_target
    hWeil hDI K hK (PRZZWitnessMass.arithmeticLabels i) (PRZZWitnessMass.arithmeticLabels j)
    eps eH tau gamma S r geom heps heH htau hgamma hS hr hgeom
    (Real.log 6) jets hj widthPhi hwPhi jetsPhi hjPhi
  have hsum : 0 ≤ ∑ i, ∑ j, C i j :=
    sum_nonneg (fun i hi => sum_nonneg (fun j hj => (hC i j).le))
  refine ⟨(∑ i, ∑ j, C i j)+1,by positivity,?_⟩
  intro theta T L N ss i j Phi A B hN hT hNT hlog hST hY hNY hss hPhi hsPhi hA hB hsep
  have hY0 : 0 < PRZZ.length theta T := by
    have : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    exact this.trans_le hNY
  have hm (i : Fin 7) (k : ℕ) (hk : k ∈ range (Nat.log 2 N+2)) (R : ℝ) (hR : 0 < R) :
      PRZZProfileMellin.Member (Real.log 6) jets
        (scaledCutoff (normalized G (PRZZ.length theta T) ((2:ℝ)^k) i) R) := by
    apply PRZZClassPoisson.member_mono _ _ _ _ le_rfl
      (fun n => le_add_of_nonneg_right (hjf n)) _
      (hg _ _ R i hY (one_le_pow₀ (by norm_num))
        ((PRZZPositiveOuterGrid.dyadic_scale N k hN hk).trans (by gcongr)) hR)
  rw [body_basis_grid theta T i j G G F Phi hsG hsG N ss eps eH A B hY0 hNY]
  have hb := h i j L N ss T A B
    (fun k => normalized G (PRZZ.length theta T) ((2:ℝ)^k) i)
    (fun k => normalized G (PRZZ.length theta T) ((2:ℝ)^k) j)
    F Phi (fun _ _ _ => 1) hN hT hNT hlog hST hss
    (fun k hk => by
      have hh := hm i k hk 1 (by norm_num)
      unfold scaledCutoff at hh
      simpa using hh)
    (fun k hk => hm j k hk _ (by positivity))
    (fun s hs => PRZZClassPoisson.member_mono _ _ _ _ le_rfl
      (fun n => le_add_of_nonneg_left (hjg n)) _ (hf _ (by positivity)))
    (fun k => (normalized_support G _ _ i).trans hsG)
    (fun k => (normalized_support G _ _ j).trans hsG) hsF hA hB hsep hPhi hsPhi
    (fun p hp s hs d hd => by simp)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by unfold PRZZOptimalPowers.target; positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hi : C i j ≤ ∑ k, C i k := single_le_sum (fun k hk => (hC i k).le) (mem_univ j)
  have hj' : (∑ k, C i k) ≤ ∑ l, ∑ k, C l k :=
    single_le_sum (fun l hl => sum_nonneg (fun k hk => (hC l k).le)) (mem_univ i)
  linarith

theorem body_optimized
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (G F : ℝ → ℂ)
    (hG : ContDiff ℝ ∞ G) (hF : ContDiff ℝ ∞ F)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (tau S r geom : ℝ) (htau : 0 < tau)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi)
    (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta T : ℝ) (L N : ℕ) (ss : Finset ℕ)
      (i j : Fin 7) (Phi : ℝ → ℂ) (A B : ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi →
      Function.support Phi ⊆ Set.Icc (1:ℝ) 2 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralGridIdentity.central (fun _ => G) (fun _ => G) F Phi
        (Nat.log 2 N+2) N ss (PRZZWitnessBasis.basis theta T i)
        (PRZZWitnessBasis.basis theta T j) (PRZZCentralGridIdentity.body T (tau/8))
        T (tau/16) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := body_target hWeil hDI K hK G F hG hF hsG hsF
    (tau/16) (tau/8) (tau/4) (tau/4) S r geom (by linarith) (by linarith)
    (by linarith) (by linarith) hS hr hgeom widthPhi hwPhi jetsPhi hjPhi
  refine ⟨C,hC,?_⟩
  intro theta T L N ss i j Phi A B hN hT hNT hlog hST hY hNY hss hPhi hsPhi hA hB hsep
  apply (h theta T L N ss i j Phi A B hN hT hNT hlog hST hY hNY hss hPhi hsPhi hA hB hsep).trans
  apply mul_le_mul_of_nonneg_right _ (by unfold PRZZOptimalPowers.target; positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith)) hC.le

/-- All 49 pairs, at each fixed height, share one exhaustion threshold.
No bound at the prescribed row bodyCut follows from this convergence. -/
theorem tails_eventually (P F Phi : ℝ → ℂ) (K L N : ℕ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (theta T eps : ℝ) (hT : 0 < T) (a b : ℂ) (hs : a+b ≠ 0)
    (E : ℝ) (hE : 0 < E) :
    ∀ᶠ J : ℕ in atTop, ∀ i j : Fin 7,
      ‖PRZZMixedPoisson.lift (fun c => PRZZCentralMainAssembly.tailPart
        P F Phi K L J N c T eps a b)
        (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)‖ < E := by
  have ht (i j : Fin 7) : Tendsto (fun J : ℕ =>
      PRZZMixedPoisson.lift (fun c => PRZZCentralMainAssembly.tailPart
        P F Phi K L J N c T eps a b)
        (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)) atTop (𝓝 0) := by
    have h (c : ℕ → ℂ) := PRZZCentralMainAssembly.tail_part_tendsto P F Phi K L N c
      hF hl hr hPhi hsPhi T eps hT a b hs
    unfold PRZZMixedPoisson.lift
    convert ((((h _).sub (h _)).add ((h _).const_mul I)).sub
      ((h _).const_mul I)).div_const (4:ℂ) using 1 <;> simp
  have hh : ∀ i j : Fin 7, ∀ᶠ J : ℕ in atTop,
      ‖PRZZMixedPoisson.lift (fun c => PRZZCentralMainAssembly.tailPart
        P F Phi K L J N c T eps a b)
        (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)‖ < E := by
    intro i j
    exact ((ht i j).norm).eventually (eventually_lt_nhds (by simpa using hE))
  simpa only [Filter.eventually_all] using hh

/-- Common-J transfer and Fourier tail must be evaluated together: their
sum is exactly the body-cut tail, not two quantities vanishing with J. -/
theorem cell_tail_transport (N d J B : ℕ) (D T M : ℝ) (c e : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (a b : ℂ) :
    (PRZZCentralGridIdentity.cell N d J D T M c e F G H Phi a b-
      PRZZCentralGridIdentity.cell N d B D T M c e F G H Phi a b)+
      PRZZMixedPoisson.lift (fun f => PRZZCentralArithmeticJoin.cellTail
        N d J D T M f F G H Phi a b) c e =
    PRZZMixedPoisson.lift (fun f => PRZZCentralArithmeticJoin.cellTail
      N d B D T M f F G H Phi a b) c e := by
  simp only [PRZZCentralGridIdentity.cell,PRZZClassPoisson.positiveCell,
    PRZZClassNegativePoisson.negativeCell,PRZZCentralArithmeticJoin.cellTail,
    PRZZCentralArithmeticJoin.prefix_split,PRZZMixedPoisson.lift]
  ring

def bodyTail (P F Phi : ℝ → ℂ) (K L N : ℕ) (c e : ℕ → ℂ)
    (T eps eH : ℝ) (a b : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, ∑ s ∈ PRZZCentralGridIdentity.spatial L T, ∑ d ∈ Icc 1 N,
    PRZZMixedPoisson.lift (fun f => PRZZCentralArithmeticJoin.cellTail N d
      (PRZZCentralGridIdentity.body T eH p s d)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s) f
      (PRZZWRowLimit.profile F) (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a b) c e

theorem transfer_tail_eq_bodyTail (P F Phi : ℝ → ℂ) (K L J N : ℕ)
    (c e : ℕ → ℂ) (T eps eH : ℝ) (a b : ℂ) :
    PRZZCentralGridIdentity.transfer (fun _ => PRZZWRowLimit.profile P)
      (fun _ => PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F) Phi K J N
      (PRZZCentralGridIdentity.spatial L T) c e T eps eH a b+
    PRZZMixedPoisson.lift (fun f => PRZZCentralMainAssembly.tailPart P F Phi K L J N
      f T eps a b) c e = bodyTail P F Phi K L N c e T eps eH a b := by
  simp only [PRZZCentralGridIdentity.transfer,PRZZCentralMainAssembly.tailPart,
    PRZZCentralMainAssembly.collect,bodyTail,PRZZCentralGridIdentity.spatial,
    PRZZCentralGridIdentity.lift_sum,← sum_add_distrib]
  apply sum_congr rfl; intro p hp
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  exact cell_tail_transport N d J _ _ T _ c e _ _ _ Phi a b

/-- The original two-branch nonzero residual now has just one retained
tail object per branch, with exactly the same bodyCut as the Weil/DI body. -/
theorem nonzero_eq_body_bodyTail (P F Phi : ℝ → ℂ) (K J N : ℕ)
    (c e : ℕ → ℂ) (T eps eH : ℝ) (a b : ℂ) :
    PRZZMixedPoisson.lift (fun f => PRZZClassZeroCorrection.nonzeroResidual
      P F Phi K J N f T eps a b) c e =
    PRZZCentralMainAssembly.branchPair (fun Phi a b =>
      PRZZCentralGridIdentity.central (fun _ => PRZZWRowLimit.profile P)
        (fun _ => PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F) Phi K N
        (PRZZCentralGridIdentity.spatial (PRZZLiteralExhaustion.spatialLength T) T)
        c e (PRZZCentralGridIdentity.body T eH) T eps a b) Phi T a b+
    PRZZCentralMainAssembly.branchPair (fun Phi a b =>
      bodyTail P F Phi K (PRZZLiteralExhaustion.spatialLength T) N c e T eps eH a b)
      Phi T a b := by
  have he := PRZZCentralGridIdentity.nonzero_eq_body_transfer_tail
    P F Phi K J N c e T eps eH a b
  have hp := transfer_tail_eq_bodyTail P F Phi K (PRZZLiteralExhaustion.spatialLength T)
    J N c e T eps eH a b
  have hq := transfer_tail_eq_bodyTail P F (PRZZKeptLiteral.dualProfile Phi T a b)
    K (PRZZLiteralExhaustion.spatialLength T) J N c e T eps eH (-b) (-a)
  simp only [PRZZCentralMainAssembly.branchPair,PRZZCentralGridIdentity.lift_add] at he ⊢
  linear_combination he+hp+hq

#print axioms body_target
#print axioms body_optimized
#print axioms tails_eventually
#print axioms cell_tail_transport
#print axioms transfer_tail_eq_bodyTail
#print axioms nonzero_eq_body_bodyTail
end XiPrime8845.PRZZBasisGridBound
