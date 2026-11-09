import PRZZCappedBodyMass
import PRZZBodyTailOptimal
import PRZZBasisGridBound

/-! Common-cap arithmetic and time aggregation for the actual paired body
Fourier tail, with native rejection removed by a proved exhaustion. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZCappedBodyTail
open PRZZMellinSeparation PRZZNativeCentralLiteral PRZZWindowCentralAssembly
open PRZZBodyTailCollector PRZZActualTailCollector
set_option maxHeartbeats 15000000
attribute [local instance] Classical.propDecidable

def density (F G W : ℝ → ℂ) (c : ℕ → ℂ) (R L N : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Finset.Icc 1 N,
    ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) 2,
      if good R N d ((2:ℝ)^s) z then
        ‖PRZZResolvedTailMass.branch dual A B T t *
          PRZZNativeComponents.row .tail R (bodyCut T V eH s d 0 0 0) W
            (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) z
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
            c d t‖ else 0

theorem density_bound (F G W : ℝ → ℂ) (c : ℕ → ℂ) (R L N : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) (hLR : L ≤ R) :
    density F G W c R L N dual T Q V eD eH t A B ≤
      PRZZCappedBodyMass.mass F G W c R N dual T Q V 4 eD eH t A B := by
  unfold density
  calc
    _ ≤ ∑ s ∈ PRZZWindowGrids.spatial R T 4, ∑ d ∈ Finset.Icc 1 N,
        ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) 2,
          if good R N d ((2:ℝ)^s) z then
            ‖PRZZResolvedTailMass.branch dual A B T t *
              PRZZNativeComponents.row .tail R (bodyCut T V eH s d 0 0 0) W
                (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) z
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                c d t‖ else 0 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro s hs
        obtain ⟨hs,hm⟩ := mem_filter.mp hs
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hs; omega),hm.le⟩
      · intro s hs hnot
        positivity
    _ ≤ _ := by
      unfold PRZZCappedBodyMass.mass
      apply sum_le_sum; intro s hss
      apply sum_le_sum; intro d hd
      rw [PRZZNativeTailRectangle.rectangle]
      apply sum_le_sum; intro u hu
      apply sum_le_sum; intro v hv
      by_cases had : PRZZDiagonalAssembly.admissible N d u v
      · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
        simp only [if_pos had,if_pos had']
        apply sum_le_sum; intro gap hg
        by_cases hh : gap ≠ 0 ∧ |(gap:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d
        · rw [if_pos hh]
          by_cases hm : |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4
          · have hc : gap ≠ 0 ∧ |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
                |((-gap:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
              ⟨hh.1,hm,by simpa only [Int.cast_neg,abs_neg] using hh.2.le⟩
            rw [if_pos hm,if_pos hc]
            rfl
          · rw [if_neg hm]
            split_ifs <;> positivity
        · rw [if_neg hh]
          split_ifs <;> positivity
      · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
        simp only [if_neg had,if_neg had',le_refl]

theorem mass_time (P F Phi : ℝ → ℂ) (c : ℕ → ℂ) (R K L N : ℕ) (dual : Bool)
    (T eD eH : ℝ) (A B : ℂ)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous (profile dual Phi T A B)) (hT : 0 < T)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    PRZZActualTailCollector.mass P F (profile dual Phi T A B) R K L N
      c T eD
      (PRZZCommonSignedWindow.cutoff T eH) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
    ∑ p ∈ range K ×ˢ range K, ∫ t in Icc T (2*T), ‖Phi (t/T)‖*
      density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
        c R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B := by
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  unfold PRZZActualTailCollector.mass PRZZActualTailCollector.nativeCellMass
  apply sum_congr rfl
  intro p hp
  let ss := (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))
  let term := fun s d z t => if good R N d ((2:ℝ)^s) z then
    ‖profile dual Phi T A B (t/T)*PRZZNativeComponents.row .tail R
      (PRZZCommonSignedWindow.cutoff T eH p s d) (PRZZWRowLimit.profile F)
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) ((2:ℝ)^s) z
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      c d t‖ else 0
  have hi (s d : ℕ) (z : PRZZAStar.Index)
      (hz : z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) 2) :
      IntegrableOn (term s d z) (Icc T (2*T)) := by
    have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    by_cases hg : good R N d ((2:ℝ)^s) z
    · have hn := (PRZZTailRowIntegrable.native_integrable R d
        (PRZZCommonSignedWindow.cutoff T eH p s d) (PRZZWRowLimit.profile F)
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) (profile dual Phi T A B)
        c hf.1 hPhi hf.2.2 T ((2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) z hT
        (by positivity) (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs).norm
      apply hn.congr
      exact Eventually.of_forall (fun t => by simp only [term,if_pos hg])
    · simp only [term,if_neg hg]
      exact integrableOn_zero
  have he (t : ℝ) : ‖Phi (t/T)‖*density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
      (PRZZWRowLimit.profile F) c R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B =
      ∑ s ∈ ss, ∑ d ∈ Finset.Icc 1 N,
        ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) 2,
          term s d z t := by
    unfold density
    simp only [mul_sum]
    apply sum_congr rfl; intro s hss
    apply sum_congr rfl; intro d hd
    apply sum_congr rfl; intro z hz
    by_cases hg : good R N d ((2:ℝ)^s) z
    · simp only [term,if_pos hg,profile_time dual Phi T t A B hT.ne',
        norm_mul,PRZZCommonSignedWindow.cutoff,mul_assoc]
    · simp only [term,if_neg hg,mul_zero]
  simp_rw [he]
  rw [integral_finsetSum _ (fun s hss => integrable_finsetSum _
    (fun d hd => integrable_finsetSum _ (fun z hz => hi s d z hz)))]
  apply sum_congr rfl; intro s hss
  rw [integral_finsetSum _ (fun d hd => integrable_finsetSum _ (fun z hz => hi s d z hz))]
  apply sum_congr rfl; intro d hd
  rw [integral_finsetSum _ (fun z hz => hi s d z hz)]
  apply sum_congr rfl; intro z hz
  by_cases hg : good R N d ((2:ℝ)^s) z <;> simp only [term,hg,if_true,if_false,integral_zero]


theorem uniform_mass (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eD eH delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (R L N : ℕ) (dual : Bool) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → L ≤ R → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZActualTailCollector.mass P F (profile dual Phi T A B) R (Nat.log 2 N+2) L N
        c T eD
        (PRZZCommonSignedWindow.cutoff T eH) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨Cb,hCb,hbody⟩ := PRZZCappedBodyMass.uniform _ _ _ hp.1.continuous hp.1.continuous
    hp.2.1 hp.2.1 hp.2.2 hp.2.2 hf.1 hf.2.2 Hcap hHcap 1 4 S r eD eH (2-delta)
    (by norm_num) (by norm_num) hS hr heD he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  obtain ⟨P0,hP0,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨D*Cb*P0,by positivity,?_⟩
  filter_upwards [hbody,PRZZGammaCentral.log_scaled_shifts_eventually S,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hbody hsmall hT hlog
  intro c R L N dual A B hcoef hLR hN hNT hA hB hsep
  have hT0 : 0 < T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have hprofile : Continuous (profile dual Phi T A B) := by
    cases dual
    · exact hPhi
    · exact (PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T
        ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))
        (by simpa only [neg_div,norm_neg] using (hsmall A B hA hB).2)
        (by simpa only [neg_div,norm_neg] using (hsmall A B hA hB).1)).1
  rw [mass_time P F Phi c R (Nat.log 2 N+2) L N dual T eD eH A B hF hFl hFr hprofile hT0 hs]
  have hi : IntegrableOn (fun t : ℝ => Cb*T^(-(2-delta))*‖Phi (t/T)‖) (Icc T (2*T)) :=
    (continuous_const.mul (hPhi.comp (continuous_id.div_const T)).norm).integrableOn_Icc
  have hphiMass : (∫ t in Icc T (2*T), ‖Phi (t/T)‖) ≤ P0*T := by
    simpa only [scaledCutoff,div_eq_mul_inv,mul_comm] using (hcut T hT0).2
  have hbnd (p : ℕ × ℕ) :
      (∫ t in Icc T (2*T), ‖Phi (t/T)‖*
        density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
          c R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B) ≤
      Cb*T^(-(2-delta))*(P0*T) := by
    have hh : (∫ t in Icc T (2*T), ‖Phi (t/T)‖*
        density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
          c R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B) ≤
        ∫ t in Icc T (2*T), Cb*T^(-(2-delta))*‖Phi (t/T)‖ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun t =>
        mul_nonneg (norm_nonneg (Phi (t/T))) (by unfold density; positivity))) hi ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hh := (density_bound _ _ _ c R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B hLR).trans
        (hbody c R N dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B hcoef hN hNT
          (by positivity) (by positivity) ht hA hB hsep)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (Phi (t/T)))).trans_eq (by ring)
    rw [integral_const_mul] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_left hphiMass (by positivity)
  have hgrid' : ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ) ≤ D*T := by
    simpa only [Real.rpow_one] using hgrid N hN T hNT hlog
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), Cb*T^(-(2-delta))*(P0*T) :=
      sum_le_sum (fun p hp => hbnd p)
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*(Cb*T^(-(2-delta))*(P0*T)) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*(Cb*T^(-(2-delta))*(P0*T)) := mul_le_mul_of_nonneg_right hgrid' (by positivity)
    _ = (D*Cb*P0)*T^delta := by
      have he : T*T^(-(2-delta))*T = T^delta := by
        calc
          _ = T^(1:ℝ)*T^(-(2-delta))*T^(1:ℝ) := by simp only [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT0,← Real.rpow_add hT0]; congr 1; ring
      calc
        _ = (D*Cb*P0)*(T*T^(-(2-delta))*T) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg


def actualTail (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair (fun Phi a b =>
    PRZZWindowMoment.tail P P Phi (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T)
      N c T eD (PRZZCommonSignedWindow.cutoff T eH) a b)
    Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

def pairedRejected (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair
    (fun Phi alpha beta => rejected P P Phi R (Nat.log 2 N+2)
      (PRZZLiteralExhaustion.spatialLength T) N c
      T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta)
    Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

def pairedMass (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℝ :=
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  let m := fun Phi alpha beta => mass P P Phi R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N c
    T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta
  m Phi alpha beta+m (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha)


theorem actual_tail_bound (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4)
    (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    ‖actualTail P Phi c N T eD eH A B‖ ≤
      pairedMass P Phi c R N T eD eH A B+‖pairedRejected P Phi c R N T eD eH A B‖ := by
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]
    exact neg_ne_zero.mpr hs
  have hp := tail_split P P Phi R (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) N
    c T eD (PRZZCommonSignedWindow.cutoff T eH)
    alpha beta hP hl hr hPhi hsPhi hT hs
  have hq := tail_split P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N c
    T eD (PRZZCommonSignedWindow.cutoff T eH) (-beta) (-alpha) hP hl hr hd.1 hd.2 hT hs'
  unfold actualTail PRZZCentralMainAssembly.branchPair
  dsimp only
  rw [hp,hq]
  have h1 := native_mass P P Phi R (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) N
    c T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta
  have h2 := native_mass P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N c
    T eD (PRZZCommonSignedWindow.cutoff T eH) (-beta) (-alpha)
  dsimp only [pairedMass,pairedRejected,PRZZCentralMainAssembly.branchPair]
  calc
    _ = ‖(native P P Phi R _ _ _ _ _ _ _ _ _+
        native P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R _ _ _ _ _ _ _ _ _)+
        (rejected P P Phi R _ _ _ _ _ _ _ _ _+
        rejected P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R _ _ _ _ _ _ _ _ _)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) le_rfl)


theorem actual_tail_native (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ)
    (T eD eH : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hheight : 8 ≤ T^(1-eD))
    (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4) (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    ∀ᶠ R : ℕ in atTop,
      ‖actualTail P Phi c N T eD eH A B‖ ≤
        pairedMass P Phi c R N T eD eH A B := by
  have hp := PRZZWRowLimit.profile_regular P hP hl hr
  filter_upwards [rejected_eventually P (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N T eD hp.2.2 hT hheight] with R hR
  have hbnd := actual_tail_bound P Phi c R N T eD eH A B hP hl hr hPhi hsPhi hT ha hb hs
  have hz : pairedRejected P Phi c R N T eD eH A B = 0 := by
    simp only [pairedRejected,PRZZCentralMainAssembly.branchPair,hR,add_zero]
  simpa only [hz,norm_zero,add_zero] using hbnd


theorem actual_tail_of_native_budget (P Phi : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ)
    (T eD eH C : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hheight : 8 ≤ T^(1-eD))
    (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4) (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0)
    (hbudget : ∀ᶠ R : ℕ in atTop, pairedMass P Phi c R N T eD eH A B ≤ C) :
    ‖actualTail P Phi c N T eD eH A B‖ ≤ C := by
  obtain ⟨R,hR,hC⟩ := ((actual_tail_native P Phi c N T eD eH A B
    hP hl hr hPhi hsPhi hT hheight ha hb hs).and hbudget).exists
  exact hR.trans hC


theorem actual_tail_uniform (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eD eH delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (heD1 : eD < 1) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖actualTail P Phi c N T eD eH A B‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := uniform_mass P P Phi hP hPl hPr hP hPl hPr hPhi hcPhi hsPhi
    Hcap hHcap S r eD eH delta hS hr heD he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [h,PRZZRejectedExhaustion.height_eventually eD heD1,
    PRZZGammaCentral.log_scaled_shifts_eventually S,eventually_ge_atTop (2:ℝ)] with T h hheight hsmall hT
  intro c N A B hcoef hN hNT hA hB hsep
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne'
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hL
  apply actual_tail_of_native_budget P Phi c N T eD eH _ A B
    hP hPl hPr hPhi hsPhi hheight.1 hheight.2 (hsmall A B hA hB).1 (hsmall A B hA hB).2 hs
  filter_upwards [eventually_ge_atTop (PRZZLiteralExhaustion.spatialLength T)] with R hR
  have hp := h c R (PRZZLiteralExhaustion.spatialLength T) N false A B hcoef hR hN hNT hA hB hsep
  have hsep' : r ≤ ‖(-B)+(-A)‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have hq := h c R (PRZZLiteralExhaustion.spatialLength T) N true (-B) (-A) hcoef hR hN hNT
    (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA) hsep'
  have hh := add_le_add hp hq
  simpa only [pairedMass,profile,Bool.false_eq_true,if_false,if_true,neg_neg,neg_div,
    show C*T^delta*PRZZOptimalPowers.target N T+C*T^delta*PRZZOptimalPowers.target N T =
      (2*C)*T^delta*PRZZOptimalPowers.target N T by ring] using hh


theorem bodyTail_eq_lift (P F Phi : ℝ → ℂ) (K L N : ℕ) (c e : ℕ → ℂ)
    (T eps eH : ℝ) (a b : ℂ) :
    PRZZBasisGridBound.bodyTail P F Phi K L N c e T eps eH a b =
    PRZZMixedPoisson.lift (fun f => PRZZWindowMoment.tail P F Phi K L N f T eps
      (PRZZCommonSignedWindow.cutoff T eH) a b) c e := by
  simp only [PRZZBasisGridBound.bodyTail,PRZZWindowMoment.tail,PRZZWindowMoment.collect,
    PRZZCentralGridIdentity.spatial,PRZZCommonSignedWindow.cutoff,
    PRZZCentralGridIdentity.body,PRZZCentralGridIdentity.lift_sum]

theorem paired_body_eq (P Phi : ℝ → ℂ) (N : ℕ) (c e : ℕ → ℂ)
    (T eps eH : ℝ) (A B : ℂ) :
    PRZZCentralMainAssembly.branchPair (fun Phi a b =>
      PRZZBasisGridBound.bodyTail P P Phi (Nat.log 2 N+2)
        (PRZZLiteralExhaustion.spatialLength T) N c e T eps eH a b)
      Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
    PRZZMixedPoisson.lift (fun f => actualTail P Phi f N T eps eH A B) c e := by
  unfold PRZZCentralMainAssembly.branchPair actualTail
  simp_rw [bodyTail_eq_lift]
  exact (PRZZCentralGridIdentity.lift_add _ _ c e).symm

/-- The actual merged body tail, with both Gamma branches, is bounded
uniformly before the two coefficient slots and height. No native budget
or unevaluated body-tail estimate is a premise. -/
theorem mixed_bound (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap S r eps eH delta : ℝ) (hHcap : 0 ≤ Hcap)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c e : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.branchPair (fun Phi a b =>
        PRZZBasisGridBound.bodyTail P P Phi (Nat.log 2 N+2)
          (PRZZLiteralExhaustion.spatialLength T) N c e T eps eH a b)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := actual_tail_uniform P Phi hP hl hright hPhi hcPhi hsPhi
    (2*Hcap) (by positivity) S r eps eH delta hS hr heps heps1 he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c e N A B hc hecoef hN hNT hA hB hsep
  rw [paired_body_eq]
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact h _ N A B (PRZZClassZeroCorrection.combine_cap N c e Hcap hHcap hc hecoef z hz)
    hN hNT hA hB hsep

/-- Both height-dependent seven-vector families, hence every ordered
basis pair, enter the actual paired body tail via the evaluated cap 84. -/
theorem family_bound (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r eps eH delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (z w : Fin 7 → ℂ)
      (N : ℕ) (A B : ℂ),
      0 < theta → (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.branchPair (fun Phi a b =>
        PRZZBasisGridBound.bodyTail P P Phi (Nat.log 2 N+2)
          (PRZZLiteralExhaustion.spatialLength T) N
          (PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) z)
          (PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) w)
          T eps eH a b) Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := mixed_bound P Phi hP hl hright hPhi hcPhi hsPhi
    84 S r eps eH delta (by norm_num) hS hr heps heps1 he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro theta z w N A B htheta hz hw hN hNT hA hB hsep
  exact h _ _ N A B
    (fun n hn => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT z hz n)
    (fun n hn => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT w hw n)
    hN hNT hA hB hsep

/-- Insert the evaluated merged tail into the original nonzero collector.
The conclusion is uniform in its original common Fourier cutoff J. -/
theorem nonzero_reduction (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap S r eps eH delta : ℝ) (hHcap : 0 ≤ Hcap)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c e : ℕ → ℂ) (J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun f => PRZZClassZeroCorrection.nonzeroResidual
          P P Phi (Nat.log 2 N+2) J N f T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c e-
        PRZZCentralMainAssembly.branchPair (fun Phi a b =>
          PRZZCentralGridIdentity.central (fun _ => PRZZWRowLimit.profile P)
            (fun _ => PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) Phi
            (Nat.log 2 N+2) N (PRZZCentralGridIdentity.spatial
              (PRZZLiteralExhaustion.spatialLength T) T) c e
            (PRZZCentralGridIdentity.body T eH) T eps a b)
          Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := mixed_bound P Phi hP hl hright hPhi hcPhi hsPhi
    Hcap S r eps eH delta hHcap hS hr heps heps1 he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c e J N A B hc hecoef hN hNT hA hB hsep
  rw [PRZZBasisGridBound.nonzero_eq_body_bodyTail,add_sub_cancel_left]
  exact h c e N A B hc hecoef hN hNT hA hB hsep

#print axioms nonzero_reduction
#print axioms bodyTail_eq_lift
#print axioms paired_body_eq
#print axioms mixed_bound
#print axioms family_bound
#print axioms actual_tail_uniform
#print axioms density_bound
#print axioms mass_time
#print axioms uniform_mass
#print axioms actual_tail_bound
#print axioms actual_tail_native
#print axioms actual_tail_of_native_budget
end XiPrime8845.PRZZCappedBodyTail
