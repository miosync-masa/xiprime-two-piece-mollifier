import PRZZDiscardedTimePair
import PRZZExhaustiveAFEError

/-! Exact insertion into the original exhaustive AFE error. Only the
two valued discarded subfamilies are removed. The cutoff complement,
all other Fourier/freeze/boundary terms, diagonal, zeroPair and Gamma
defect remain literal. No convergence of separately pruned components
or identification of the retained field with central A* is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Filter Topology
namespace XiPrime8845.PRZZPrunedAFEError
open PRZZDiscardedTimePair PRZZMellinSeparation
set_option maxHeartbeats 9000000

theorem selected_continuous (L J N : ℕ) (P G H : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hleft : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (PRZZSourceMaskFamily.selectedFamily L J N P G H a R alpha beta)
      (Set.Icc T (2*T)) := by
  classical
  have hc : ContinuousOn (PRZZAllOffDiagonalRows.selected L N P G H a R alpha beta)
      (Set.Icc T (2*T)) := by
    unfold PRZZAllOffDiagonalRows.selected
    apply continuousOn_finsetSum; intro s hss
    apply continuousOn_finsetSum; intro z hz
    split_ifs
    · apply (PRZZAllOffDiagonalRows.row_continuous L N s P z
        (PRZZWRowReindex.leftCoefficient a G) (PRZZWRowReindex.rightCoefficient a H)
        alpha beta hs T hT).congr
      intro t ht
      exact (PRZZWRowReindex.row_reindex L N s z P G H a alpha beta t).symm
    · exact continuousOn_const
  apply hc.congr
  intro t ht
  exact (PRZZSourceMaskFamily.selected_resolved L J N P G H hP hleft hright a R
    alpha beta hs t (hT.trans_le ht.1)).symm

theorem field_continuous (L J N : ℕ) (P : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hleft : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (PRZZExhaustiveAFEError.field L J N P a alpha beta) (Set.Icc T (2*T)) := by
  have hh := selected_continuous L J N P (fun _ => 1) (fun _ => 1) hP hleft hright a
    (fun _ _ => True) alpha beta hs T hT
  apply hh.congr
  intro t ht
  rw [PRZZExhaustiveAFEError.field_eq]
  simp only [PRZZAllPoissonRows.family,PRZZSourceMaskFamily.selectedFamily,and_true]

def keptField (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZExhaustiveAFEError.field L J N (fun x => (P x:ℂ))
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
    selected P G H js L J N T Q V eps alpha beta t

/-- Explicitly retain both the cutoff complement and the strict
complement of the discarded source test. Nothing is silently exhausted. -/
theorem kept_field_partition (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    keptField P G H js L J N T Q V eps alpha beta t =
      (PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
       PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)+
      PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
        (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t := by
  unfold keptField selected
  rw [PRZZExhaustiveAFEError.field_eq,
    PRZZSourceMaskFamily.family_partition L J N (fun x => (P x:ℂ))
      (scaledCutoff G Q) (scaledCutoff H V) _ (PRZZSourceMaskFamily.discarded T Q eps)]
  ring

def model (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    alpha beta T (scaledCutoff F T)+
    (((∫ t in Set.Icc T (2*T), scaledCutoff F T t*keptField P G H js L J N T Q V eps alpha beta t)+
      ∫ t in Set.Icc T (2*T), (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        keptField P G H js L J N T Q V eps (-beta) (-alpha) t)-
      PRZZZeroCoupled.zeroPair N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff F T))+
    ∫ t in Set.Icc T (2*T), scaledCutoff F T t*
      PRZZZeroCross.gammaDefect N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t

theorem model_split (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Continuous F) (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.componentModel L J N (fun x => (P x:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff F T) =
      model F G H P js L J N T Q V eps alpha beta+
        pair F G H P js L J N T Q V eps alpha beta := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have hp : Continuous (scaledCutoff F T) := hF.comp (continuous_const.mul continuous_id)
  have hg : Continuous (PRZZAFEDual.dualMultiplier alpha beta) := by
    have ar := abs_le.mp ((abs_re_le_norm alpha).trans ha)
    have br := abs_le.mp ((abs_re_le_norm beta).trans hb)
    exact PRZZMollifiedTime.dualMultiplier_continuous alpha beta
      (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hs' : -beta+-alpha ≠ 0 := by simpa only [← neg_add,add_comm] using neg_ne_zero.mpr hs
  have hi (a b : ℂ) (hab : a+b ≠ 0) (phi : ℝ → ℂ) (hphi : Continuous phi) :
      (∫ t in Set.Icc T (2*T), phi t*keptField P G H js L J N T Q V eps a b t) =
      (∫ t in Set.Icc T (2*T), phi t*PRZZExhaustiveAFEError.field L J N
        (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) a b t)-
      ∫ t in Set.Icc T (2*T), phi t*selected P G H js L J N T Q V eps a b t := by
    have h1 : IntegrableOn (fun t => phi t*PRZZExhaustiveAFEError.field L J N
        (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) a b t)
        (Set.Icc T (2*T)) :=
      (hphi.continuousOn.mul (field_continuous L J N _ hP hl hr _ a b hab T hT)).integrableOn_compact isCompact_Icc
    have h2 : IntegrableOn (fun t => phi t*selected P G H js L J N T Q V eps a b t)
        (Set.Icc T (2*T)) :=
      (hphi.continuousOn.mul (selected_continuous L J N _ _ _ hP hl hr _
        (PRZZSourceMaskFamily.discarded T Q eps) a b hab T hT)).integrableOn_compact isCompact_Icc
    unfold keptField
    simp_rw [mul_sub]
    exact integral_sub h1 h2
  unfold model PRZZExhaustiveAFEError.componentModel pair
  rw [hi alpha beta hs _ hp,hi (-beta) (-alpha) hs'
    (fun t => scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t) (hp.mul hg)]
  ring

theorem original_error_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Continuous F) (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      alpha beta T (scaledCutoff F T)-model F G H P js L J N T Q V eps alpha beta =
      (PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff F T)-PRZZExhaustiveAFEError.componentModel L J N
          (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff F T))+
        pair F G H P js L J N T Q V eps alpha beta := by
  rw [model_split F G H P js L J N hF hP hleft hright T Q V eps hT alpha beta ha hb hs]
  ring

theorem all_model_error_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Continuous F) (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      alpha beta T (scaledCutoff F T)-model F G H P js L J N T Q V eps alpha beta =
      (PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff F T)-PRZZAllPoissonAFE.model L J N
          (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff F T))+
        pair F G H P js L J N T Q V eps alpha beta := by
  simpa only [PRZZExhaustiveAFEError.model_eq] using
    original_error_eq F G H P js L J N hF hP hleft hright T Q V eps hT alpha beta ha hb hs

/-- The original AFE error limit and the actual uniform discarded-pair
bound give an eventual finite-truncation estimate. J may grow arbitrarily
with L. No convergence of the removed pair is used or inferred. -/
theorem scaled_error_eventually (F G H : ℝ → ℂ) (P : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (js : List ℕ) (S r eps delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ Q V : ℝ, 0 < Q → ∀ J : ℕ → ℕ, ∀ᶠ L : ℕ in atTop,
      ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff F T)-
        model F G H P js L (J L) N T Q V eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨Ca,hCa,ha⟩ := PRZZExhaustiveAFEError.scaled_full_error_limit (fun x => (P x:ℂ))
    hP (by intro x hx; simp [hleft x hx]) (by intro x hx; simp [hright x hx])
    js S r delta hS hr hd
  obtain ⟨Cd,hCd,hdisc⟩ := PRZZDiscardedTimePair.scaled_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps 0 hS hr he he1
  obtain ⟨P0,hP0,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass F hF.continuous hcF
  refine ⟨Ca*P0+1+Cd,by positivity,?_⟩
  filter_upwards [ha,hdisc,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T ha hdisc hsmall hT
  intro A B hA hB hsep N hN hNT Q V hQ J
  have hT0 : 0 < T := by linarith
  have hphi : Continuous (scaledCutoff F T) := hF.continuous.comp (continuous_const.mul continuous_id)
  obtain ⟨E,hlim,hbound⟩ := ha A B hA hB hsep N hN hNT (scaledCutoff F T) P0 hphi hP0.le
    (fun t _ => (hcut T hT0).1 t) J
  have hL := hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖E‖))
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbase : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) hd.le).trans
      (le_mul_of_one_le_right (by positivity) htarg)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  filter_upwards [hL] with L hL
  have h1 := hdisc L (J L) N Q V A B P hN hNT hQ hA hB hsep hP hm hlo hhi hleft hright
  simp only [neg_zero,Real.rpow_zero,mul_one] at h1
  rw [original_error_eq F G H P js L (J L) N hF.continuous hP hleft hright T Q V eps hT0
    _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs]
  apply (norm_add_le _ _).trans
  have h2 := hL.le.trans (add_le_add hbound (le_refl (1:ℝ)))
  have h3 := h1.trans (le_mul_of_one_le_right hCd.le hbase)
  nlinarith only [h2,h3,hbase]

#print axioms selected_continuous
#print axioms field_continuous
#print axioms kept_field_partition
#print axioms model_split
#print axioms original_error_eq
#print axioms all_model_error_eq
#print axioms scaled_error_eventually
end XiPrime8845.PRZZPrunedAFEError
