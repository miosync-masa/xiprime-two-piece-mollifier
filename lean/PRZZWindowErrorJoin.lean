import PRZZWindowBoundary
import PRZZValuedSourceDiscarded

/-! One common budget for the displayed, actual error terms: the Gamma
kernel replacement defect, the valued exact-phase discarded sum, the
native source-localized Fourier mass, and the actual cover-boundary.
This is not an assumed identification with the complete AFE error. The
discarded term here is not multiplied by a time-varying dual Gamma factor. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Filter
namespace XiPrime8845.PRZZWindowErrorJoin
open PRZZMellinSeparation PRZZGCoefficient
set_option maxHeartbeats 7000000

theorem cutoff_mass (F : ℝ → ℂ) (hF : Continuous F) (hcF : HasCompactSupport F) :
    ∃ P : ℝ, 0 < P ∧ ∀ T : ℝ, 0 < T →
      (∀ t, ‖scaledCutoff F T t‖ ≤ P) ∧
      (∫ t in Icc T (2*T), ‖scaledCutoff F T t‖) ≤ P*T := by
  obtain ⟨C,hC⟩ := hcF.exists_bound_of_continuous hF
  let P := max C 0+1
  have hP : 0 < P := by dsimp [P]; positivity
  have hp (T t : ℝ) : ‖scaledCutoff F T t‖ ≤ P :=
    (hC _).trans ((le_max_left C 0).trans (by dsimp [P]; linarith))
  refine ⟨P,hP,?_⟩
  intro T hT
  refine ⟨hp T,?_⟩
  have hi : IntegrableOn (fun _ : ℝ => P) (Icc T (2*T)) := continuous_const.integrableOn_Icc
  apply (integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _)) hi
    (Eventually.of_forall (hp T))).trans_eq
  simp [integral_const,Measure.real,Real.volume_Icc,show 2*T-T = T by ring,hT.le,smul_eq_mul]
  ring

def replacement (F : ℝ → ℂ) (js : List ℕ) (N : ℕ) (T : ℝ) (A B : ℂ) : ℂ :=
  ∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight (scaledCutoff F T)
    (fun n => (coefficient js n:ℂ)) (fun n => (coefficient js n:ℂ)) N t *
      PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t

def boundary (F G H W : ℝ → ℂ) (js : List ℕ) (L J N : ℕ) (dual : Bool)
    (T Q V b : ℝ) (A B : ℂ) : ℂ :=
  ∫ t in Icc T (2*T), (scaledCutoff F T t*PRZZResolvedTailMass.branch dual A B T t)*
    PRZZWindowBoundary.originalPart .boundary L J N W (scaledCutoff G Q) (scaledCutoff H V)
      (fun n => (coefficient js n:ℂ)) T b t (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

theorem boundary_zero (F G H W : ℝ → ℂ) (js : List ℕ) (L J N : ℕ) (dual : Bool)
    (T Q V b : ℝ) (A B : ℂ) (hN : 1 ≤ N)
    (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3) (hL : 4*(N:ℝ)*T^b ≤ L) :
    boundary F G H W js L J N dual T Q V b A B = 0 := by
  unfold boundary
  simp_rw [PRZZWindowBoundary.original_part_eq]
  exact PRZZWindowBoundary.boundary_integral_zero L J N W _ _ _ T b _ _ _ hN hsW hL

theorem common_budget (F G H W : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 < eD) (heD1 : eD ≤ 1) (he : eD < eH) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N K : ℕ) (dual : Bool) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d → 4*(N:ℝ)*T^b ≤ L →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖replacement F js N T A B‖+
        ‖PRZZValuedSourceDiscarded.error F G H P js N K T M Q V d eD A B s‖+
        (∫ t in Icc T (2*T), ‖scaledCutoff F T t‖*
          PRZZWindowNativeTail.nativeMass G H W js L N dual T Q V b eD eH t A B)+
        ‖boundary F G H W js L J N dual T Q V b A B‖ ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨P0,hP0,hcut⟩ := cutoff_mass F hF.continuous hcF
  obtain ⟨Cr,hCr,hrb⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hdelta
  obtain ⟨Cd,hCd,hdb⟩ := PRZZValuedSourceDiscarded.scaled_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eD 0 hr heD heD1
  obtain ⟨Ct,hCt,htb⟩ := PRZZWindowNativeTail.native_przz_time G H W hG hH hcG hcH hsG
    hW hsW js a b S r eD eH delta ha hb hS hr heD.le he
  refine ⟨Cr*P0+Cd+Ct*P0,by positivity,?_⟩
  filter_upwards [hrb,hdb,htb,eventually_ge_atTop (1:ℝ)] with T hrb hdb htb hT
  intro L J N K dual M Q V d A B P s hN hNT hM hQ hd hL hA hB hsep hm hlo hhi hleft hright
  have hT0 : 0 < T := lt_of_lt_of_le
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  have hphi : Continuous (scaledCutoff F T) := hF.continuous.comp (continuous_const.mul continuous_id)
  have hc := hcut T hT0
  have h1 := hrb A B hA hB hsep N hN hNT (scaledCutoff F T) P0 hphi hP0.le
    (fun t _ => hc.1 t)
  change ‖replacement F js N T A B‖ ≤ _ at h1
  have h2 := hdb N K M Q V d A B P s hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  simp only [neg_zero,Real.rpow_zero,mul_one] at h2
  have h3 := htb L N dual Q V P0 A B (scaledCutoff F T) hN hNT hQ hP0.le hA hB hsep hphi hc.2
  rw [boundary_zero F G H W js L J N dual T Q V b A B hN hsW hL,norm_zero,add_zero]
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbase : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    (Real.one_le_rpow hT hdelta.le).trans (le_mul_of_one_le_right (by positivity) htarg)
  have h2' := h2.trans (le_mul_of_one_le_right hCd.le hbase)
  nlinarith only [h1,h2',h3]

#print axioms cutoff_mass
#print axioms boundary_zero
#print axioms common_budget
end XiPrime8845.PRZZWindowErrorJoin
