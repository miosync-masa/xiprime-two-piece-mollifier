import PRZZClassDI

/-! Class-uniform free logarithmic HB factors, with the original retained
row, extra dyadic mask and shortened Weil endpoint. No support jump or
coprimality condition is dropped. Constants precede the cutoff function. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZClassFreeLength
open PRZZMellinSeparation PRZZTypeIWeights PRZZSourceEnvelope PRZZMaskedVariation
open PRZZTypeI PRZZTypeICoprime PRZZFreeLogRow PRZZFreeLogCoprime PRZZFreeSource
open PRZZFreeDyadic PRZZFreeLength
set_option maxHeartbeats 8000000

theorem log_variation (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h a H m : ℕ, ∀ T Q F t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ a → a ≤ PRZZRowWindow.hi N d h j → m ≤ J →
      1 < T → (h:ℝ) ≤ T → 0 < F → F ≤ a → (a:ℝ)+H ≤ T → (H:ℝ) ≤ 2*F →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (sample N d j h a m F0 Q t alpha) H ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := PRZZClassVariation.source_absorbed width jets hjets J eps S Z heps hS hZ
  refine ⟨Real.exp S*C,by positivity,?_⟩
  intro F0 hf0 N d j h a H m T Q F t alpha hd hh ha hai hm hT hhT hF hFa haT hH halpha hz
  rw [sample_eq N d j h a m F0 Q t alpha hd hh ha hai,PRZZActualRowSmooth.variation_const]
  have hv' := hv F0 hf0 T Q ((d:ℝ)*h) a F (1/2) alpha ((t:ℂ)*Complex.I) m H
    (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
    hT hF hFa (by exact_mod_cast ha) haT hH le_rfl
    (by simp) halpha (by norm_num; linarith) hm
  have hb : ‖((h:ℂ)^alpha)⁻¹*twist h t‖ ≤ Real.exp S := by
    rw [norm_mul,twist_norm _ _ (by exact_mod_cast hh),mul_one]
    exact PRZZSourceCoefficients.inverse_shift T S h alpha hT hS
      ⟨by exact_mod_cast hh,hhT⟩ halpha
  have hv0 : 0 ≤ PRZZTypeI.variation
      (mask (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
        (fun k => sourceWeight (exponent (1/2) alpha ((t:ℂ)*Complex.I)) m
          ((d:ℝ)*h) (scaledCutoff F0 Q) ((a:ℝ)+k))) H := by
    unfold PRZZTypeI.variation; positivity
  have he := mul_le_mul hb hv' hv0 (Real.exp_pos S).le
  simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,mul_assoc] using he

theorem log_retained (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (sample N d j h (PRZZRowWindow.lo h j) m F0 Q t alpha)
        (PRZZRowPlacement.span N d h j) ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := log_variation width jets hjets J eps S Z heps hS hZ
  refine ⟨C,hC,?_⟩
  intro F0 hf0 N d j h m T Q t alpha hd hh hm hT hNT hne ha hz
  have hp := PRZZRowPlacement.placement N d h j T hh hne hNT
  have hhN : (h:ℝ) ≤ N := by exact_mod_cast multiplier_le N d h j _ hh hp.1 hne
  exact hv F0 hf0 N d j h _ _ m T Q (PRZZRowWindow.lo h j) t alpha hd hh hp.1 hne hm hT
    (by linarith) hp.2.1 le_rfl hp.2.2.1 hp.2.2.2 ha hz

theorem log_full (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => row N d j h m F0 Q t alpha (k+1)) N ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := log_retained width jets hjets J eps S Z heps hS hZ
  refine ⟨2*C,by positivity,?_⟩
  intro F0 hf0 N d j h m T Q t alpha hd hh hm hT hNT ha hz
  by_cases hne : PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j
  · have hl : 1 ≤ PRZZRowWindow.lo h j := Nat.succ_le_succ (Nat.zero_le _)
    have hu := PRZZRowPlacement.upper_le N d h j hh
    have hs : 0 < PRZZRowPlacement.span N d h j := by unfold PRZZRowPlacement.span; omega
    have hb := PRZZZeroExtension.supported (fun k => row N d j h m F0 Q t alpha (k+1))
      (PRZZRowWindow.lo h j-1) (PRZZRowPlacement.span N d h j) N hs
      (by unfold PRZZRowPlacement.span; omega)
      (by intro k hk; unfold row; rw [PRZZRowWindow.weight_eq N d h j hd hh]
          simp [PRZZMaskedVariation.mask,show ¬PRZZRowWindow.lo h j ≤ k+1 by omega])
      (by intro k hk; unfold row; rw [PRZZRowWindow.weight_eq N d h j hd hh]
          have hn : PRZZRowWindow.hi N d h j < k+1 := by unfold PRZZRowPlacement.span at hk; omega
          simp [PRZZMaskedVariation.mask,not_le.mpr hn])
    have he (k : ℕ) : PRZZRowWindow.lo h j-1+k+1=PRZZRowWindow.lo h j+k := by omega
    simp only [he,Nat.sub_add_cancel hl] at hb
    have hh' := PRZZZeroExtension.head_le
      (fun k => row N d j h m F0 Q t alpha (PRZZRowWindow.lo h j+k)) _ hs
    simp only [Nat.add_zero] at hh'
    have hv' := hv F0 hf0 N d j h m T Q t alpha hd hh hm hT hNT hne ha hz
    rw [← shift_eq] at hv'
    nlinarith
  · have he := PRZZRowPlacement.empty_row N d h j hd hh (lt_of_not_ge hne)
    simp only [row,he,Pi.zero_apply,mul_zero,variation,sub_self,norm_zero,sum_const_zero,add_zero]
    positivity

theorem free_variation (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eta S Z : ℝ)
    (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h e r m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 0 < e → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => freeWeight N d j h e r m F0 Q t alpha (k+1)) N ≤
        C*(1+|t|)*T^eta := by
  obtain ⟨C,hC,hv⟩ := log_full width jets hjets J eta S Z heta hS hZ
  refine ⟨3*C,by positivity,?_⟩
  intro F0 hf0 N d j h e r m T Q t alpha hd hh he hm hT hNT ha hz
  by_cases hN : N=0
  · subst N
    simp [variation,freeWeight,PRZZDyadic.cell]
    positivity
  have hN : 0 < N := Nat.pos_of_ne_zero hN
  let w := fun k => PRZZFreeLogCoprime.row N d j (h*e) m F0 Q t alpha (k+1)
  have hv' : variation w N ≤ C*(1+|t|)*T^eta :=
    hv F0 hf0 N d j (h*e) m T Q t alpha hd (Nat.mul_pos hh he) hm hT hNT ha hz
  have hwN : w N = 0 := by
    have hp : N < (h*e)*(N+1) := by nlinarith [Nat.mul_pos hh he]
    have hn : (h*e)*(N+1) ∉ PRZZDyadic.cell N j := by
      intro hn
      exact (not_le.mpr hp) (mem_Icc.mp (mem_filter.mp hn).1).2
    simp [w,PRZZFreeLogCoprime.row,PRZZResidualRow.weight,hn]
  have hw : ∀ k ≤ N, ‖w k‖ ≤ C*(1+|t|)*T^eta := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact (point_le w N k hk).trans hv'
    · rw [hwN,norm_zero]; positivity
  rw [dyadic_mask N d j h e r m F0 Q t alpha hN]
  exact (PRZZMaskedVariation.mask_of_variation _ _ N w _ _
    (by positivity) hw hv').trans_eq (by ring)

theorem transformed_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
(width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h e r m q : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ, ∀ k : ℤ,
      0 < d → 0 < h → 0 < e → m ≤ J → 1 ≤ q → (h*e).Coprime q →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖restrictedSum d q N
        ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
        (freeWeight N d j h e r m F0 Q t alpha)‖ ≤
      C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(k.natAbs.gcd q:ℝ)*
        (1+(endpoint N d h e r:ℝ)/q)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := supported_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := free_variation width jets hjets J eta S Z heta hS hZ
  refine ⟨Cw*Cv,by positivity,?_⟩
  intro F0 hf0 N d j h e r m q T Q t alpha k hd hh he hm hq hcop hT hNT ha hz
  have hb := hw d q N (endpoint N d h e r) hd.ne' hq (min_le_left _ _)
    ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
    (freeWeight N d j h e r m F0 Q t alpha)
    (vanishes N d j h e r m F0 Q t alpha hd hh he)
  rw [slice_frequency_gcd q h e (by omega) hcop k] at hb
  apply hb.trans
  have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
  exact (mul_le_mul_of_nonneg_left
    (hv F0 hf0 N d j h e r m T Q t alpha hd hh he hm hT hNT ha hz)
    (by positivity)).trans_eq (by ring)

#print axioms log_variation
#print axioms log_retained
#print axioms log_full
#print axioms free_variation
#print axioms transformed_bound
end XiPrime8845.PRZZClassFreeLength
