import PRZZActualRowSmooth
import PRZZRowPlacement

/-! Analytic supplier for a free factor carrying log(n)^J. The multiplier
h may include the fixed complementary product. Both original sharp row
cutoffs are kept. Interval placement and the extra coprimality remain
separate from the incomplete Weil estimate below. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeLogRow
open PRZZMellinSeparation PRZZTypeIWeights PRZZSourceEnvelope PRZZMaskedVariation
set_option maxHeartbeats 2000000

def sample (N d j h a J : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ) (k : ℕ) : ℂ :=
  (Real.log ((a:ℝ)+k):ℂ)^J*
    PRZZResidualRow.weight N d j h (scaledCutoff F0 Q) alpha t (a+k)

theorem sample_eq (N d j h a J : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ)
    (hd : 0 < d) (hh : 0 < h) (ha : 1 ≤ a) (hai : a ≤ PRZZRowWindow.hi N d h j) :
    sample N d j h a J F0 Q t alpha = fun k =>
      (((h:ℂ)^alpha)⁻¹*twist h t)*
        mask (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
          (fun k => sourceWeight (exponent (1/2) alpha ((t:ℂ)*Complex.I)) J
            ((d:ℝ)*h) (scaledCutoff F0 Q) ((a:ℝ)+k)) k := by
  funext k
  unfold sample
  rw [congrFun (PRZZActualRowSmooth.sampled_eq N d j h a F0 Q t alpha hd hh ha hai) k]
  simp only [mask]
  split_ifs <;> simp only [sourceWeight,pow_zero,mul_one,mul_zero] <;> ring

/-- All degrees up to J share one constant chosen before the height,
fixed complementary product, cutoff scale and Mellin frequency. -/
theorem variation_bound (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h a H m : ℕ, ∀ T Q F t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ a → a ≤ PRZZRowWindow.hi N d h j → m ≤ J →
      1 < T → (h:ℝ) ≤ T → 0 < F → F ≤ a → (a:ℝ)+H ≤ T → (H:ℝ) ≤ 2*F →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (sample N d j h a m F0 Q t alpha) H ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := PRZZMaskedAbsorption.source_absorbed F0 hf hc J eps S Z heps hS hZ
  refine ⟨Real.exp S*C,by positivity,?_⟩
  intro N d j h a H m T Q F t alpha hd hh ha hai hm hT hhT hF hFa haT hH halpha hz
  rw [sample_eq N d j h a m F0 Q t alpha hd hh ha hai,PRZZActualRowSmooth.variation_const]
  have hv' := hv T Q ((d:ℝ)*h) a F (1/2) alpha ((t:ℂ)*Complex.I) m H
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

theorem weil_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h a H m q : ℕ, ∀ T Q F t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ a → a ≤ PRZZRowWindow.hi N d h j → m ≤ J → 1 ≤ q →
      1 < T → (h:ℝ) ≤ T → 0 < F → F ≤ a → (a:ℝ)+H ≤ T → (H:ℝ) ≤ 2*F →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → ∀ v : ℤ,
      ‖PRZZTypeI.weightedSum q v (a-1) H (sample N d j h a m F0 Q t alpha)‖ ≤
        C*Real.rpow q (1/2+eps)*(v.natAbs.gcd q)*(1+(H:ℝ)/q)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZTypeI.weighted_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := variation_bound F0 hf hc J eta S Z heta hS hZ
  refine ⟨Cw*Cv,mul_pos hCw hCv,?_⟩
  intro N d j h a H m q T Q F t alpha hd hh ha hai hm hq hT hhT hF hFa haT hH halpha hz v
  apply (hw q hq v (a-1) H _).trans
  have hp : 0 ≤ Cw*Real.rpow q (1/2+eps)*(v.natAbs.gcd q)*(1+(H:ℝ)/q) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCw.le
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _)) (by positivity)
  have hb := mul_le_mul_of_nonneg_left
    (hv N d j h a H m T Q F t alpha hd hh ha hai hm hT hhT hF hFa haT hH halpha hz)
    hp
  exact hb.trans_eq (by simp only [Real.rpow_eq_pow]; ring)

/-- A nonempty retained row also supplies the height room for the fixed
multiplier h (which may already include the complementary product). -/
theorem multiplier_le (N d h j a : ℕ) (hh : 0 < h) (ha : 1 ≤ a)
    (hai : a ≤ PRZZRowWindow.hi N d h j) : h ≤ N := by
  have ht : a ≤ N/h := hai.trans (min_le_left _ _)
  have hm := (Nat.le_div_iff_mul_le hh).mp ht
  nlinarith

theorem retained_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (sample N d j h (PRZZRowWindow.lo h j) m F0 Q t alpha)
        (PRZZRowPlacement.span N d h j) ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := variation_bound F0 hf hc J eps S Z heps hS hZ
  refine ⟨C,hC,?_⟩
  intro N d j h m T Q t alpha hd hh hm hT hNT hne ha hz
  have hp := PRZZRowPlacement.placement N d h j T hh hne hNT
  have hhN : (h:ℝ) ≤ N := by exact_mod_cast multiplier_le N d h j _ hh hp.1 hne
  exact hv N d j h _ _ m T Q (PRZZRowWindow.lo h j) t alpha hd hh hp.1 hne hm hT
    (by linarith) hp.2.1 le_rfl hp.2.2.1 hp.2.2.2 ha hz

#print axioms multiplier_le
#print axioms retained_variation
#print axioms sample_eq
#print axioms variation_bound
#print axioms weil_bound
end XiPrime8845.PRZZFreeLogRow
