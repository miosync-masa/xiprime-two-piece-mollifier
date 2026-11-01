import PRZZMaskedAbsorption
import PRZZSmallRowVariation

/-! Exact smooth-weight identification on a sampled interval of the actual
row. The shifted integer mask retains both original cutoffs. Interval
placement is explicit; no full-height variation estimate is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualRowSmooth
open PRZZMellinSeparation PRZZTypeIWeights PRZZSourceEnvelope PRZZMaskedVariation
set_option maxHeartbeats 2000000

theorem analytic_factor (F0 : ℝ → ℂ) (Q d h x t : ℝ) (alpha : ℂ)
    (hh : 0 < h) (hx : 0 < x) :
    scaledCutoff F0 Q (d*(h*x))/((h*x:ℝ):ℂ)^alpha*twist (h*x) t =
      ((h:ℂ)^alpha)⁻¹*twist h t *
        sourceWeight (exponent (1/2) alpha ((t:ℂ)*Complex.I)) 0 (d*h)
          (scaledCutoff F0 Q) x := by
  have hn : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [sourceWeight,pow_zero,mul_one,exponent,
    show ((1/2:ℝ):ℂ)-(1/2:ℂ)=0 by push_cast; ring,zero_sub]
  rw [Complex.cpow_sub _ _ hn]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hh.le hx.le,twist_mul h x t hh.le hx.le]
  simp only [twist,Complex.cpow_neg,mul_inv_rev,div_eq_mul_inv]
  rw [show d*(h*x)=d*h*x by ring]
  ring

theorem variation_const (c : ℂ) (w : ℕ → ℂ) (H : ℕ) :
    PRZZTypeI.variation (fun k => c*w k) H = ‖c‖*PRZZTypeI.variation w H := by
  simp only [PRZZTypeI.variation,← mul_sub,norm_mul,mul_add,mul_sum]

theorem sampled_eq (N d j h a : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ)
    (hd : 0 < d) (hh : 0 < h) (ha : 1 ≤ a) (hai : a ≤ PRZZRowWindow.hi N d h j) :
    (fun k => PRZZResidualRow.weight N d j h (scaledCutoff F0 Q) alpha t (a+k)) =
      fun k => (((h:ℂ)^alpha)⁻¹*twist h t) *
        mask (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
          (fun k => sourceWeight (exponent (1/2) alpha ((t:ℂ)*Complex.I)) 0
            ((d:ℝ)*h) (scaledCutoff F0 Q) ((a:ℝ)+k)) k := by
  funext k
  rw [PRZZRowWindow.weight_eq N d h j hd hh]
  have he : (PRZZRowWindow.lo h j ≤ a+k ∧ a+k ≤ PRZZRowWindow.hi N d h j) ↔
      PRZZRowWindow.lo h j-a ≤ k ∧ k ≤ PRZZRowWindow.hi N d h j-a := by omega
  simp only [mask,he]
  split_ifs
  · push_cast
    simpa only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast] using
      analytic_factor F0 Q d h (a+k) t alpha (by exact_mod_cast hh)
      (by have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
          have hk' : (0:ℝ) ≤ k := Nat.cast_nonneg k
          linarith)
  · simp

#print axioms analytic_factor
#print axioms variation_const
#print axioms sampled_eq

/-- Insert the literal source row, including its h-dependent scalar and
shifted sharp mask, into the proved smooth subpower bound. -/
theorem sampled_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h a H : ℕ, ∀ T Q F t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ a → a ≤ PRZZRowWindow.hi N d h j →
      1 < T → (h:ℝ) ≤ T → 0 < F → F ≤ a → (a:ℝ)+H ≤ T → (H:ℝ) ≤ 2*F →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (fun k => PRZZResidualRow.weight N d j h
        (scaledCutoff F0 Q) alpha t (a+k)) H ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := PRZZMaskedAbsorption.source_absorbed F0 hf hc 0 eps S Z heps hS hZ
  refine ⟨Real.exp S*C,by positivity,?_⟩
  intro N d j h a H T Q F t alpha hd hh ha hai hT hhT hF hFa haT hH halpha hz
  rw [sampled_eq N d j h a F0 Q t alpha hd hh ha hai,variation_const]
  have hv' := hv T Q ((d:ℝ)*h) a F (1/2) alpha ((t:ℂ)*Complex.I) 0 H
    (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
    hT hF hFa (by exact_mod_cast ha) haT hH le_rfl
    (by simp) halpha (by norm_num; linarith) le_rfl
  have hb : ‖((h:ℂ)^alpha)⁻¹*twist h t‖ ≤ Real.exp S := by
    rw [norm_mul,twist_norm _ _ (by exact_mod_cast hh),mul_one]
    exact PRZZSourceCoefficients.inverse_shift T S h alpha hT hS
      ⟨by exact_mod_cast hh,hhT⟩ halpha
  have hn : 0 ≤ C*(1+‖(t:ℂ)*Complex.I‖)*T^eps := by positivity
  have hv0 : 0 ≤ PRZZTypeI.variation
      (mask (PRZZRowWindow.lo h j-a) (PRZZRowWindow.hi N d h j-a)
        (fun k => sourceWeight (exponent (1/2) alpha ((t:ℂ)*Complex.I)) 0
          ((d:ℝ)*h) (scaledCutoff F0 Q) ((a:ℝ)+k))) H := by
    unfold PRZZTypeI.variation; positivity
  have he := mul_le_mul hb hv' hv0 (Real.exp_pos S).le
  simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,mul_assoc] using he

#print axioms sampled_variation

/-- The small-scale constant is also uniform in the scale Q of F0. -/
theorem small_scaled (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (S c : ℝ) (hS : 0 ≤ S) (hc0 : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d j h H : ℕ, ∀ T Q t U : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ) ≤ T → |alpha.re| ≤ S/Real.log T →
      U ≤ c → (PRZZRowWindow.hi N d h j:ℝ) ≤ c*U →
      PRZZTypeI.variation (fun k => PRZZResidualRow.weight N d j h
        (scaledCutoff F0 Q) alpha t (k+1)) H ≤ C := by
  obtain ⟨C0,C1,h0,h1,hb⟩ := PRZZSmoothWeights.cutoff_bounds F0 hf hc
  refine ⟨(1+2*(⌊c^2⌋₊:ℝ))*(C0*Real.exp S),by positivity,?_⟩
  intro N d j h H T Q t U alpha hd hh hT hNT halpha hU hi
  apply PRZZSmallRowVariation.supported_variation _ ⌊c^2⌋₊ H _ (by positivity)
  · intro n
    unfold PRZZResidualRow.weight
    split_ifs with hm
    · have hn := (PRZZDyadic.mem_cell N j (h*n)).mp hm.1
      have hp : 0 < h*n := (mem_Icc.mp hn.1).1
      have hx : (h*n:ℝ) ∈ Set.Icc 1 T := ⟨by exact_mod_cast hp,
        (by exact_mod_cast (mem_Icc.mp hn.1).2 : (h*n:ℝ) ≤ N).trans hNT⟩
      have hz := PRZZSourceCoefficients.inverse_shift T S (h*n) alpha hT hS hx halpha
      rw [div_eq_mul_inv,norm_mul,norm_mul,twist_norm _ _ (by exact_mod_cast hp),mul_one]
      exact mul_le_mul (hb Q _).1
        (by simpa only [Nat.cast_mul,Complex.ofReal_mul,Complex.ofReal_natCast] using hz)
        (norm_nonneg _) h0
    · simp only [norm_zero]; positivity
  · intro n hn
    have hhi := PRZZSmallRowVariation.small_scale _ c U hc0 hU hi
    rw [PRZZRowWindow.weight_eq N d h j hd hh]
    simp [mask,not_le.mpr (lt_of_le_of_lt hhi hn)]

#print axioms small_scaled

def selected (N d j h a : ℕ) (F0 : ℝ → ℂ) (Q t U c : ℝ) (alpha : ℂ) : ℕ → ℂ :=
  if U ≤ c then fun k => PRZZResidualRow.weight N d j h (scaledCutoff F0 Q) alpha t (k+1)
  else fun k => PRZZResidualRow.weight N d j h (scaledCutoff F0 Q) alpha t (a+k)

/-- Both scale cases use one constant before all height, window and h choices.
The large-case sampling conditions remain explicit for the dyadic supplier. -/
theorem selected_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (eps S Z c : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hc0 : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h a H : ℕ, ∀ T Q F t U : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ) ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      (U ≤ c → (PRZZRowWindow.hi N d h j:ℝ) ≤ c*U) →
      (c < U → 1 ≤ a ∧ a ≤ PRZZRowWindow.hi N d h j ∧
        0 < F ∧ F ≤ a ∧ (a:ℝ)+H ≤ T ∧ (H:ℝ) ≤ 2*F) →
      PRZZTypeI.variation (selected N d j h a F0 Q t U c alpha) H ≤
        C*(1+|t|)*T^eps := by
  obtain ⟨Cs,hCs,hs⟩ := small_scaled F0 hf hc S c hS hc0
  obtain ⟨Cl,hCl,hl⟩ := sampled_variation F0 hf hc eps S Z heps hS hZ
  refine ⟨Cs+Cl,by positivity,?_⟩
  intro N d j h a H T Q F t U alpha hd hh hT hNT hhT ha hz hsmall hlarge
  unfold selected
  split_ifs with hU
  · have hv := hs N d j h H T Q t U alpha hd hh hT hNT ha hU (hsmall hU)
    have ht : 1 ≤ T^eps := Real.one_le_rpow hT.le heps.le
    have hb : Cs ≤ (Cs+Cl)*(1+|t|)*T^eps := by
      calc
        Cs ≤ Cs+Cl := by linarith
        _ ≤ (Cs+Cl)*(1+|t|) := le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg t])
        _ ≤ _ := le_mul_of_one_le_right (by positivity) ht
    exact hv.trans hb
  · obtain ⟨ha1,hai,hF,hFa,haT,hH⟩ := hlarge (lt_of_not_ge hU)
    exact (hl N d j h a H T Q F t alpha hd hh ha1 hai hT hhT hF hFa haT hH ha hz).trans
      (by gcongr; exact le_add_of_nonneg_left hCs)

#print axioms selected_variation
end XiPrime8845.PRZZActualRowSmooth
