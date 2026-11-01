import PRZZTypeIVariation

/-! PRZZ section 4 Type I exponent sigma0-1/2-alpha-w.
For 1<=x<=T, sigma0<=1/2 and Re w>=0, a small real shift gives
P=exp(S), L=log T. The hypotheses are explicit, not contour suppliers.
The norm of the full exponent is retained in the variation budget. -/
noncomputable section
open scoped ContDiff
open Set
namespace XiPrime8845.PRZZSourceEnvelope
open PRZZTypeI PRZZTypeIWeights PRZZTypeIVariation PRZZMellinSeparation
set_option maxHeartbeats 2000000

def exponent (sigma : ℝ) (alpha w : ℂ) : ℂ := (sigma:ℂ)-1/2-alpha-w

theorem exponent_re (sigma S T : ℝ) (alpha w : ℂ)
    (hs : sigma ≤ 1/2) (hw : 0 ≤ w.re) (ha : |alpha.re| ≤ S/Real.log T) :
    (exponent sigma alpha w).re ≤ S/Real.log T := by
  simp only [exponent,Complex.sub_re,Complex.ofReal_re]
  norm_num
  linarith [(abs_le.mp ha).1]

theorem power_log (T S x : ℝ) (z : ℂ) (hT : 1 < T) (hS : 0 ≤ S)
    (hx : x ∈ Icc 1 T) (hz : z.re ≤ S/Real.log T) :
    ‖(x:ℂ)^z‖ ≤ Real.exp S ∧ |Real.log x| ≤ Real.log T := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hL := Real.log_pos hT
  have hl := Real.log_nonneg hx.1
  have hlt := Real.log_le_log hx0 hx.2
  refine ⟨?_,by rwa [abs_of_nonneg hl]⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hz hl
  have hh' := mul_le_mul_of_nonneg_right hlt (div_nonneg hS hL.le)
  have he : Real.log T*(S/Real.log T)=S := by field_simp
  exact hh.trans (hh'.trans_eq he)

def budget (C0 C1 S T : ℝ) (z : ℂ) (j : ℕ) : ℝ :=
  Real.exp S*(Real.log T)^j*C0+
    2*(Real.exp S*((‖z‖*(Real.log T)^j+(j:ℝ)*(Real.log T)^(j-1))*C0+(Real.log T)^j*C1))

theorem source_variation_uniform (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ T S N kappa a F sigma : ℝ,
      ∀ alpha w : ℂ, ∀ j H : ℕ,
      1 < T → 0 ≤ S → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      variation (fun k => sourceWeight (exponent sigma alpha w) j kappa
        (scaledCutoff F0 N) (a+k)) H ≤ budget C0 C1 S T (exponent sigma alpha w) j := by
  obtain ⟨C0,C1,h0,h1,h⟩ := source_variation F0 hf hc
  refine ⟨C0,C1,h0,h1,?_⟩
  intro T S N kappa a F sigma alpha w j H hT hS hF hFa ha haT hH hs hw halpha
  apply h N kappa a F (Real.exp S) (Real.log T) _ j H hF hFa
    (Real.exp_pos S).le (Real.log_pos hT).le hH
  intro x hx
  exact power_log T S x _ hT hS ⟨ha.trans hx.1,hx.2.trans haT⟩
    (exponent_re sigma S T alpha w hs hw halpha)

#print axioms exponent_re
/-- The actual sampled source weight is now inserted into Weil's
partial-summation adapter. No Weil proposition is installed as an axiom. -/
theorem source_weil (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (eps : ℝ) (heps : 0 < eps) (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) :
    ∃ K C0 C1 : ℝ, 0 < K ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ T S N kappa F sigma : ℝ, ∀ alpha w : ℂ, ∀ j H M q : ℕ, ∀ b : ℤ,
      1 < T → 0 ≤ S → 0 < F → F ≤ (M:ℝ)+1 → (M:ℝ)+1+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T → 1 ≤ q →
      ‖weightedSum q b M H (fun k => sourceWeight (exponent sigma alpha w) j kappa
        (scaledCutoff F0 N) ((M:ℝ)+1+k))‖ ≤
        (K*(q:ℝ)^(1/2+eps)*(b.natAbs.gcd q)*(1+(H:ℝ)/q))*
          budget C0 C1 S T (exponent sigma alpha w) j := by
  obtain ⟨K,hK,hk⟩ := weighted_bound hWeil eps heps
  obtain ⟨C0,C1,h0,h1,hv⟩ := source_variation_uniform F0 hf hc
  refine ⟨K,C0,C1,hK,h0,h1,?_⟩
  intro T S N kappa F sigma alpha w j H M q b hT hS hF hFM hMT hH hs hw ha hq
  apply (hk q hq b M H _).trans
  apply mul_le_mul_of_nonneg_left
    (hv T S N kappa ((M:ℝ)+1) F sigma alpha w j H hT hS hF hFM
      (by have := Nat.cast_nonneg (α := ℝ) M; linarith) hMT hH hs hw ha)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (Nat.cast_nonneg _))
    (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg q)))

#print axioms source_weil
#print axioms power_log
#print axioms source_variation_uniform
end XiPrime8845.PRZZSourceEnvelope
