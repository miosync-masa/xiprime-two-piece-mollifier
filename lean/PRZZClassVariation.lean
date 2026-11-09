import PRZZClassSources

/-! Common dimensionless jets control the actual sharp-masked residual
row, including zero extension and empty rows, before the cutoff is chosen.
The fixed plateau partition is not generalized. Full Type I/AFE assembly
is a further step; no full profile moment bound is asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex
namespace XiPrime8845.PRZZClassVariation
open PRZZTypeI PRZZTypeIWeights PRZZTypeIVariation PRZZMellinSeparation
open PRZZSourceEnvelope PRZZMaskedVariation PRZZActualRowSmooth
open PRZZSmoothWeights PRZZRowWindow PRZZRowPlacement
set_option maxHeartbeats 8000000

theorem cutoff_bounds (width : ℝ) (jets : ℕ → ℝ) (F0 : ℝ → ℂ)
    (hf : PRZZProfileMellin.Member width jets F0) (N x : ℝ) :
    ‖scaledCutoff F0 N x‖ ≤ jets 0 ∧
      ‖(x:ℂ)*deriv (scaledCutoff F0 N) x‖ ≤ jets 1 := by
  refine ⟨PRZZClassSources.member_sup width jets F0 hf _,?_⟩
  rw [scaled_deriv F0 hf.smooth N x]
  have he : (x:ℂ)*((N⁻¹:ℝ) • deriv F0 (N⁻¹*x)) =
      (N⁻¹*x:ℝ)*deriv F0 (N⁻¹*x) := by
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he]
  simpa using hf.jet_bound 1 (N⁻¹*x)

theorem source_variation (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N kappa a F P L : ℝ,
      ∀ z : ℂ, ∀ j H : ℕ, 0 < F → F ≤ a → 0 ≤ P → 0 ≤ L → (H:ℝ) ≤ 2*F →
      (∀ x ∈ Icc a (a+H), ‖(x:ℂ)^z‖ ≤ P ∧ |Real.log x| ≤ L) →
      variation (fun k => sourceWeight z j kappa (scaledCutoff F0 N) (a+k)) H ≤
        P*L^j*(jets 0)+2*(P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*(jets 0)+L^j*(jets 1))) := by
  let C0 := jets 0
  let C1 := jets 1
  have hC0 := hj 0
  have hC1 := hj 1
  intro F0 hf
  have hcut := cutoff_bounds width jets F0 hf
  intro N kappa a F P L z j H hF ha hP hL hH henv
  let w := sourceWeight z j kappa (scaledCutoff F0 N)
  let D := P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hder (x : ℝ) (hx : x ∈ Icc a (a+H)) : HasDerivAt w (deriv w x) x := by
    have hx0 : 0 < x := hF.trans_le (ha.trans hx.1)
    exact (source_hasDerivAt z j kappa x _ _ hx0
      ((scaled_hasDerivAt F0 hf.smooth N (kappa*x)).differentiableAt.hasDerivAt)).differentiableAt.hasDerivAt
  apply PRZZTypeIVariation.sampled_variation w a F (P*L^j*C0) D H hF hD hH
  · have hx : a+(H-1:ℕ) ∈ Icc a (a+H) := by
      constructor
      · have := Nat.cast_nonneg (α := ℝ) (H-1); linarith
      · have hh : ((H-1:ℕ):ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
        linarith
    dsimp [w,sourceWeight]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (henv _ hx).1
      (pow_le_pow_left₀ (abs_nonneg _) (henv _ hx).2 j) (by positivity) hP)
      (hcut N (kappa*(a+(H-1:ℕ)))).1 (norm_nonneg _) (by positivity)
  · exact hder
  · intro x hx
    have hx0 : 0 < x := hF.trans_le (ha.trans hx.1)
    have hd := source_hasDerivAt z j kappa x _ _ hx0
      ((scaled_hasDerivAt F0 hf.smooth N (kappa*x)).differentiableAt.hasDerivAt)
    have hb := source_derivative_bound z j kappa x _ _ P L C0 C1 hx0 hP hL hC0 hC1
      (henv x hx).1 (henv x hx).2 (hcut N (kappa*x)).1
      (by simpa only [Complex.ofReal_mul] using (hcut N (kappa*x)).2)
    rw [← hd.deriv] at hb
    change ‖(x:ℂ)*deriv w x‖ ≤ D at hb
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0] at hb
    apply (le_div_iff₀ hF).mpr
    nlinarith [norm_nonneg (deriv w x),ha.trans hx.1]

theorem source_variation_uniform (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ T S N kappa a F sigma : ℝ,
      ∀ alpha w : ℂ, ∀ j H : ℕ,
      1 < T → 0 ≤ S → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      variation (fun k => sourceWeight (exponent sigma alpha w) j kappa
        (scaledCutoff F0 N) (a+k)) H ≤ budget (jets 0) (jets 1) S T (exponent sigma alpha w) j := by
  intro F0 hf
  have h := source_variation width jets hj F0 hf
  intro T S N kappa a F sigma alpha w j H hT hS hF hFa ha haT hH hs hw halpha
  apply h N kappa a F (Real.exp S) (Real.log T) _ j H hF hFa
    (Real.exp_pos S).le (Real.log_pos hT).le hH
  intro x hx
  exact power_log T S x _ hT hS ⟨ha.trans hx.1,hx.2.trans haT⟩
    (exponent_re sigma S T alpha w hs hw halpha)

theorem masked_source_uniform (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ T S N kappa a F sigma : ℝ, ∀ alpha w : ℂ, ∀ j H lo hi : ℕ,
      1 < T → 0 ≤ S → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      PRZZTypeI.variation (mask lo hi
        (fun k => sourceWeight (exponent sigma alpha w) j kappa (scaledCutoff F0 N) (a+k))) H ≤
      budget (jets 0) (jets 1) S T (exponent sigma alpha w) j+2*(Real.exp S*(Real.log T)^j*(jets 0)) := by
  intro F0 hf
  let C0 := jets 0
  let C1 := jets 1
  let C2 := jets 0
  have h2 := hj 0
  have hv := source_variation_uniform width jets hj F0 hf
  have hcut := cutoff_bounds width jets F0 hf
  intro T S N kappa a F sigma alpha w j H lo hi hT hS hF hFa ha haT hH hs hw halpha
  have hL : 0 ≤ Real.log T := (Real.log_pos hT).le
  apply mask_of_variation lo hi H _ (Real.exp S*(Real.log T)^j*C2) _ (by positivity) _
    (hv T S N kappa a F sigma alpha w j H hT hS hF hFa ha haT hH hs hw halpha)
  intro k hk
  have hkR : (k:ℝ) ≤ H := by exact_mod_cast hk
  have hx : a+k ∈ Icc 1 T := ⟨by have := Nat.cast_nonneg (α := ℝ) k; linarith, by linarith⟩
  have he := power_log T S (a+k) (exponent sigma alpha w) hT hS hx
    (exponent_re sigma S T alpha w hs hw halpha)
  unfold sourceWeight
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul he.1
    (pow_le_pow_left₀ (abs_nonneg _) he.2 j) (by positivity) (Real.exp_pos S).le)
    (hcut N (kappa*(a+k))).1 (norm_nonneg _) (by positivity)

theorem source_absorbed (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ T N kappa a F sigma : ℝ, ∀ alpha w : ℂ, ∀ j H lo hi : ℕ,
      1 < T → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      |sigma|+1/2+‖alpha‖ ≤ Z → j ≤ J →
      PRZZTypeI.variation (PRZZMaskedVariation.mask lo hi
        (fun k => sourceWeight (exponent sigma alpha w) j kappa (scaledCutoff F0 N) (a+k))) H ≤
      C*(1+‖w‖)*T^eps := by
  let C0 := jets 0
  let C1 := jets 1
  let C2 := jets 0
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 0
  obtain ⟨B,hB,hb⟩ := PRZZSourceAbsorption.budget_absorbed J eps C0 C1 S (Z+1)
    heps h0 h1 (by positivity)
  obtain ⟨D,hD,hd⟩ := PRZZSourceAbsorption.finite_log_powers J eps heps
  refine ⟨B+2*Real.exp S*D*C2,by positivity,?_⟩
  have hjets := hj
  intro F0 hf T N kappa a F sigma alpha w j H lo hi hT hF hFa ha haT hH hs hw halpha hz hj
  have hv := masked_source_uniform width jets hjets F0 hf
  apply (hv T S N kappa a F sigma alpha w j H lo hi hT hS hF hFa ha haT hH hs hw halpha).trans
  have hb' := hb T hT _ w j hj (PRZZSourceAbsorption.exponent_norm sigma Z alpha w hz)
  have ht : 0 ≤ T^eps := Real.rpow_nonneg (by linarith) _
  have hh : 2*(Real.exp S*(Real.log T)^j*C2) ≤
      (2*Real.exp S*D*C2)*(1+‖w‖)*T^eps := by
    calc
      _ ≤ 2*(Real.exp S*(D*T^eps)*C2) := by gcongr; exact hd T hT.le j hj
      _ ≤ _ := by nlinarith [norm_nonneg w, mul_nonneg (by positivity : 0 ≤ 2*Real.exp S*D*C2) ht]
  exact (add_le_add hb' hh).trans_eq (by ring)

theorem sampled_variation (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d j h a H : ℕ, ∀ T Q F t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ a → a ≤ PRZZRowWindow.hi N d h j →
      1 < T → (h:ℝ) ≤ T → 0 < F → F ≤ a → (a:ℝ)+H ≤ T → (H:ℝ) ≤ 2*F →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      PRZZTypeI.variation (fun k => PRZZResidualRow.weight N d j h
        (scaledCutoff F0 Q) alpha t (a+k)) H ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := source_absorbed width jets hj 0 eps S Z heps hS hZ
  refine ⟨Real.exp S*C,by positivity,?_⟩
  intro F0 hf N d j h a H T Q F t alpha hd hh ha hai hT hhT hF hFa haT hH halpha hz
  rw [sampled_eq N d j h a F0 Q t alpha hd hh ha hai,variation_const]
  have hv' := hv F0 hf T Q ((d:ℝ)*h) a F (1/2) alpha ((t:ℂ)*Complex.I) 0 H
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

theorem retained_variation (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d h j : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      lo h j ≤ hi N d h j →
      PRZZTypeI.variation (fun k => PRZZResidualRow.weight N d j h
        (scaledCutoff F0 Q) alpha t (lo h j+k)) (span N d h j) ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := sampled_variation width jets hj eps S Z heps hS hZ
  refine ⟨C,hC,?_⟩
  intro F0 hf N d h j T Q t alpha hd hh hT hNT hhT ha hz hne
  have hp := placement N d h j T hh hne hNT
  exact hv F0 hf N d j h (lo h j) (span N d h j) T Q (lo h j) t alpha hd hh hp.1 hne
    hT hhT hp.2.1 le_rfl hp.2.2.1 hp.2.2.2 ha hz

theorem full_variation (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d h j : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => PRZZResidualRow.weight N d j h
        (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (k+1)) N ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := retained_variation width jets hj eps S Z heps hS hZ
  refine ⟨2*C,by positivity,?_⟩
  intro F0 hf N d h j T Q t alpha hd hh hT hNT hhT ha hz
  by_cases hne : PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j
  · exact (PRZZZeroExtension.actual N d h j _ alpha t hd hh hne).trans
      ((mul_le_mul_of_nonneg_left (hv F0 hf N d h j T Q t alpha hd hh hT hNT hhT ha hz hne)
        (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
  · rw [PRZZRowPlacement.empty_row N d h j hd hh (lt_of_not_ge hne)]
    simp only [Pi.zero_apply,sub_self,norm_zero,sum_const_zero,add_zero,variation]
    positivity

theorem weil_row (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 → ∀ N d h j q : ℕ, ∀ a : ℤ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ q → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖weightedSum q a 0 N (fun k => PRZZResidualRow.weight N d j h
        (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (k+1))‖ ≤
      C*Real.rpow q (1/2+eta)*(a.natAbs.gcd q)*(1+(N:ℝ)/q)*(1+|t|)*T^eps := by
  obtain ⟨Cw,hCw,hw⟩ := weighted_bound hWeil eta heta
  obtain ⟨Cv,hCv,hv⟩ := full_variation width jets hj eps S Z heps hS hZ
  refine ⟨Cw*Cv,by positivity,?_⟩
  intro F0 hf N d h j q a T Q t alpha hd hh hq hT hNT hhT ha hz
  apply (hw q hq a 0 N _).trans
  exact (mul_le_mul_of_nonneg_left (hv F0 hf N d h j T Q t alpha hd hh hT hNT hhT ha hz)
    (mul_nonneg (mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (Nat.cast_nonneg _)) (by positivity))).trans_eq (by simp only [Real.rpow_eq_pow]; ring)

#print axioms cutoff_bounds
#print axioms source_variation
#print axioms source_variation_uniform
#print axioms masked_source_uniform
#print axioms source_absorbed
#print axioms sampled_variation
#print axioms retained_variation
#print axioms full_variation
#print axioms weil_row
end XiPrime8845.PRZZClassVariation
