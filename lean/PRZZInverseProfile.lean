import PRZZFrozenTail
import PRZZNormalizedTail

/-! Absorb the extra inverse spatial variable into a fixed cutoff profile.
The scale M^-1 is retained; the Fourier modulus must be transformed too. -/
noncomputable section
open scoped ContDiff FourierTransform
open Set Filter Topology MeasureTheory Complex
namespace XiPrime8845.PRZZInverseProfile
open PRZZFullWeightSmooth
set_option maxHeartbeats 3000000

def profile (F : ℝ → ℂ) (x : ℝ) : ℂ := F x/(x:ℂ)

theorem support (F : ℝ → ℂ) (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    Function.support (profile F) ⊆ Icc (1/2:ℝ) 3 := by
  intro x hx
  apply hs
  intro hf
  exact hx (by simp [profile,hf])

set_option backward.isDefEq.respectTransparency false in
theorem smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) : ContDiff ℝ ∞ (profile F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : profile F =ᶠ[𝓝 (0:ℝ)] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2)] with y hy
      have hf : F y = 0 := by
        by_contra hn
        have hh := hs hn
        linarith [hh.1]
      simp [profile,hf]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hr : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹) x := contDiffAt_id.inv hx
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => (y⁻¹:ℝ):ℝ → ℂ) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
    convert hF.contDiffAt.mul hc using 1 <;> try rfl
    funext y
    change F y/(y:ℂ) = F y*((y⁻¹:ℝ):ℂ)
    rw [Complex.ofReal_inv,div_eq_mul_inv]

theorem compact (F : ℝ → ℂ) (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    HasCompactSupport (profile F) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (support F hs hn)

/-- All derivative constants are fixed before the dilation scale. -/
theorem jets (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M x : ℝ, 0 < M →
      ‖iteratedDeriv n (PRZZMellinSeparation.scaledCutoff (profile F) M) x‖ ≤ C/M^n :=
  PRZZCutoffJets.ordinary_uniform (profile F) (smooth F hF hs) (compact F hs) n

theorem weight_absorb_pos (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ)
    (x : ℝ) (hM : 0 < M) (hx : 0 < x) :
    weight F M k omega (z+1) sigma x =
      ((M⁻¹:ℝ):ℂ)*weight (profile F) M k omega z sigma x := by
  have he : Complex.exp (-(Real.log x:ℂ)) = (x:ℂ)⁻¹ := by
    rw [Complex.exp_neg,← Complex.ofReal_exp,Real.exp_log hx]
  unfold weight profile
  rw [show -(z+1)*(Real.log x:ℂ) = -z*(Real.log x:ℂ) + -(Real.log x:ℂ) by ring,
    Complex.exp_add,he]
  push_cast
  have hm : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp

theorem weight_absorb (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ)
    (hM : 0 < M) (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (x : ℝ) :
    weight F M k omega (z+1) sigma x =
      ((M⁻¹:ℝ):ℂ)*weight (profile F) M k omega z sigma x := by
  by_cases hx : 0 < x
  · exact weight_absorb_pos F M k omega z sigma x hM hx
  · have hf : F (M⁻¹*x) = 0 := by
      by_contra hn
      have hh := (hs hn).1
      have hneg := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hM.le) (le_of_not_gt hx)
      linarith
    simp [weight,profile,hf]

theorem fourier_absorb (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ)
    (hM : 0 < M) (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (ξ : ℝ) :
    𝓕 (weight F M k omega (z+1) sigma) ξ =
      ((M⁻¹:ℝ):ℂ)*𝓕 (weight (profile F) M k omega z sigma) ξ := by
  rw [Real.fourier_eq',Real.fourier_eq',← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [weight_absorb F M k omega z sigma hM hs x]
  simp only [smul_eq_mul]
  ring

/-- Actual frozen Fourier weight, now with a small shift exponent and
the inverse spatial factor fully absorbed into the fixed profile. -/
theorem frozen_profile_fourier (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t ξ : ℝ) (hM : 0 < M) (hm : 0 < z.1.2)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) ξ =
      (Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ))/(M:ℂ)) *
        𝓕 (weight (profile F) M (2*Real.pi*z.1.1/(t*z.1.2))
          ((z.2.1:ℝ)*t/z.1.1) (alpha+beta) sigma) (ξ/z.1.2) := by
  rw [PRZZFrozenTail.frozen_fourier F M z alpha beta sigma t ξ hM hm hs,
    fourier_absorb F M _ _ (alpha+beta) sigma hM hs]
  push_cast
  ring

/-- The original q^-1 normalization is retained although the transformed
Fourier modulus is q*v. All inverse-profile derivative inputs are supplied.
The explicit v/M factor is not silently absorbed into a constant. -/
theorem uniform_transformed_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (M k omega R q v Z P s : ℝ) (z sigma : ℂ),
      0 < M → 0 < k → 0 ≤ R → 0 < q → 0 < v → sigma ≠ 0 →
      0 ≤ Z → ‖z‖ ≤ Z → ‖z‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤ P →
      1/‖sigma‖^2 ≤ s → (∀ x ∈ Icc (M/2) (3*M), |omega/x| ≤ R) →
      let f := weight F M k omega (z+1) sigma
      let B := (3*M-M/2)*(PRZZJetUniform.uniformCap C D E a k M R Z P s (n+2)/(M/2)^(n+2))
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/(q*v))‖+‖𝓕 f (-(((H+j:ℝ)+1)/(q*v)))‖
      Summable tail ∧ (∑' j, q⁻¹*tail j) ≤
        (v/M)*(2*B*(q*v)^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass) := by
  obtain ⟨C,D,E,hpos,h⟩ := PRZZNormalizedTail.uniform_tail (profile F)
    (smooth F hF hs) (support F hs) a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H M k omega R q v Z P s z sigma hM hk hR hq hv hsig hZ hz hP hsigma hp
  have ht := h n H M k omega R (q*v) Z P s z sigma hM hk hR (mul_pos hq hv)
    hsig hZ hz hP hsigma hp
  dsimp only at ht ⊢
  let g := weight (profile F) M k omega z sigma
  let tg := fun j : ℕ => ‖𝓕 g (((H+j:ℝ)+1)/(q*v))‖+‖𝓕 g (-(((H+j:ℝ)+1)/(q*v)))‖
  have he : ∀ ξ : ℝ, ‖𝓕 (weight F M k omega (z+1) sigma) ξ‖ = M⁻¹*‖𝓕 g ξ‖ := by
    intro ξ
    rw [fourier_absorb F M k omega z sigma hM hs ξ,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hM)]
  constructor
  · simp_rw [he]
    simpa only [mul_add] using ht.1.mul_left (M⁻¹)
  · simp_rw [he]
    have heq : (fun j : ℕ => q⁻¹*(M⁻¹*‖𝓕 g (((H+j:ℝ)+1)/(q*v))‖+
        M⁻¹*‖𝓕 g (-(((H+j:ℝ)+1)/(q*v)))‖)) =
        (fun j => (v/M)*((q*v)⁻¹*tg j)) := by
      funext j
      dsimp [tg]
      field_simp
    rw [heq,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left ht.2 (by positivity)

/-- Rounding the transformed cutoff supplies the IBP gain, with no
per-row cutoff inequality assumed. The original cutoff is multiplied by v. -/
theorem rounded_cutoff_gain (d T M Q e v : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hv : 0 < v) :
    Q*v/(d*M*((⌈v*PRZZSourceCutoffs.poissonCutoff d T M Q e⌉₊:ℝ)+1)) ≤ T^(-e) := by
  let H : ℕ := ⌈v*PRZZSourceCutoffs.poissonCutoff d T M Q e⌉₊
  have hcut : PRZZSourceCutoffs.poissonCutoff d T M Q e ≤ ((H:ℝ)+1)/v := by
    apply (le_div_iff₀ hv).mpr
    have hh := Nat.le_ceil (v*PRZZSourceCutoffs.poissonCutoff d T M Q e)
    dsimp only [H]
    nlinarith
  have hh := PRZZSourceCutoffs.tail_ratio d T M Q e 0 (((H:ℝ)+1)/v) hd hT hM hQ hcut
  simp only [Real.rpow_zero,mul_one,zero_sub] at hh
  convert hh using 1 <;> dsimp only [H] <;> field_simp

/-- Substitute the rounded transformed cutoff into the complete scalar
tail budget. B is the explicit derivative mass in uniform_transformed_tail;
no claim that the remaining v/M cost is height independent is made. -/
theorem rounded_tail_budget (n : ℕ) (B T M q e v : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hM : 0 < M) (hq : 0 < q) (hv : 0 < v) :
    let H : ℕ := ⌈v*PRZZSourceCutoffs.poissonCutoff 1 T M q e⌉₊
    (v/M)*(2*B*(q*v)^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*
      PRZZWeightTail.squareMass) ≤
    (v/M)*(2*B*(q*v)*(M*T^(-e))^n/(2*Real.pi)^(n+2)*
      PRZZWeightTail.squareMass) := by
  dsimp only
  let H : ℕ := ⌈v*PRZZSourceCutoffs.poissonCutoff 1 T M q e⌉₊
  have hh := rounded_cutoff_gain 1 T M q e v (by norm_num) hT hM hq hv
  simp only [one_mul] at hh
  have hH : 0 < (H:ℝ)+1 := by positivity
  have hg : q*v/((H:ℝ)+1) ≤ M*T^(-e) := by
    apply (div_le_iff₀ hH).mpr
    have hh' := (div_le_iff₀ (mul_pos hM hH)).mp hh
    nlinarith only [hh']
  have hm : 0 ≤ PRZZWeightTail.squareMass := by
    unfold PRZZWeightTail.squareMass
    positivity
  calc
    _ = (v/M)*(2*B*(q*v)*(q*v/((H:ℝ)+1))^n/(2*Real.pi)^(n+2)*
        PRZZWeightTail.squareMass) := by
      rw [div_pow,pow_succ]
      ring
    _ ≤ _ := by gcongr

#print axioms rounded_tail_budget
#print axioms rounded_cutoff_gain
#print axioms frozen_profile_fourier
#print axioms uniform_transformed_tail
#print axioms support
#print axioms smooth
#print axioms compact
#print axioms jets
#print axioms weight_absorb_pos
#print axioms weight_absorb
#print axioms fourier_absorb
end XiPrime8845.PRZZInverseProfile
