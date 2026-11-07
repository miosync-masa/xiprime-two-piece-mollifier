import PRZZContourKernel

/-! Exact punctured-limit residues at the noncentral completed-zeta poles.
These are values, not height-uniform bounds or a contour-shift theorem.
Collision exclusions are explicit: no simple-pole claim at a collision. -/
noncomputable section
open Complex Filter Topology Set
namespace XiPrime8845.PRZZNoncentralResidues
open PRZZAFEDual PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

theorem shifted_residue_zero (z : ℂ) :
    Tendsto (fun s : ℂ => (s-(-z))*completedRiemannZeta (z+s))
      (𝓝[≠] (-z)) (𝓝 (-1)) := by
  let f : ℂ → ℂ := fun s => (s+z)*completedRiemannZeta₀ (z+s)-1-(s+z)/(1-(z+s))
  have hf : ContinuousAt f (-z) := by
    have hc : Continuous (fun s : ℂ => completedRiemannZeta₀ (z+s)) :=
      differentiable_completedZeta₀.continuous.comp (continuous_const.add continuous_id)
    unfold f
    fun_prop (disch := simp)
  have ht := hf.tendsto.mono_left (nhdsWithin_le_nhds (s := ({-z}ᶜ : Set ℂ)))
  have he : f (-z) = -1 := by simp [f]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : z+s ≠ 0 := by
    intro h
    have : s = -z := by linear_combination h
    exact hs this
  rw [completedRiemannZeta_eq]
  dsimp [f]
  field_simp
  <;> ring

theorem shifted_residue_one (z : ℂ) :
    Tendsto (fun s : ℂ => (s-(1-z))*completedRiemannZeta (z+s))
      (𝓝[≠] (1-z)) (𝓝 1) := by
  let f : ℂ → ℂ := fun s => (s-(1-z))*completedRiemannZeta₀ (z+s)-(s-(1-z))/(z+s)+1
  have hf : ContinuousAt f (1-z) := by
    have hc : Continuous (fun s : ℂ => completedRiemannZeta₀ (z+s)) :=
      differentiable_completedZeta₀.continuous.comp (continuous_const.add continuous_id)
    unfold f
    fun_prop (disch := ring_nf; norm_num)
  have ht := hf.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1-z}ᶜ : Set ℂ)))
  have he : f (1-z) = 1 := by simp [f]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : 1-(z+s) ≠ 0 := by
    intro h
    have : s = 1-z := by linear_combination -h
    exact hs this
  rw [completedRiemannZeta_eq]
  dsimp [f]
  field_simp
  <;> ring

def weight (sigma D s : ℂ) : ℂ := exp (s^2)*annihilator sigma s/(D*s)

theorem weight_continuous (sigma D p : ℂ) (hp : p ≠ 0) :
    ContinuousAt (weight sigma D) p := by
  have he : weight sigma D = fun s => (exp (s^2)*annihilator sigma s/D)/s := by
    funext s; unfold weight; ring
  rw [he]
  unfold annihilator
  fun_prop

/-- Two residue values for one factor, with the other factor regular.
Switching z and w supplies the other two crossed poles. -/
theorem product_residue_zero (z w sigma D : ℂ) (hz : z ≠ 0)
    (hw0 : w-z ≠ 0) (hw1 : w-z ≠ 1) :
    Tendsto (fun s : ℂ => (s-(-z))*(weight sigma D s*
      completedRiemannZeta (z+s)*completedRiemannZeta (w+s)))
      (𝓝[≠] (-z)) (𝓝 (-weight sigma D (-z)*completedRiemannZeta (w-z))) := by
  have hc : ContinuousAt (fun s : ℂ => completedRiemannZeta (w+s)) (-z) := by
    have h : ContinuousAt completedRiemannZeta (w+(-z)) := by
      simpa only [sub_eq_add_neg] using (differentiableAt_completedZeta hw0 hw1).continuousAt
    exact h.comp (continuousAt_const.add continuousAt_id)
  have h := (((weight_continuous sigma D (-z) (neg_ne_zero.mpr hz)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({-z}ᶜ : Set ℂ)))).mul (shifted_residue_zero z)).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1 <;> first | (funext s; ring) | (simp only [sub_eq_add_neg]; ring)

theorem product_residue_one (z w sigma D : ℂ) (hz : 1-z ≠ 0)
    (hw0 : w+(1-z) ≠ 0) (hw1 : w+(1-z) ≠ 1) :
    Tendsto (fun s : ℂ => (s-(1-z))*(weight sigma D s*
      completedRiemannZeta (z+s)*completedRiemannZeta (w+s)))
      (𝓝[≠] (1-z)) (𝓝 (weight sigma D (1-z)*completedRiemannZeta (w+(1-z)))) := by
  have hc : ContinuousAt (fun s : ℂ => completedRiemannZeta (w+s)) (1-z) :=
    (differentiableAt_completedZeta hw0 hw1).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have h := (((weight_continuous sigma D (1-z) hz).tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({1-z}ᶜ : Set ℂ)))).mul (shifted_residue_one z)).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1 <;> first | (funext s; ring) | ring

theorem contour_eq_product (a b s : ℂ) (t : ℝ) :
    contourNumerator a b s t/s = weight (a+b) (gammaPair a b t) s*
      completedRiemannZeta (leftArg a t+s)*completedRiemannZeta (rightArg b t+s) := by
  unfold contourNumerator completedPair weight
  ring

/-- Both factors are covered by the two possible orderings (z,w).
Thus the two conclusions give all four noncentral residues of the actual
contour, without an assumed residue formula. -/
theorem actual_residues (a b z w : ℂ) (t : ℝ)
    (hzw : (z = leftArg a t ∧ w = rightArg b t) ∨
      (z = rightArg b t ∧ w = leftArg a t))
    (hz : z ≠ 0) (hz1 : 1-z ≠ 0)
    (hw0 : w-z ≠ 0) (hw1 : w-z ≠ 1)
    (hw0' : w+(1-z) ≠ 0) (hw1' : w+(1-z) ≠ 1) :
    Tendsto (fun s : ℂ => (s-(-z))*(contourNumerator a b s t/s))
      (𝓝[≠] (-z)) (𝓝 (-weight (a+b) (gammaPair a b t) (-z)*completedRiemannZeta (w-z))) ∧
    Tendsto (fun s : ℂ => (s-(1-z))*(contourNumerator a b s t/s))
      (𝓝[≠] (1-z)) (𝓝 (weight (a+b) (gammaPair a b t) (1-z)*completedRiemannZeta (w+(1-z)))) := by
  have he (s : ℂ) : contourNumerator a b s t/s = weight (a+b) (gammaPair a b t) s*
      completedRiemannZeta (z+s)*completedRiemannZeta (w+s) := by
    rw [contour_eq_product]
    rcases hzw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  simp_rw [he]
  exact ⟨product_residue_zero z w _ _ hz hw0 hw1,
    product_residue_one z w _ _ hz1 hw0' hw1'⟩

/-- All collision exclusions above are supplied for the actual small-shift,
positive-height regime, before choosing either completed-zeta factor. -/
theorem arguments_separated (a b : ℂ) (t : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (ht : 1 ≤ t) (z w : ℂ)
    (hzw : (z = leftArg a t ∧ w = rightArg b t) ∨
      (z = rightArg b t ∧ w = leftArg a t)) :
    z ≠ 0 ∧ 1-z ≠ 0 ∧ w-z ≠ 0 ∧ w-z ≠ 1 ∧
      w+(1-z) ≠ 0 ∧ w+(1-z) ≠ 1 := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have ai := abs_le.mp ((abs_im_le_norm a).trans ha)
  have bi := abs_le.mp ((abs_im_le_norm b).trans hb)
  have hra : 0 < (leftArg a t).re ∧ (leftArg a t).re < 1 := by
    simp only [leftArg,add_re,div_ofNat_re,one_re,mul_re,ofReal_re,I_re,
      ofReal_im,I_im,mul_zero,zero_mul,sub_zero,add_zero]
    constructor <;> linarith
  have hrb : 0 < (rightArg b t).re ∧ (rightArg b t).re < 1 := by
    simp only [rightArg,sub_re,add_re,div_ofNat_re,one_re,mul_re,ofReal_re,I_re,
      ofReal_im,I_im,mul_zero,zero_mul,sub_zero]
    constructor <;> linarith
  have hi : (leftArg a t).im ≠ (rightArg b t).im := by
    simp only [leftArg,rightArg,sub_im,add_im,div_ofNat_im,one_im,zero_div,
      mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,zero_mul,add_zero,zero_add]
    linarith
  have hh (z w : ℂ) (hr : 0 < z.re ∧ z.re < 1) (hi : z.im ≠ w.im) :
      z ≠ 0 ∧ 1-z ≠ 0 ∧ w-z ≠ 0 ∧ w-z ≠ 1 ∧
        w+(1-z) ≠ 0 ∧ w+(1-z) ≠ 1 := by
    have hz : z ≠ 0 := by intro h; simp [h] at hr
    have hz1 : 1-z ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [sub_re,one_re,zero_re] at h'
      linarith [hr.2]
    have nonreal (v : ℂ) (hv : v.im ≠ 0) : v ≠ 0 ∧ v ≠ 1 := by
      constructor <;> intro h <;> apply hv <;> simp [h]
    have h1 := nonreal (w-z) (by simpa using sub_ne_zero.mpr hi.symm)
    have h2 := nonreal (w+(1-z)) (by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hi.symm)
    exact ⟨hz,hz1,h1.1,h1.2,h2.1,h2.2⟩
  rcases hzw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hh _ _ hra hi
  · exact hh _ _ hrb hi.symm

/-- All four actual noncentral residues with collision conditions supplied
from the small-shift regime, rather than passed as analytic hypotheses. -/
theorem small_shift_residues (a b : ℂ) (t : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (ht : 1 ≤ t) (z w : ℂ)
    (hzw : (z = leftArg a t ∧ w = rightArg b t) ∨
      (z = rightArg b t ∧ w = leftArg a t)) :
    Tendsto (fun s : ℂ => (s-(-z))*(contourNumerator a b s t/s))
      (𝓝[≠] (-z)) (𝓝 (-weight (a+b) (gammaPair a b t) (-z)*completedRiemannZeta (w-z))) ∧
    Tendsto (fun s : ℂ => (s-(1-z))*(contourNumerator a b s t/s))
      (𝓝[≠] (1-z)) (𝓝 (weight (a+b) (gammaPair a b t) (1-z)*completedRiemannZeta (w+(1-z)))) := by
  obtain ⟨hz,hz1,hw0,hw1,hw0',hw1'⟩ := arguments_separated a b t ha hb ht z w hzw
  exact actual_residues a b z w t hzw hz hz1 hw0 hw1 hw0' hw1'

#print axioms shifted_residue_zero
#print axioms shifted_residue_one
#print axioms weight_continuous
#print axioms product_residue_zero
#print axioms product_residue_one
#print axioms contour_eq_product
#print axioms actual_residues
#print axioms arguments_separated
#print axioms small_shift_residues
end XiPrime8845.PRZZNoncentralResidues
