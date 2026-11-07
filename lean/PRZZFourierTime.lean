import PRZZArithmeticFourierTail

/-! Time measurability of the literal Fourier weight. Measurability uses
the defining contour integral, not an assumed extension across x=0. -/
noncomputable section
open scoped FourierTransform ContDiff RealInnerProductSpace
open MeasureTheory Set Complex
namespace XiPrime8845.PRZZFourierTime
set_option maxHeartbeats 3000000

theorem source_measurable (sigma : ℂ) :
    StronglyMeasurable (PRZZDyadicEnvelope.sourceW sigma) := by
  have h : Measurable (fun p : ℝ × ℝ =>
      (p.1:ℂ)^(-(2+(p.2:ℂ)*I))*Complex.exp ((2+(p.2:ℂ)*I)^2)*
        PRZZDyadicEnvelope.annihilator sigma (2+(p.2:ℂ)*I)/(2+(p.2:ℂ)*I)) := by
    unfold PRZZDyadicEnvelope.annihilator
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.const_mul _

theorem joint_measurable (F : ℝ → ℂ) (hF : Continuous F)
    (M u q delta : ℝ) (z sigma : ℂ) :
    StronglyMeasurable (fun p : ℝ × ℝ => PRZZFullWeightSmooth.weight F M
      (2*Real.pi*u/(p.1*q)) (delta*p.1/u) z sigma p.2) := by
  have hw : Measurable (fun p : ℝ × ℝ => PRZZDyadicEnvelope.sourceW sigma
      ((2*Real.pi*u/(p.1*q))*p.2^2)) :=
    (source_measurable sigma).measurable.comp (by fun_prop)
  apply Measurable.stronglyMeasurable
  unfold PRZZFullWeightSmooth.weight
  fun_prop

theorem fourier_measurable (F : ℝ → ℂ) (hF : Continuous F)
    (M u q delta xi : ℝ) (z sigma : ℂ) :
    StronglyMeasurable (fun t : ℝ => 𝓕 (PRZZFullWeightSmooth.weight F M
      (2*Real.pi*u/(t*q)) (delta*t/u) z sigma) xi) := by
  simp_rw [Real.fourier_eq']
  have hh : StronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2*Real.pi*⟪p.2,xi⟫)*I)) •
        PRZZFullWeightSmooth.weight F M (2*Real.pi*u/(p.1*q)) (delta*p.1/u) z sigma p.2) := by
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2*Real.pi*⟪p.2,xi⟫)*I)))).stronglyMeasurable.smul
        (joint_measurable F hF M u q delta z sigma)
  exact hh.integral_prod_right'

/-- The compactness constant is uniform in time and frequency, but may
depend on the fixed height and row. It supplies domination for exchange,
not the optimized height exponent. -/
theorem uniform_fourier (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M u q delta : ℝ) (z sigma : ℂ)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < u) (hq : 0 < q) (hs : sigma ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc T (2*T), ∀ xi : ℝ, xi ≠ 0 →
      ‖𝓕 (PRZZFullWeightSmooth.weight F M (2*Real.pi*u/(t*q))
        (delta*t/u) z sigma) xi‖ ≤ B/(2*Real.pi*|xi|)^2 := by
  obtain ⟨C,D,E,hpos,hm⟩ := PRZZEnvelopeMass.mass_bound F hF hsF 1 (by norm_num)
  let R := |delta| * (2*T)/u/(M/2)
  let b := fun t : ℝ => (3*M-M/2)*(PRZZEnvelopeMass.cap C D E 1
    (2*Real.pi*u/(t*q)) M R (|Real.log (M/2)|+|Real.log (3*M)|) z sigma 2/(M/2)^2)
  have hc : ContinuousOn b (Icc T (2*T)) := by
    intro t ht
    have ht0 : 0 < t := hT.trans_le ht.1
    have hbase : ContinuousAt (fun s : ℝ =>
        (2*Real.pi*u/(s*q)*(M/2)^2)^(-(1:ℝ))) t := by
      simp only [Real.rpow_neg_one]
      exact ((continuousAt_const.div (continuousAt_id.mul_const q)
        (mul_ne_zero ht0.ne' hq.ne')).mul_const ((M/2)^2)).inv₀
          (show 2*Real.pi*u/(t*q)*(M/2)^2 ≠ 0 from ne_of_gt (by positivity))
    have hcap : ContinuousAt (fun s : ℝ => PRZZEnvelopeMass.cap C D E 1
        (2*Real.pi*u/(s*q)) M R (|Real.log (M/2)|+|Real.log (3*M)|) z sigma 2) t := by
      unfold PRZZEnvelopeMass.cap PRZZFullWeightJets.convolution
      apply tendsto_finsetSum
      intro i hi
      exact continuousAt_const.mul (continuousAt_const.mul hbase)
    exact (continuousAt_const.mul (hcap.div_const _)).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro t ht xi hxi
  have ht0 : 0 < t := hT.trans_le ht.1
  have hk : 0 < 2*Real.pi*u/(t*q) := by positivity
  have hp : ∀ x ∈ Icc (M/2) (3*M), |(delta*t/u)/x| ≤ R := by
    intro x hx
    have hx0 : 0 < x := (by positivity : 0 < M/2).trans_le hx.1
    rw [abs_div,abs_div,abs_mul,abs_of_pos ht0,abs_of_pos hu,abs_of_pos hx0]
    dsimp [R]
    gcongr
    · exact ht.2
    · exact hx.1
  have hm' := hm 2 M _ _ R z sigma hM hk (by dsimp [R]; positivity) hs hp
  have habs : |b t| ≤ B := by simpa only [Real.norm_eq_abs] using hB t ht
  have hb' : b t ≤ max B 0 := (le_abs_self _).trans (habs.trans (le_max_left _ _))
  have hh := PRZZWeightFourier.fourier_bound (1/2) 3 (by norm_num) F hF M
    (2*Real.pi*u/(t*q)) (delta*t/u) z sigma
    hM hk hs hsF 2 xi hxi
  rw [← PRZZWeightFourier.mass_on_support (1/2) 3 (by norm_num) F M
    (2*Real.pi*u/(t*q)) (delta*t/u) z sigma hM hsF 2] at hh
  exact hh.trans (div_le_div_of_nonneg_right (hm'.trans hb') (by positivity))

def term (F : ℝ → ℂ) (M u q delta : ℝ) (z sigma : ℂ) (H j : ℕ)
    (p m : ℕ → ℂ) (t : ℝ) : ℂ :=
  (q⁻¹:ℝ) • (𝓕 (PRZZFullWeightSmooth.weight F M (2*Real.pi*u/(t*q))
    (delta*t/u) z sigma) (((H+j:ℝ)+1)/q)*p j+
    𝓕 (PRZZFullWeightSmooth.weight F M (2*Real.pi*u/(t*q))
    (delta*t/u) z sigma) (-(((H+j:ℝ)+1)/q))*m j)

/-- Actual normalized positive/negative Fourier terms admit a time-uniform
summable envelope. No Fourier-decay premise is supplied. -/
theorem term_domination (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M u q delta : ℝ) (z sigma : ℂ) (H : ℕ) (p m : ℕ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < u) (hq : 0 < q) (hs : sigma ≠ 0)
    (hp : ∀ j, ‖p j‖ ≤ 1) (hm : ∀ j, ‖m j‖ ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc T (2*T), ∀ j,
      ‖term F M u q delta z sigma H j p m t‖ ≤ D*(1/((j:ℝ)+1)^2) := by
  obtain ⟨B,hB,h⟩ := uniform_fourier F hF hsF T M u q delta z sigma hT hM hu hq hs
  refine ⟨q⁻¹*(2*B*(q/(2*Real.pi))^2),by positivity,?_⟩
  intro t ht j
  have hx : 0 < ((H+j:ℝ)+1)/q := by positivity
  have h1 := h t ht _ hx.ne'
  have h2 := h t ht _ (neg_ne_zero.mpr hx.ne')
  rw [abs_of_pos hx] at h1
  rw [abs_neg,abs_of_pos hx] at h2
  have hb : ‖term F M u q delta z sigma H j p m t‖ ≤
      q⁻¹*(2*B*(q/(2*Real.pi))^2/((H+j:ℝ)+1)^2) := by
    unfold term
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hq)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    have hh := add_le_add
      (mul_le_mul h1 (hp j) (norm_nonneg _) (by positivity))
      (mul_le_mul h2 (hm j) (norm_nonneg _) (by positivity))
    apply hh.trans_eq
    field_simp
    <;> ring
  apply hb.trans
  have hh := PRZZWeightTail.tail_majorant (2*B*(q/(2*Real.pi))^2) (by positivity) 0 H j
  simpa only [pow_zero,div_one,mul_assoc] using
    mul_le_mul_of_nonneg_left hh (show 0 ≤ q⁻¹ by positivity)

theorem actual_swap (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M u q delta : ℝ) (z sigma : ℂ) (H : ℕ) (p m : ℕ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < u) (hq : 0 < q) (hs : sigma ≠ 0)
    (hp : ∀ j, ‖p j‖ ≤ 1) (hm : ∀ j, ‖m j‖ ≤ 1)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∑' j, ∫ t in Icc T (2*T), Phi (t/T)*term F M u q delta z sigma H j p m t) =
      ∫ t in Icc T (2*T), ∑' j, Phi (t/T)*term F M u q delta z sigma H j p m t := by
  obtain ⟨D,hD,hd⟩ := term_domination F hF hsF T M u q delta z sigma H p m hT hM hu hq hs hp hm
  obtain ⟨P,hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show Continuous (fun t : ℝ => Phi (t/T)) by fun_prop).continuousOn
  apply PRZZArithmeticFourierTail.time_swap _
    (fun j => (max P 0*D)*(1/((j:ℝ)+1)^2)) T
    (PRZZWeightTail.square_summable.mul_left _) (fun j => by positivity)
  · intro j
    apply StronglyMeasurable.aestronglyMeasurable
    apply ((show Continuous (fun t : ℝ => Phi (t/T)) by fun_prop).stronglyMeasurable).mul
    unfold term
    exact (((fourier_measurable F hF.continuous M u q delta _ z sigma).mul_const _).add
      ((fourier_measurable F hF.continuous M u q delta _ z sigma).mul_const _)).const_smul (q⁻¹:ℝ)
  · intro j t ht
    rw [norm_mul]
    exact (mul_le_mul ((hP t ht).trans (le_max_left _ _)) (hd t ht j)
      (norm_nonneg _) (le_max_right _ _)).trans_eq (by ring)

/-- The actual residue phases, with both signs and the original modulus. -/
def residuePhase (H : ℕ) (q residue : ℝ) (j : ℕ) : ℂ :=
  Complex.exp (I*((2*Real.pi*((H+j:ℝ)+1)*residue/q:ℝ):ℂ))

theorem residue_norm (H : ℕ) (q residue : ℝ) (j : ℕ) :
    ‖residuePhase H q residue j‖ = 1 := by
  simp [residuePhase,Complex.norm_exp]

theorem source_swap (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (d T b eD eH residue r : ℝ) (row : PRZZTailTimeSum.Row)
    (hrow : PRZZTailTimeSum.Domain d T b eD eH row)
    (hT : 36 ≤ T) (hlog : 1 ≤ Real.log T) (alpha beta : ℂ)
    (hr : 0 < r) (hsep : r ≤ ‖alpha+beta‖)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    let f := fun j t => Phi (t/T)*term F row.M row.u row.q row.delta
      (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) row.H j
      (residuePhase row.H row.q residue) (residuePhase row.H row.q (-residue)) t
    (∑' j, ∫ t in Icc T (2*T), f j t) = ∫ t in Icc T (2*T), ∑' j, f j t := by
  obtain ⟨hM,_,_,_,hq,_,_,hu,_⟩ := hrow
  have hab : alpha+beta ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith)
  exact actual_swap F hF hsF T row.M row.u row.q row.delta _ _ row.H _ _
    (by linarith) (by linarith) (by linarith) hq (div_ne_zero hab hL)
    (fun j => (residue_norm _ _ _ j).le) (fun j => (residue_norm _ _ _ j).le) Phi hPhi

#print axioms residue_norm
#print axioms source_swap
#print axioms term_domination
#print axioms actual_swap
#print axioms uniform_fourier
#print axioms source_measurable
#print axioms joint_measurable
#print axioms fourier_measurable
end XiPrime8845.PRZZFourierTime
