import PRZZMellinTail

/-! Supplied time/Mellin Fubini for the actual Gamma kernel on bounded
time intervals. Constants may depend on the interval; the exponential
height envelope proves integrability, not an optimized error estimate. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZKernelTime
open PRZZMellinTail PRZZGammaFar PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem joint_continuous (a b : ℂ) (x : ℝ) (hx : 0 < x)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    Continuous (fun p : ℝ × ℝ => integrand a b x p.1 p.2) := by
  have hg (c : ℂ) (hc : -(1/2:ℝ) < c.re) (e : ℝ) :
      Continuous (fun p : ℝ × ℝ => Gamma ((1/2+c+(2+(p.2:ℂ)*I)+(e*p.1:ℝ)*I)/2)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply (PRZZGammaPath.gamma_analytic _ (by simp; linarith)).continuousAt.comp (x := p)
    fun_prop
  have hd (c : ℂ) (hc : -(1/2:ℝ) < c.re) (e : ℝ) :
      Continuous (fun p : ℝ × ℝ => Gamma ((1/2+c+(e*p.1:ℝ)*I)/2)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply (PRZZGammaPath.gamma_analytic _ (by simp; linarith)).continuousAt.comp (x := p)
    fun_prop
  have hn (c : ℂ) (hc : -(1/2:ℝ) < c.re) (y : ℝ) :
      Gamma ((1/2+c+(y:ℂ)*I)/2) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith)
  have ga := hg a ha 1
  have gb := hg b hb (-1)
  have da := hd a ha 1
  have db := hd b hb (-1)
  simp only [one_mul,ofReal_neg,neg_mul,← sub_eq_add_neg] at ga gb da db
  have hr : Continuous (fun p : ℝ × ℝ => PRZZAFEGamma.gammaRatio a b (2+(p.2:ℂ)*I) p.1) := by
    unfold PRZZAFEGamma.gammaRatio
    refine Continuous.div ?_ (da.mul db) ?_
    · apply Continuous.mul _ (ga.mul gb)
      simp_rw [Complex.cpow_def_of_ne_zero (show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)]
      fun_prop
    · intro p
      exact mul_ne_zero (hn a ha p.1) (by simpa [sub_eq_add_neg] using hn b hb (-p.1))
  have hf : Continuous (fun v : ℝ => factor (a+b) x v) := by
    unfold factor annihilator
    apply Continuous.div
    · simp_rw [Complex.cpow_def_of_ne_zero (show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne')]
      fun_prop
    · fun_prop
    · intro v he
      have hh := congrArg Complex.re he
      norm_num at hh
  have he : Continuous (fun p : ℝ × ℝ => exp ((2+(p.2:ℂ)*I)^2)) := by fun_prop
  exact (hf.comp continuous_snd).mul (he.mul hr)

theorem uniform_space_majorant (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 < x → ∀ t v : ℝ, |t| ≤ R →
      ‖integrand a b x t v‖ ≤ B*x^(-2:ℝ)*majorant v := by
  obtain ⟨C,hC,h⟩ := actual_ratio_bound a b ha ha' hb hb'
  refine ⟨(1+16/‖a+b‖^2)*C*Real.exp (4+2*Real.pi*R),by positivity,?_⟩
  intro x hx t v ht
  have hg : ‖exp ((2+(v:ℂ)*I)^2)*PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤
      C*Real.exp (4+2*Real.pi*R)*Real.exp (-v^2/2) := by
    rw [norm_mul,gaussian_norm]
    calc
      _ ≤ Real.exp (4-v^2)*(C*Real.exp (2*Real.pi*|t|)) := by gcongr; exact h t v
      _ = C*Real.exp (4-v^2+2*Real.pi*|t|) := by rw [Real.exp_add]; ring
      _ ≤ C*Real.exp (4+2*Real.pi*R+(-v^2/2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht),sq_nonneg v])) hC.le
      _ = _ := by rw [Real.exp_add]; ring
  rw [integrand,norm_mul]
  exact (mul_le_mul (factor_bound (a+b) hs x v hx) hg (norm_nonneg _) (by positivity)).trans_eq
    (by unfold majorant; ring)

theorem bounded_time_majorant (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x R : ℝ) (hx : 0 < x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t v : ℝ, |t| ≤ R →
      ‖integrand a b x t v‖ ≤ B*majorant v := by
  obtain ⟨B,hB,h⟩ := uniform_space_majorant a b ha ha' hb hb' hs R
  exact ⟨B*x^(-2:ℝ),by positivity,h x hx⟩

def timeCut (a b : ℂ) (x R t v : ℝ) : ℂ :=
  (Icc (-R) R).indicator (fun t => integrand a b x t v) t

theorem time_mellin_integrable (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x R : ℝ) (hx : 0 < x) : Integrable (Function.uncurry (timeCut a b x R)) := by
  obtain ⟨B,hB,h⟩ := bounded_time_majorant a b ha ha' hb hb' hs x R hx
  have hi : Integrable ((Icc (-R) R).indicator (fun _ : ℝ => B)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (continuousOn_const.integrableOn_compact isCompact_Icc)
  have hm := hi.mul_prod majorant_integrable
  have he : Function.uncurry (timeCut a b x R) =
      ((Icc (-R) R) ×ˢ (Set.univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ => integrand a b x p.1 p.2) := by
    funext p
    simp [timeCut,Set.indicator,Function.uncurry]
  apply hm.mono'
  · rw [he]
    exact (joint_continuous a b x hx ha hb).aestronglyMeasurable.indicator
      (measurableSet_Icc.prod MeasurableSet.univ)
  · apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p.1 ∈ Icc (-R) R
    · simpa [timeCut,Function.uncurry,hp] using h p.1 p.2 (abs_le.mpr hp)
    · simp [timeCut,Function.uncurry,hp]

/-- Both integrability and the majorant are supplied for the actual kernel.
The retained time window is not a premise on an abstract integrand. -/
theorem time_mellin_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x R : ℝ) (hx : 0 < x) :
    (∫ t, ∫ v, timeCut a b x R t v) = ∫ v, ∫ t, timeCut a b x R t v :=
  integral_integral_swap (time_mellin_integrable a b ha ha' hb hb' hs x R hx)

theorem kernel_time_integral (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x R : ℝ) (hx : 0 < x) :
    (∫ t in Icc (-R) R, PRZZAFEGamma.kernel a b x t) =
      (1/(2*Real.pi):ℂ)*∫ v, ∫ t in Icc (-R) R, integrand a b x t v := by
  have h := time_mellin_swap a b ha ha' hb hb' hs x R hx
  have hl : (∫ t, ∫ v, timeCut a b x R t v) =
      ∫ t in Icc (-R) R, ∫ v, integrand a b x t v := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc (-R) R <;> simp [timeCut,ht]
  have hr (v : ℝ) : (∫ t, timeCut a b x R t v) =
      ∫ t in Icc (-R) R, integrand a b x t v := by
    exact integral_indicator measurableSet_Icc
  rw [hl] at h
  simp_rw [hr] at h
  simp_rw [kernel_eq]
  rw [integral_const_mul,h]

#print axioms joint_continuous
#print axioms uniform_space_majorant
#print axioms bounded_time_majorant
#print axioms time_mellin_integrable
#print axioms time_mellin_swap
#print axioms kernel_time_integral
end XiPrime8845.PRZZKernelTime
