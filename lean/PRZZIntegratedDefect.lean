import PRZZDualError

/-! The single original zeta-to-W defect integral. Integrability of the
replacement and residue terms is supplied before splitting the integral.
The W series have not yet been converted to post-Poisson A*. -/
noncomputable section
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZIntegratedDefect
open PRZZAFEDual PRZZL1Finite PRZZActualDirectSum
set_option maxHeartbeats 3000000

def mainSeries (a b : ℂ) (t : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, directTerm a b (mainWeight a b) t (p.1+1) (p.2+1)

def defect (a b : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (leftArg a t)*riemannZeta (rightArg b t) -
    (mainSeries a b t+dualMultiplier a b t*mainSeries (-b) (-a) t)

theorem replacement_integrable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (w : ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun t => w t*PRZZReplacementIntegral.difference a b t) (Icc T (2*T)) := by
  let f := fun p : ℕ × ℕ => fun t : ℝ =>
    directTerm a b (fun n t => PRZZLocalReplacement.error a b n t) t (p.1+1) (p.2+1)
  have hm (p : ℕ × ℕ) : AEStronglyMeasurable (f p) (volume.restrict (Icc T (2*T))) :=
    PRZZProductTime.term_measurable a b ha hb hs T (by linarith) _ _ (by omega) (by omega)
  have hsum : AEStronglyMeasurable (fun t => ∑' p, f p t) (volume.restrict (Icc T (2*T))) := by
    refine ⟨fun t => ∑' p, (hm p).mk (f p) t,
      StronglyMeasurable.tsum (fun p => (hm p).stronglyMeasurable_mk),?_⟩
    filter_upwards [ae_all_iff.mpr (fun p => (hm p).ae_eq_mk)] with t ht
    exact tsum_congr (fun p => ht p)
  have he : (fun t => PRZZReplacementIntegral.difference a b t) =ᵐ[volume.restrict (Icc T (2*T))]
      (fun t => ∑' p, f p t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact infinite_replacement a b ha hb hs T t hT hT' ht.1 ht.2
  obtain ⟨C,hC,h⟩ := PRZZReplacementIntegral.actual_series_bound
  have hi : IntegrableOn (fun t => ‖w t‖*(C*(1+16/‖a+b‖^2)*
      PRZZReplacementIntegral.cost T t*PRZZReplacementIntegral.arithmeticMass)) (Icc T (2*T)) := by
    apply Continuous.integrableOn_Icc
    unfold PRZZReplacementIntegral.cost; fun_prop
  apply hi.mono' (hw.aestronglyMeasurable.mul (hsum.congr he.symm))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h a b ha hb hs T t hT hT' ht.1 ht.2) (norm_nonneg _)

theorem zeta_continuous (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) :
    Continuous (fun t : ℝ => riemannZeta (leftArg a t)*riemannZeta (rightArg b t)) := by
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  apply Continuous.mul
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (differentiableAt_riemannZeta (s := leftArg a t) (by
      intro he; have hh := congrArg Complex.re he
      simp [leftArg] at hh; linarith [har.2])).continuousAt.comp
    unfold leftArg; fun_prop
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (differentiableAt_riemannZeta (s := rightArg b t) (by
      intro he; have hh := congrArg Complex.re he
      simp [rightArg] at hh; linarith [hbr.2])).continuousAt.comp
    unfold rightArg; fun_prop

theorem residue_integrable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 1 ≤ T) (w : ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun t => w t*PRZZContourAFE.noncentralSum a b t) (Icc T (2*T)) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hs' : -b + -a ≠ 0 := by
    rw [show -b + -a = -(a+b) by ring]; exact neg_ne_zero.mpr hs
  have hc := PRZZMollifiedTime.dualMultiplier_continuous a b
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hi := PRZZIntegratedAFE.weighted_integrable a b
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2]) hs (2*T) w hw
  have hj := PRZZIntegratedAFE.weighted_integrable (-b) (-a)
    (by simp; linarith [br.2]) (by simp; linarith [br.1])
    (by simp; linarith [ar.2]) (by simp; linarith [ar.1]) hs' (2*T)
    (fun t => w t*dualMultiplier a b t) (hw.mul hc)
  have hsub : Icc T (2*T) ⊆ Icc (-(2*T)) (2*T) := by intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hz : IntegrableOn (fun t => w t*(riemannZeta (leftArg a t)*riemannZeta (rightArg b t)))
      (Icc T (2*T)) := (hw.mul (zeta_continuous a b ha hb)).integrableOn_Icc
  apply (((hi.mono_set hsub).add (hj.mono_set hsub)).sub hz).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he := PRZZSeriesAFE.series_afe a b t ha hb hs (hT.trans ht.1)
  change _ = PRZZIntegratedAFE.series a b t+dualMultiplier a b t*PRZZIntegratedAFE.series (-b) (-a) t-_ at he
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [he]
  ring

/-- No integrability or decomposition premise is requested. -/
theorem integral_eq (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (w : ℝ → ℂ) (hw : Continuous w) :
    (∫ t in Icc T (2*T), w t*defect a b t) =
      ((∫ t in Icc T (2*T), w t*PRZZReplacementIntegral.difference a b t) -
        (∫ t in Icc T (2*T), w t*PRZZContourAFE.noncentralSum a b t)) +
      (∫ t in Icc T (2*T), w t*dualMultiplier a b t*PRZZReplacementIntegral.difference (-b) (-a) t) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hc := PRZZMollifiedTime.dualMultiplier_continuous a b
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hs' : -b + -a ≠ 0 := by rw [show -b + -a = -(a+b) by ring]; exact neg_ne_zero.mpr hs
  have hi := replacement_integrable a b ha hb hs T hT hT' w hw
  have hj := replacement_integrable (-b) (-a) (by simpa using hb) (by simpa using ha)
    hs' T hT hT' (fun t => w t*dualMultiplier a b t) (hw.mul hc)
  have hr := residue_integrable a b ha hb hs T (by linarith) w hw
  have his : IntegrableOn (fun t => w t*PRZZReplacementIntegral.difference a b t-
      w t*PRZZContourAFE.noncentralSum a b t) (Icc T (2*T)) := hi.sub hr
  rw [← integral_sub hi hr,← integral_add his hj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have he := PRZZDualError.two_sided_defect a b t ha hb hs (by linarith [ht.1])
  change defect a b t = _ at he
  dsimp only
  rw [he]
  ring

/-- A bound on the single literal zeta-to-W defect integral, not merely
on a formally assembled sum of error integrals. -/
theorem scaled_target (js : List ℕ) (S r delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZDualError.replacement_residue_target js S r delta hS hr hd
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (256*Real.pi),eventually_ge_atTop (128:ℝ)] with T h hsmall hT hT'
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hab (by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1]))
  rw [integral_eq _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs T hT hT' _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi _ _ N)]
  exact h A B hA hB hsep N hN hNT phi P hphi hP hp

#print axioms scaled_target
#print axioms replacement_integrable
#print axioms zeta_continuous
#print axioms residue_integrable
#print axioms integral_eq
end XiPrime8845.PRZZIntegratedDefect
