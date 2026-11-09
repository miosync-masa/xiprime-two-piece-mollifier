import PRZZFamilyMoment
import PRZZMixedDefect

/-! Polarize the complete actual Poisson model, not isolated nonintegrable
Fourier components. Both branches and all five collective components,
zeroPair and gammaDefect are retained. The cutoff-removed error is bounded
uniformly before the two coefficient slots. This is an AFE reduction, not
an optimal estimate of the remaining collective Poisson field. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ContDiff
namespace XiPrime8845.PRZZMixedPoisson
open PRZZCoefficientPolarization
set_option maxHeartbeats 7000000

def lift (Q : (ℕ → ℂ) → ℂ) (c d : ℕ → ℂ) : ℂ :=
  (Q (combine c d 1)-Q (combine c d (-1))+
    I*Q (combine c d I)-I*Q (combine c d (-I)))/4

def moment (N : ℕ) (c d : ℕ → ℂ) (a b : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  pairing (volume.restrict (Icc T (2*T))) N
    (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg a t)*
      riemannZeta (PRZZAFEDual.rightArg b t))) c d

def model (L J N : ℕ) (F : ℝ → ℂ) (c d : ℕ → ℂ) (a b : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  lift (fun e => PRZZAllPoissonAFE.model L J N F e a b T phi) c d

/-- Every actual collective residual is retained before polarization. -/
def components (L J N : ℕ) (F : ℝ → ℂ) (e : ℕ → ℂ) (a b : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (((∫ t in Icc T (2*T), phi t*PRZZExhaustiveAFEError.field L J N F e a b t)+
    ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier a b t)*
      PRZZExhaustiveAFEError.field L J N F e (-b) (-a) t)-
    PRZZZeroCoupled.zeroPair N e a b T phi)+
  ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N e a b t

theorem moment_eq_lift (N : ℕ) (c d : ℕ → ℂ) (a b : ℂ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (T : ℝ)
    (phi : ℝ → ℂ) (hp : Continuous phi) :
    moment N c d a b T phi =
      lift (fun e => PRZZExhaustiveAFEError.moment N e a b T phi) c d := by
  have hg := hp.mul (PRZZIntegratedDefect.zeta_continuous a b ha hb)
  have hh := pairing_polarization (volume.restrict (Icc T (2*T))) N
    (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg a t)*
      riemannZeta (PRZZAFEDual.rightArg b t))) c d (by
      intro z hz
      exact ((hg.mul (PRZZMollifiedTime.polynomial_continuous _ _)).mul
        (PRZZMollifiedTime.polynomial_continuous _ _).star).integrableOn_Icc)
  simp_rw [← PRZZFamilyMoment.moment_eq] at hh
  unfold moment lift
  linear_combination hh/4

theorem original_error_eq (L J N : ℕ) (F : ℝ → ℂ) (c d : ℕ → ℂ)
    (a b : ℂ) (T : ℝ) (phi : ℝ → ℂ) :
    moment N c d a b T phi-
        lift (fun e => PRZZCoupledAFE.diagonalMain N e a b T phi) c d =
      lift (fun e => components L J N F e a b T phi) c d+
        (moment N c d a b T phi-model L J N F c d a b T phi) := by
  have he (e : ℕ → ℂ) : PRZZAllPoissonAFE.model L J N F e a b T phi =
      PRZZCoupledAFE.diagonalMain N e a b T phi+components L J N F e a b T phi := by
    rw [← PRZZExhaustiveAFEError.model_eq]
    unfold PRZZExhaustiveAFEError.componentModel components
    ring
  simp only [model,lift,he]
  ring

theorem square_error_limit (N : ℕ) (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (e : ℕ → ℂ) (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (hn : ‖a+b‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) (J : ℕ → ℕ) :
    Tendsto (fun L => PRZZExhaustiveAFEError.moment N e a b T phi-
      PRZZAllPoissonAFE.model L (J L) N F e a b T phi) atTop
      (𝓝 (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi e e N t*
        PRZZIntegratedDefect.defect a b t)) := by
  let R : ℕ → PRZZAFEIndices.Label → Prop := fun _ _ => True
  have h := PRZZWRowLimit.afe_error_limit N F R hlo hhi e e a b ha hb hs T hT phi hp
  have hd := PRZZCoupledAFE.diagonalPair_limit N F e a b ha hb hs hn T hT phi hp hlo hhi
  have hz := hd.sub_const (PRZZCoupledAFE.diagonalMain N e a b T phi+
    PRZZCoupledAFE.correctionPair N e a b T phi)
  have hh := h.add hz
  simp only [sub_self,add_zero] at hh
  convert hh using 1
  funext L
  rw [PRZZAllPoissonAFE.model_eq L (J L) N F hf hlo hhi R e a b ha hb hs hn T hT phi hp]
  unfold PRZZExhaustiveAFEError.moment PRZZCoupledAFE.coupledModel
    PRZZCoupledAFE.offDiagonalPair
  ring

/-- Integrability is proved before polarizing the actual defect integral. -/
theorem defect_integrable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun t => w t*PRZZIntegratedDefect.defect a b t) (Icc T (2*T)) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hc := PRZZMollifiedTime.dualMultiplier_continuous a b
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hs' : -b + -a ≠ 0 := by
    rw [show -b + -a = -(a+b) by ring]; exact neg_ne_zero.mpr hs
  have hz : IntegrableOn (fun t => w t*(riemannZeta (PRZZAFEDual.leftArg a t)*
      riemannZeta (PRZZAFEDual.rightArg b t))) (Icc T (2*T)) :=
    (hw.mul (PRZZIntegratedDefect.zeta_continuous a b ha hb)).integrableOn_Icc
  have hi := PRZZWRowLimit.main_integrable a b ha hb hs T hT w hw
  have hj := PRZZWRowLimit.main_integrable (-b) (-a) (by simpa using hb) (by simpa using ha)
    hs' T hT (fun t => w t*PRZZAFEDual.dualMultiplier a b t) (hw.mul hc)
  apply (hz.sub (hi.add hj)).congr
  exact Eventually.of_forall (fun t => by
    dsimp only [Pi.sub_apply,Pi.add_apply]
    unfold PRZZIntegratedDefect.defect
    ring)

theorem defect_eq_lift (N : ℕ) (c d : ℕ → ℂ) (a b : ℂ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t*
      PRZZIntegratedDefect.defect a b t) =
    lift (fun e => ∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi e e N t*
      PRZZIntegratedDefect.defect a b t) c d := by
  let g := fun t => phi t*PRZZIntegratedDefect.defect a b t
  have he (e f : ℕ → ℂ) :
      (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi e f N t*
        PRZZIntegratedDefect.defect a b t) =
      pairing (volume.restrict (Icc T (2*T))) N g e f := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      unfold PRZZMollifiedTime.mollifierWeight density
      dsimp [g]; ring)
  have hh := pairing_polarization (volume.restrict (Icc T (2*T))) N g c d (by
    intro z hz
    have hi := defect_integrable a b ha hb hs T hT _
      (PRZZMollifiedTime.mollifierWeight_continuous phi hp (combine c d z) (combine c d z) N)
    apply hi.congr
    exact Eventually.of_forall (fun t => by
      unfold PRZZMollifiedTime.mollifierWeight density
      dsimp [g]; ring))
  unfold lift
  simp_rw [he]
  linear_combination hh/4

/-- The limit is exactly the actual mixed defect integral, not an
existentially chosen proxy or an assumed Fourier remainder. -/
theorem error_limit (N : ℕ) (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (c d : ℕ → ℂ) (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (hn : ‖a+b‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) (J : ℕ → ℕ) :
    Tendsto (fun L => moment N c d a b T phi-model L (J L) N F c d a b T phi) atTop
      (𝓝 (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t*
        PRZZIntegratedDefect.defect a b t)) := by
  have h (z : ℂ) := square_error_limit N F hf hlo hhi (combine c d z) a b ha hb hs hn T hT phi hp J
  have hh := ((((h 1).sub (h (-1))).add ((h I).const_mul I)).sub
    ((h (-I)).const_mul I)).div_const (4:ℂ)
  rw [defect_eq_lift N c d a b ha hb hs T hT phi hp]
  convert hh using 1
  · funext L
    rw [moment_eq_lift N c d a b ha hb T phi hp]
    unfold model lift
    ring
  · rfl

theorem lift_bound (Q : (ℕ → ℂ) → ℂ) (c d : ℕ → ℂ) (B : ℝ)
    (h : ∀ z ∈ ([1,-1,I,-I] : List ℂ), ‖Q (combine c d z)‖ ≤ B) :
    ‖lift Q c d‖ ≤ B := by
  have h1 := h 1 (by simp)
  have h2 := h (-1) (by simp)
  have h3 := h I (by simp)
  have h4 := h (-I) (by simp)
  have hsub := norm_sub_le (Q (combine c d 1)) (Q (combine c d (-1)))
  have hadd := norm_add_le (Q (combine c d 1)-Q (combine c d (-1))) (I*Q (combine c d I))
  have hlast := norm_sub_le (Q (combine c d 1)-Q (combine c d (-1))+I*Q (combine c d I))
    (I*Q (combine c d (-I)))
  simp only [norm_mul,norm_I,one_mul] at hadd hlast
  unfold lift
  rw [norm_div]
  norm_num only [norm_ofNat]
  linarith

/-- C and the eventual height threshold precede both coefficient slots,
including height-dependent profiles. The Fourier cutoff J(L) is arbitrary. -/
theorem scaled_error_limit (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (S r delta H : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ (c d : ℕ → ℂ) (N : ℕ),
      1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) → ∀ J : ℕ → ℕ, ∃ E : ℂ,
      Tendsto (fun L => moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi-
        model L (J L) N F c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZMixedDefect.defect_target S r delta H hS hr hd hH
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hp hP hphi J
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  have ha : ‖a‖ ≤ 1/4 := (hsmall.2 A hA).trans (by norm_num)
  have hb : ‖b‖ ≤ 1/4 := (hsmall.2 B hB).trans (by norm_num)
  have hs : a+b ≠ 0 := by
    dsimp [a,b]; rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  have hn : ‖a+b‖ ≤ 1/8 := (norm_add_le a b).trans
    (by have h1 := hsmall.2 A hA; have h2 := hsmall.2 B hB; dsimp [a,b] at *; linarith)
  refine ⟨_,error_limit N F hf hlo hhi c d a b ha hb hs hn T (by linarith) phi hp J,?_⟩
  exact h A B hA hB hsep c d N hN hNT hc hd' phi P hp hP hphi

#print axioms moment_eq_lift
#print axioms original_error_eq
#print axioms square_error_limit
#print axioms defect_integrable
#print axioms defect_eq_lift
#print axioms error_limit
#print axioms lift_bound
#print axioms scaled_error_limit
end XiPrime8845.PRZZMixedPoisson
