import PRZZDiagonalMellin
import PRZZHorizontalDecay

/-! Quantitative bounds for the primitive diagonal Mellin contour.
The Gaussian and zeta estimates are supplied here. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
namespace XiPrime8845.PRZZDiagonalContour
open PRZZDiagonalMellin PRZZDyadicEnvelope
set_option maxHeartbeats 5000000

theorem strip_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (w : ℂ)
    (hlo : -(1/8:ℝ) ≤ w.re) (hhi : w.re ≤ 2)
    (hw : 1/8 ≤ ‖w‖) (hp : 1/8 ≤ ‖1-(1+sigma+2*w)‖) :
    ‖integrand sigma X w‖ ≤
      (256*Real.exp 4)*(1+16/‖sigma‖^2)*X^w.re*
        (1+|w.im|)^3*Real.exp (-w.im^2) := by
  let V := 1+|w.im|
  have hV : 1 ≤ V := by dsimp [V]; linarith [abs_nonneg w.im]
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  have hsre : 1/2 ≤ (1+sigma+2*w).re := by simp; linarith
  have hsn : (1+sigma+2*w) ≠ 1 := by intro he; norm_num [he] at hp
  have hwre : |w.re| ≤ 2 := abs_le.mpr ⟨by linarith,hhi⟩
  have hwn : ‖w‖ ≤ 2*V := by
    have hh := norm_le_abs_re_add_abs_im w
    dsimp [V]; linarith
  have hsnorm : ‖1+sigma+2*w‖ ≤ 6*V := by
    have hh := (norm_add_le (1+sigma) (2*w)).trans
      (add_le_add (norm_add_le (1:ℂ) sigma) le_rfl)
    norm_num [norm_mul] at hh
    linarith
  have hz : ‖riemannZeta (1+sigma+2*w)‖ ≤ 32*V := by
    have hh := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (by linarith : 0 < (1+sigma+2*w).re) hsn
    have hd : ‖1+sigma+2*w‖/(1+sigma+2*w).re ≤ 2*‖1+sigma+2*w‖ := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [norm_nonneg (1+sigma+2*w)]
    have hi : 1/‖1-(1+sigma+2*w)‖ ≤ (8:ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith
  have ha : ‖annihilator sigma w‖ ≤ (1+16/‖sigma‖^2)*V^2 := by
    have hh := annihilator_bound sigma w 1 ‖sigma‖ (by norm_num) (norm_pos_iff.mpr hs) (by simp)
    simp only [div_pow,one_pow,mul_one_div] at hh
    apply hh.trans
    calc
      _ ≤ 1+4*(2*V)^2/‖sigma‖^2 := by gcongr
      _ ≤ _ := by
        have hsq : 1 ≤ V^2 := by nlinarith
        calc
          _ = 1+(16/‖sigma‖^2)*V^2 := by ring
          _ ≤ _ := by nlinarith
  have he : ‖Complex.exp (w^2)‖ ≤ Real.exp 4*Real.exp (-w.im^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,mul_re]
    nlinarith [sq_abs w.re,abs_nonneg w.re]
  have hi : ‖w‖⁻¹ ≤ (8:ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖w‖)).mpr
    linarith
  rw [integrand,amplitude,norm_mul,norm_div,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    _ ≤ ((X^w.re*(Real.exp 4*Real.exp (-w.im^2))*
      ((1+16/‖sigma‖^2)*V^2))*8)*(32*V) := by
      simp only [div_eq_mul_inv]
      gcongr; simpa only [div_eq_mul_inv] using ha
    _ = _ := by dsimp [V]; ring

def majorant (v : ℝ) : ℝ := (1+|v|)^3*Real.exp (-v^2)

theorem majorant_integrable : Integrable majorant := by
  have h0 : Integrable (fun v : ℝ => Real.exp (-v^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have h4 : Integrable (fun v : ℝ => v^4*Real.exp (-v^2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      (by norm_num : (-1:ℝ) < 4)
    simpa [Real.rpow_natCast] using h
  apply ((h0.add h4).const_mul 16).mono' (by unfold majorant; fun_prop)
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold majorant; positivity)]
  have hv : 0 ≤ |v| := abs_nonneg v
  have hpoly : (1+|v|)^3 ≤ 16*(1+v^4) := by
    by_cases h : |v| ≤ 1
    · have hh : (1+|v|)^3 ≤ (2:ℝ)^3 := by gcongr; linarith
      nlinarith [show 0 ≤ v^4 by positivity]
    · have h1 : 1 ≤ |v| := le_of_not_ge h
      have hh : (1+|v|)^3 ≤ (2*|v|)^3 := by gcongr; linarith
      have hp : |v|^3 ≤ |v|^4 := pow_le_pow_right₀ h1 (by norm_num : 3 ≤ 4)
      rw [show |v|^4 = v^4 from by rw [pow_abs]; exact abs_of_nonneg (by positivity)] at hp
      nlinarith
  dsimp [majorant]
  nlinarith [mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-v^2)).le]

theorem left_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (v : ℝ) :
    ‖integrand sigma X ((-(1/8:ℝ):ℂ)+(v:ℂ)*I)‖ ≤
      (256*Real.exp 4)*(1+16/‖sigma‖^2)*X^(-(1/8:ℝ))*majorant v := by
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  have hw : (1/8:ℝ) ≤ ‖(-(1/8:ℝ):ℂ)+(v:ℂ)*I‖ :=
    (by norm_num : (1/8:ℝ) ≤ |(-(1/8:ℝ))|).trans
      (by simpa using abs_re_le_norm ((-(1/8:ℝ):ℂ)+(v:ℂ)*I))
  have hp : (1/8:ℝ) ≤ ‖1-(1+sigma+2*((-(1/8:ℝ):ℂ)+(v:ℂ)*I))‖ := by
    have hh := abs_re_le_norm (1-(1+sigma+2*((-(1/8:ℝ):ℂ)+(v:ℂ)*I)))
    have he : (1-(1+sigma+2*((-(1/8:ℝ):ℂ)+(v:ℂ)*I))).re = 1/4-sigma.re := by simp; ring
    rw [he,abs_of_nonneg (by linarith)] at hh
    linarith
  simpa [majorant,mul_assoc] using strip_bound sigma hs hn X hX
    ((-(1/8:ℝ):ℂ)+(v:ℂ)*I) (by simp) (by norm_num) hw hp

/-- An actual integrable shifted contour with uniform shift dependence.
The remaining main-term subtraction still needs the contour identity. -/
theorem left_error_bound : ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℂ) (X : ℝ),
    sigma ≠ 0 → ‖sigma‖ ≤ 1/8 → 0 < X →
    ‖(1/(2*Real.pi):ℂ)*∫ v : ℝ,
      integrand sigma X ((-(1/8:ℝ):ℂ)+(v:ℂ)*I)‖ ≤
      C*(1+16/‖sigma‖^2)*X^(-(1/8:ℝ)) := by
  let J := ∫ v : ℝ, majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by unfold majorant; positivity)
  refine ⟨(256*Real.exp 4)/(2*Real.pi)*(J+1),by positivity,?_⟩
  intro sigma X hs hn hX
  let B := (256*Real.exp 4)*(1+16/‖sigma‖^2)*X^(-(1/8:ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi : Integrable (fun v : ℝ => integrand sigma X ((-(1/8:ℝ):ℂ)+(v:ℂ)*I)) := by
    apply (majorant_integrable.const_mul B).mono'
    · apply Continuous.aestronglyMeasurable
      apply continuous_iff_continuousAt.mpr
      intro v
      have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
      have hz : 1+sigma+2*((-(1/8:ℝ):ℂ)+(v:ℂ)*I) ≠ 1 := by
        intro he; have hh := congrArg Complex.re he
        simp at hh
        linarith
      have hc := (differentiableAt_riemannZeta hz).continuousAt.comp
        (f := fun v : ℝ => 1+sigma+2*((-(1/8:ℝ):ℂ)+(v:ℂ)*I)) (by fun_prop)
      unfold integrand amplitude annihilator
      have hx : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
      simp_rw [Complex.cpow_def_of_ne_zero hx]
      fun_prop (disch := norm_num; intro he; have hh := congrArg Complex.re he; norm_num at hh)
    · exact Filter.Eventually.of_forall (fun v => left_bound sigma hs hn X hX v)
  have hh := integral_mono hi.norm (majorant_integrable.const_mul B)
    (fun v => left_bound sigma hs hn X hX v)
  rw [integral_const_mul] at hh
  have hnrm := (norm_integral_le_integral_norm _).trans hh
  rw [norm_mul]
  have hc : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hc]
  apply (mul_le_mul_of_nonneg_left hnrm (by positivity)).trans
  calc
    _ ≤ (1/(2*Real.pi))*(B*(J+1)) := by
      dsimp [J]
      gcongr
      linarith
    _ = _ := by dsimp [B]; ring

theorem integrand_differentiable (sigma : ℂ) (X : ℝ) (hX : 0 < X) (w : ℂ)
    (hw : w ≠ 0) (hp : w ≠ -sigma/2) :
    DifferentiableAt ℂ (integrand sigma X) w := by
  have hz : 1+sigma+2*w ≠ 1 := by
    intro he; apply hp; linear_combination he/2
  have hd := (differentiableAt_riemannZeta hz).comp w
    (show DifferentiableAt ℂ (fun w : ℂ => 1+sigma+2*w) w by fun_prop)
  unfold integrand amplitude annihilator
  have hx : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hx]
  fun_prop

/-- The actual finite residue identity: central zeta main factor plus
the annihilated possible pole, with all analytic hypotheses supplied. -/
theorem finite_rectangle (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X H : ℝ) (hX : 0 < X) (hH : 1 < H) :
    RectangleIntegral' (integrand sigma X)
      ((-(1/8:ℝ):ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I) = riemannZeta (1+sigma) := by
  classical
  let p : ℂ := -sigma/2
  let S : Finset ℂ := {0,p}
  have hp : p ≠ 0 := div_ne_zero (neg_ne_zero.mpr hs) (by norm_num)
  have hd : ∀ w, w ∉ S → DifferentiableAt ℂ (integrand sigma X) w := by
    intro w hw
    apply integrand_differentiable sigma X hX w
    · intro he; apply hw; simp [S,he]
    · intro he; apply hw; simp [S,p,he]
  have hi : ∀ q ∈ S,
      Rectangle ((-(1/8:ℝ):ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I) ∈ 𝓝 q := by
    intro q hq
    have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
    have him := abs_le.mp ((abs_im_le_norm sigma).trans hn)
    rw [rectangle_mem_nhds_iff,mem_reProdIm]
    have hre : ((-(1/8:ℝ):ℂ)-(H:ℂ)*I).re ≤ ((2:ℂ)+(H:ℂ)*I).re := by norm_num
    have him' : ((-(1/8:ℝ):ℂ)-(H:ℂ)*I).im ≤ ((2:ℂ)+(H:ℂ)*I).im := by simp; linarith
    rw [Set.uIoo_of_le hre,Set.uIoo_of_le him']
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;>
      simp [p] <;> (repeat' constructor) <;> linarith
  have hpp : ∀ q ∈ S,
      ((integrand sigma X) - fun w => residue (integrand sigma X) q/(w-q))
        =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
    intro q hq
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [central_residue sigma hs X hX]
      apply PRZZFiniteContour.principal_part_of_limit _ S _ _ hd
      simpa only [sub_zero] using central_limit sigma hs X hX
    · rw [canceled_residue sigma hs X hX]
      exact PRZZFiniteContour.principal_part_of_limit _ S _ _ hd
        (canceled_limit sigma hs X hX)
  have h := Zeta23.Analytic.residueTheorem_finset
    (f := integrand sigma X)
    (z := ((-(1/8:ℝ):ℂ)-(H:ℂ)*I)) (w := ((2:ℂ)+(H:ℂ)*I))
    (by norm_num) (by simp; linarith) S (residue (integrand sigma X)) hi
    (by intro w hw; exact (hd w hw.2).differentiableWithinAt) hpp
  have hsum : (∑ q ∈ S, residue (integrand sigma X) q) = riemannZeta (1+sigma) := by
    dsimp [S]
    rw [Finset.sum_insert (by simpa using hp.symm),Finset.sum_singleton,
      central_residue sigma hs X hX]
    have hc : residue (integrand sigma X) p = 0 := canceled_residue sigma hs X hX
    rw [hc,add_zero]
  exact h.trans hsum

theorem vertical_geometry (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (c v : ℝ)
    (hc : c = -(1/8:ℝ) ∨ c = 2) :
    (1/8:ℝ) ≤ ‖(c:ℂ)+(v:ℂ)*I‖ ∧
      (1/8:ℝ) ≤ ‖1-(1+sigma+2*((c:ℂ)+(v:ℂ)*I))‖ := by
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  constructor
  · have hh := abs_re_le_norm ((c:ℂ)+(v:ℂ)*I)
    rcases hc with rfl | rfl <;> norm_num at hh ⊢ <;> linarith
  · have hh := abs_re_le_norm (1-(1+sigma+2*((c:ℂ)+(v:ℂ)*I)))
    have he : (1-(1+sigma+2*((c:ℂ)+(v:ℂ)*I))).re = -sigma.re-2*c := by simp; ring
    rw [he] at hh
    rcases hc with rfl | rfl
    · rw [abs_of_nonneg (by linarith)] at hh
      linarith
    · rw [abs_of_nonpos (by linarith)] at hh
      linarith

theorem vertical_continuous (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (X c : ℝ) (hX : 0 < X) (hc : c = -(1/8:ℝ) ∨ c = 2) :
    Continuous (fun v : ℝ => integrand sigma X ((c:ℂ)+(v:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hg := vertical_geometry sigma hn c v hc
  have hw : (c:ℂ)+(v:ℂ)*I ≠ 0 := by intro he; norm_num [he] at hg
  have hp : (c:ℂ)+(v:ℂ)*I ≠ -sigma/2 := by
    intro he
    have hz : 1-(1+sigma+2*((c:ℂ)+(v:ℂ)*I)) = 0 := by rw [he]; ring
    rw [hz,norm_zero] at hg
    norm_num at hg
  exact (integrand_differentiable sigma X hX _ hw hp).continuousAt.comp
    (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) (by fun_prop)

theorem vertical_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X c : ℝ) (hX : 0 < X) (hc : c = -(1/8:ℝ) ∨ c = 2) :
    Integrable (fun v : ℝ => integrand sigma X ((c:ℂ)+(v:ℂ)*I)) := by
  let B := (256*Real.exp 4)*(1+16/‖sigma‖^2)*X^c
  apply (majorant_integrable.const_mul B).mono'
    (vertical_continuous sigma hn X c hX hc).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  have hg := vertical_geometry sigma hn c v hc
  have hh := strip_bound sigma hs hn X hX ((c:ℂ)+(v:ℂ)*I)
    (by rcases hc with rfl | rfl <;> norm_num)
    (by rcases hc with rfl | rfl <;> norm_num) hg.1 hg.2
  simpa [B,majorant,mul_assoc] using hh

theorem horizontal_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -(1/8:ℝ) ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖integrand sigma X w‖ ≤ C*(1+|w.im|)^4*Real.exp (-w.im^2) := by
  let C := (256*Real.exp 4)*(1+16/‖sigma‖^2)*Real.exp (2*|Real.log X|)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro w hlo hhi him
  have hw : (1/8:ℝ) ≤ ‖w‖ := by linarith [abs_im_le_norm w]
  have hp : (1/8:ℝ) ≤ ‖1-(1+sigma+2*w)‖ := by
    have hi := (abs_im_le_norm sigma).trans hn
    have hh := abs_sub_le (sigma.im+2*w.im) 0 sigma.im
    simp only [sub_zero,zero_sub,abs_neg] at hh
    rw [show sigma.im+2*w.im-sigma.im = 2*w.im by ring,abs_mul] at hh
    have hb := abs_im_le_norm (1-(1+sigma+2*w))
    have he : (1-(1+sigma+2*w)).im = -(sigma.im+2*w.im) := by simp
    rw [he,abs_neg] at hb
    norm_num at hh
    linarith
  have hpow : X^w.re ≤ Real.exp (2*|Real.log X|) := by
    rw [Real.rpow_def_of_pos hX]
    apply Real.exp_le_exp.mpr
    have hre : |w.re| ≤ 2 := abs_le.mpr ⟨by linarith,hhi⟩
    have hm := mul_le_mul_of_nonneg_left hre (abs_nonneg (Real.log X))
    have hh := le_abs_self (Real.log X*w.re)
    rw [abs_mul] at hh
    nlinarith
  have h3 : (1+|w.im|)^3 ≤ (1+|w.im|)^4 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg w.im]) (by norm_num : 3 ≤ 4)
  apply (strip_bound sigma hs hn X hX w hlo hhi hw hp).trans
  dsimp [C]
  gcongr

theorem horizontal_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (e : ℝ) (he : |e| = 1) :
    Tendsto (fun H : ℝ => ∫ c in (-(1/8:ℝ))..2,
      integrand sigma X ((c:ℂ)+(e*H:ℝ)*I)) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := horizontal_bound sigma hs hn X hX
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun H => norm_nonneg _)) _
    (by simpa using PRZZHorizontalDecay.majorant_tendsto.const_mul ((17/8:ℝ)*C))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with H hH
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-(1/8:ℝ))) (b := 2) (C := C*(1+H)^4*Real.exp (-H^2))
    (f := fun c : ℝ => integrand sigma X ((c:ℂ)+(e*H:ℝ)*I)) (by
      intro c hc
      have hh : c ∈ Ioc (-(1/8:ℝ)) 2 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-(1/8:ℝ)) ≤ 2)] using hc
      have hb := h ((c:ℂ)+(e*H:ℝ)*I) (by simpa using hh.1.le)
        (by simpa using hh.2) (by simpa [abs_mul,he,abs_of_nonneg (by linarith : 0 ≤ H)] using hH)
      simpa [abs_mul,he,abs_of_nonneg (by linarith : 0 ≤ H),← sq_abs (e*H),add_comm] using hb)
  norm_num at hb
  simpa [add_comm,mul_assoc,mul_left_comm,mul_comm] using hb

/-- Infinite diagonal contour shift, including vanished horizontal edges
and both absolutely convergent vertical integrals. -/
theorem shifted_identity (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    diagonal sigma X-riemannZeta (1+sigma) =
      (1/(2*Real.pi):ℂ)*∫ v : ℝ,
        integrand sigma X ((-(1/8:ℝ):ℂ)+(v:ℂ)*I) := by
  let f := integrand sigma X
  have hb : Tendsto (fun H : ℝ => HIntegral f (-(1/8)) 2 (-H)) atTop (𝓝 0) := by
    simpa [f,HIntegral] using horizontal_limit sigma hs hn X hX (-1) (by norm_num)
  have ht : Tendsto (fun H : ℝ => HIntegral f (-(1/8)) 2 H) atTop (𝓝 0) := by
    simpa [f,HIntegral] using horizontal_limit sigma hs hn X hX 1 (by norm_num)
  have hv (c : ℝ) (hc : c = -(1/8:ℝ) ∨ c = 2) :
      Tendsto (fun H : ℝ => ∫ v in -H..H, f ((c:ℂ)+(v:ℂ)*I)) atTop
        (𝓝 (∫ v : ℝ, f ((c:ℂ)+(v:ℂ)*I))) :=
    intervalIntegral_tendsto_integral (vertical_integrable sigma hs hn X c hX hc)
      tendsto_neg_atTop_atBot tendsto_id
  have hlim := (((hb.sub ht).add ((hv 2 (Or.inr rfl)).const_mul I)).sub
    ((hv (-(1/8)) (Or.inl rfl)).const_mul I)).const_mul (1/(2*(Real.pi:ℂ)*I))
  have hl : Tendsto (fun H : ℝ => RectangleIntegral' f
      ((-(1/8:ℝ):ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) atTop
      (𝓝 ((1/(2*(Real.pi:ℂ)*I))*(I*(∫ v : ℝ, f (2+(v:ℂ)*I))-
        I*(∫ v : ℝ, f ((-(1/8:ℝ):ℂ)+(v:ℂ)*I))))) := by
    simpa [RectangleIntegral',RectangleIntegral,VIntegral,smul_eq_mul,f] using hlim
  have hevent : (fun H : ℝ => RectangleIntegral' f
      ((-(1/8:ℝ):ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) =ᶠ[atTop]
      (fun _ => riemannZeta (1+sigma)) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with H hH
    exact finite_rectangle sigma hs hn X H hX hH
  have heq := tendsto_nhds_unique hl (tendsto_const_nhds.congr' hevent.symm)
  have hscalar : (1/(2*(Real.pi:ℂ)*I))*I = (1/(2*Real.pi):ℂ) := by field_simp
  rw [← mul_sub,← mul_assoc,hscalar] at heq
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  have hm := diagonal_mellin sigma hs (by linarith : -1 ≤ sigma.re) X hX
  change diagonal sigma X = (1/(2*Real.pi):ℂ)*∫ v : ℝ, f (2+(v:ℂ)*I) at hm
  rw [mul_sub,← hm] at heq
  linear_combination heq

/-- Quantitative primitive diagonal main term, with a single constant
chosen before the shift and height scale. -/
theorem diagonal_error : ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℂ) (X : ℝ),
    sigma ≠ 0 → ‖sigma‖ ≤ 1/8 → 0 < X →
    ‖diagonal sigma X-riemannZeta (1+sigma)‖ ≤
      C*(1+16/‖sigma‖^2)*X^(-(1/8:ℝ)) := by
  obtain ⟨C,hC,h⟩ := left_error_bound
  refine ⟨C,hC,?_⟩
  intro sigma X hs hn hX
  rw [shifted_identity sigma hs hn X hX]
  exact h sigma X hs hn hX

/-- The actual logarithmic shift family has only the displayed quadratic
logarithmic singularity cost. The constant is chosen before all shifts,
height and primitive diagonal scale. -/
theorem scaled_diagonal_error (S r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ X : ℝ, 0 < X →
      ‖diagonal ((A+B)/(Real.log T:ℂ)) X-
        riemannZeta (1+(A+B)/(Real.log T:ℂ))‖ ≤
        C*(1+16*(Real.log T)^2/r^2)*X^(-(1/8:ℝ)) := by
  obtain ⟨C,hC,h⟩ := diagonal_error
  refine ⟨C,hC,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (max (16*S) 0))] with T hT
  have hL : 0 < Real.log T := lt_of_le_of_lt (le_max_right _ _) hT
  have hSL : 16*S ≤ Real.log T := (le_max_left _ _).trans hT.le
  intro A B hA hB hsep X hX
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply (div_le_iff₀ hL).mpr
    have hh := norm_add_le A B
    linarith
  have hh := h ((A+B)/(Real.log T:ℂ)) X (div_ne_zero hab hLc) hn hX
  have he : 16/‖(A+B)/(Real.log T:ℂ)‖^2 = 16*(Real.log T)^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

#print axioms scaled_diagonal_error
#print axioms horizontal_bound
#print axioms horizontal_limit
#print axioms shifted_identity
#print axioms diagonal_error
#print axioms vertical_geometry
#print axioms vertical_continuous
#print axioms vertical_integrable
#print axioms integrand_differentiable
#print axioms finite_rectangle
#print axioms strip_bound
#print axioms majorant_integrable
#print axioms left_bound
#print axioms left_error_bound
end XiPrime8845.PRZZDiagonalContour
