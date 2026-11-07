import PRZZSeriesAFE
import PRZZSourceW

/-! The primitive one-variable W diagonal and its actual zeta Mellin
integral. Absolute-integral summability is supplied before exchanging the
series and integral. Local residue calculations are separate from an
infinite contour shift and its quantitative remainder. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZDiagonalMellin
open PRZZDyadicEnvelope PRZZGaussianLine
set_option maxHeartbeats 4000000

def amplitude (sigma : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  (X:ℂ)^w*Complex.exp (w^2)*annihilator sigma w/w

def integrand (sigma : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  amplitude sigma X w*riemannZeta (1+sigma+2*w)

def term (sigma : ℂ) (X : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  amplitude sigma X (line v)/((n+1:ℕ):ℂ)^(1+sigma+2*line v)

def diagonal (sigma : ℂ) (X : ℝ) : ℂ :=
  ∑' n : ℕ, sourceW sigma (((n+1:ℕ):ℝ)^2/X)/((n+1:ℕ):ℂ)^(1+sigma)

theorem reciprocal_power (X : ℝ) (hX : 0 < X) (w : ℂ) :
    ((X⁻¹:ℝ):ℂ)^(-w) = (X:ℂ)^w := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (inv_ne_zero hX.ne')),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hX.ne'),
    ← Complex.ofReal_log (by positivity),← Complex.ofReal_log hX.le,Real.log_inv,
    Complex.ofReal_neg]
  congr 1
  ring

theorem amplitude_integrable (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    Integrable (fun v : ℝ => amplitude sigma X (line v)) := by
  have hi := PRZZSourceW.source_integrable sigma hs X⁻¹ (by positivity)
  simpa only [reciprocal_power X hX,amplitude] using hi

theorem power_factor (n X : ℝ) (hn : 0 < n) (hX : 0 < X) (sigma w : ℂ) :
    (((n^2/X:ℝ):ℂ)^(-w))/((n:ℂ)^(1+sigma)) =
      (X:ℂ)^w/(n:ℂ)^(1+sigma+2*w) := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpC : ((n^2/X:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : 0 < n^2/X))
  have hl : Complex.log ((n^2/X:ℝ):ℂ) =
      2*(Real.log n:ℂ)-(Real.log X:ℂ) := by
    rw [← Complex.ofReal_log (by positivity),Real.log_div (by positivity) hX.ne',Real.log_pow]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hpC,Complex.cpow_def_of_ne_zero hnC,
    Complex.cpow_def_of_ne_zero hXC,Complex.cpow_def_of_ne_zero hnC,
    hl,← Complex.ofReal_log hn.le,← Complex.ofReal_log hX.le]
  simp only [div_eq_mul_inv,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  ring

theorem term_integral (sigma : ℂ) (X : ℝ) (hX : 0 < X) (n : ℕ) :
    (1/(2*Real.pi):ℂ)*(∫ v : ℝ, term sigma X n v) =
      sourceW sigma (((n+1:ℕ):ℝ)^2/X)/((n+1:ℕ):ℂ)^(1+sigma) := by
  have he (v : ℝ) : term sigma X n v =
      ((((n+1:ℕ):ℝ)^2/X:ℝ):ℂ)^(-line v)*Complex.exp ((line v)^2)*
        annihilator sigma (line v)/line v /((n+1:ℕ):ℂ)^(1+sigma) := by
    have hp := power_factor ((n+1:ℕ):ℝ) X (by positivity) hX sigma (line v)
    simp only [Complex.ofReal_natCast] at hp
    unfold term amplitude
    calc
      _ = ((X:ℂ)^line v/((n+1:ℕ):ℂ)^(1+sigma+2*line v)) *
          (Complex.exp ((line v)^2)*annihilator sigma (line v)/line v) := by ring
      _ = _ := by rw [← hp]; ring
  simp_rw [he]
  rw [integral_div]
  unfold sourceW
  change _ = ((1/(2*Real.pi):ℂ)*∫ v : ℝ,
    ((((n+1:ℕ):ℝ)^2/X:ℝ):ℂ)^(-line v)*Complex.exp ((line v)^2)*
      annihilator sigma (line v)/line v)/((n+1:ℕ):ℂ)^(1+sigma)
  ring

theorem term_bound (sigma : ℂ) (X v : ℝ) (n : ℕ) (hr : -1 ≤ sigma.re) :
    ‖term sigma X n v‖ ≤
      ‖amplitude sigma X (line v)‖*(1/((n+1:ℕ):ℝ)^4) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have hd : ((n+1:ℕ):ℝ)^4 ≤ ‖((n+1:ℕ):ℂ)^(1+sigma+2*line v)‖ := by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hn,← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.le_add_left 1 n))
    simp [line]
    linarith
  rw [term,norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd).trans_eq (by ring)

theorem absolute_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (X : ℝ) (hX : 0 < X) :
    (∀ n, Integrable (term sigma X n)) ∧
      Summable (fun n : ℕ => ∫ v : ℝ, ‖term sigma X n v‖) := by
  have hi := amplitude_integrable sigma hs X hX
  have hj (n : ℕ) : Integrable (term sigma X n) := by
    apply (hi.norm.mul_const (1/((n+1:ℕ):ℝ)^4)).mono'
    · have hc : Continuous (fun v : ℝ => term sigma X n v) := by
        have hn : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
        have hx : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
        have ha : Continuous (fun v : ℝ => amplitude sigma X (line v)) := by
          unfold amplitude annihilator line
          simp_rw [Complex.cpow_def_of_ne_zero hx]
          fun_prop (disch := intro v he; have hh := congrArg Complex.re he; simp at hh)
        have hd : Continuous (fun v : ℝ => ((n+1:ℕ):ℂ)^(1+sigma+2*line v)) := by
          simp_rw [Complex.cpow_def_of_ne_zero hn]
          unfold line
          fun_prop
        exact ha.div hd (fun v => Complex.cpow_ne_zero_iff.mpr (Or.inl hn))
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun v => term_bound sigma X v n hr)
  refine ⟨hj,?_⟩
  have hp : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)^4) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
  apply (hp.mul_left (∫ v : ℝ, ‖amplitude sigma X (line v)‖)).of_nonneg_of_le
  · intro n; exact integral_nonneg (fun v => norm_nonneg _)
  · intro n
    have hh := integral_mono (hj n).norm (hi.norm.mul_const (1/((n+1:ℕ):ℝ)^4))
      (fun v => term_bound sigma X v n hr)
    simpa only [integral_mul_const] using hh

theorem zeta_expansion (sigma : ℂ) (X v : ℝ) (hr : -1 ≤ sigma.re) :
    integrand sigma X (line v) = ∑' n : ℕ, term sigma X n v := by
  have hre : 1 < (1+sigma+2*line v).re := by simp [line]; linarith
  rw [integrand,zeta_eq_tsum_one_div_nat_add_one_cpow hre,← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [term,Nat.cast_add,Nat.cast_one]
  ring

/-- The genuine primitive diagonal W series, not an assumed Mellin
representation. In particular the Mellin normalization is 1/(2*pi). -/
theorem diagonal_mellin (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (X : ℝ) (hX : 0 < X) :
    diagonal sigma X = (1/(2*Real.pi):ℂ)*∫ v : ℝ, integrand sigma X (line v) := by
  obtain ⟨hi,ha⟩ := absolute_exchange sigma hs hr X hX
  simp_rw [zeta_expansion sigma X _ hr]
  rw [← integral_tsum_of_summable_integral_norm hi ha,← tsum_mul_left]
  exact (tsum_congr (fun n => term_integral sigma X hX n)).symm

/-- The central residue is exactly the diagonal zeta main factor. -/
theorem central_limit (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    Tendsto (fun w : ℂ => w*integrand sigma X w) (𝓝[≠] 0)
      (𝓝 (riemannZeta (1+sigma))) := by
  let f := fun w : ℂ => (X:ℂ)^w*Complex.exp (w^2)*annihilator sigma w*
    riemannZeta (1+sigma+2*w)
  have hz : ContinuousAt (fun w : ℂ => riemannZeta (1+sigma+2*w)) 0 :=
    (differentiableAt_riemannZeta (s := 1+sigma+2*0) (by
      intro he; apply hs; linear_combination he)).continuousAt.comp
        (f := fun w : ℂ => 1+sigma+2*w) (by fun_prop)
  have hf : ContinuousAt f 0 := by
    unfold f annihilator
    have hx : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    simp_rw [Complex.cpow_def_of_ne_zero hx]
    fun_prop
  have he : f 0 = riemannZeta (1+sigma) := by
    simp [f,annihilator,hs]
  have ht := hf.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := hw
  dsimp [f,integrand,amplitude]
  field_simp

theorem central_residue (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    residue (integrand sigma X) 0 = riemannZeta (1+sigma) := by
  apply residue_eq_of_tendsto
  simpa only [sub_zero] using central_limit sigma hs X hX

/-- The shift annihilator removes the zeta pole in the residue sum.
This computes its residue; it does not yet bound a shifted vertical line. -/
theorem canceled_limit (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    Tendsto (fun w : ℂ => (w-(-sigma/2))*integrand sigma X w)
      (𝓝[≠] (-sigma/2)) (𝓝 0) := by
  let p : ℂ := -sigma/2
  have hp : p ≠ 0 := by dsimp [p]; exact div_ne_zero (neg_ne_zero.mpr hs) (by norm_num)
  have hmap : Tendsto (fun w : ℂ => 1+sigma+2*w) (𝓝[≠] p) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (show ContinuousAt (fun w : ℂ => 1+sigma+2*w) p by fun_prop).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({p}ᶜ : Set ℂ))) using 1
      dsimp [p]; congr 1; ring
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro he
      change 1+sigma+2*w = 1 at he
      apply hw
      change w = p
      dsimp [p]
      linear_combination he/2
  have hz := riemannZeta_residue_one.comp hmap
  let g := fun w : ℂ => (X:ℂ)^w*Complex.exp (w^2)*annihilator sigma w/(2*w)
  have hg : ContinuousAt g p := by
    unfold g annihilator
    have hx : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    simp_rw [Complex.cpow_def_of_ne_zero hx]
    fun_prop (disch := norm_num [hs,hp])
  have he : g p = 0 := by
    dsimp [g,p,annihilator]
    have h : sigma^2-(2*(-sigma/2))^2 = 0 := by ring
    rw [h]
    simp
  have ht := (hg.tendsto.mono_left (nhdsWithin_le_nhds (s := ({p}ᶜ : Set ℂ)))).mul hz
  rw [he,zero_mul] at ht
  apply ht.congr'
  filter_upwards with w
  dsimp [g,integrand,amplitude,p]
  ring

theorem canceled_residue (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    residue (integrand sigma X) (-sigma/2) = 0 := by
  exact residue_eq_of_tendsto (canceled_limit sigma hs X hX)

#print axioms central_limit
#print axioms central_residue
#print axioms canceled_limit
#print axioms canceled_residue
#print axioms reciprocal_power
#print axioms amplitude_integrable
#print axioms power_factor
#print axioms term_integral
#print axioms term_bound
#print axioms absolute_exchange
#print axioms zeta_expansion
#print axioms diagonal_mellin
end XiPrime8845.PRZZDiagonalMellin
