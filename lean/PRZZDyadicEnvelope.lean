import PRZZDyadicWindow
import PRZZSmoothWeights
import PRZZOuterMass
import PRZZMellinMoment

/-! Scale-uniform elementary envelopes on the sharp dyadic window.
The source pole annihilator depends on the shifts: its inverse-square
cost is explicit. Bounds on the actual inverse Mellin W are NOT supplied
by continuity of a fixed W; its Gaussian evaluation and uniform bound
are proved separately in PRZZSourceW. -/
noncomputable section
open scoped ContDiff
open Set MeasureTheory Complex
namespace XiPrime8845.PRZZDyadicEnvelope
open PRZZDyadicWindow PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem inverse_power (T K S x : ℝ) (z : ℂ) (hL : 0 < Real.log T)
    (hx : 0 < x) (hS : 0 ≤ S) (hlog : |Real.log x| ≤ K*Real.log T)
    (hz : |z.re| ≤ S/Real.log T) :
    ‖((x:ℂ)^z)⁻¹‖ ≤ Real.exp (K*S) := by
  have hh := mul_le_mul hz hlog (abs_nonneg _) (div_nonneg hS hL.le)
  have he : S/Real.log T*(K*Real.log T) = K*S := by field_simp
  rw [he] at hh
  have hb : -(Real.log x*z.re) ≤ K*S := by
    calc
      _ ≤ |Real.log x*z.re| := neg_le_abs _
      _ = |z.re| * |Real.log x| := by rw [abs_mul,mul_comm]
      _ ≤ _ := hh
  rw [norm_inv,Complex.norm_cpow_eq_rpow_re_of_pos hx,Real.rpow_def_of_pos hx,← Real.exp_neg]
  exact Real.exp_le_exp.mpr hb

theorem dyadic_log_bound (T M V K x : ℝ) (hL : 1 ≤ Real.log T)
    (hM : 0 < M) (hV : 0 < V) (_hK : 0 ≤ K)
    (hscale : |Real.log M|+|Real.log V| ≤ K*Real.log T)
    (hx : x ∈ Icc (M/(4*V)) (3*M/V)) :
    |Real.log x| ≤ (K+Real.log 4)*Real.log T := by
  have hx0 : 0 < x := (div_pos hM (by positivity)).trans_le hx.1
  have hlo := Real.log_le_log (div_pos hM (by positivity : 0 < 4*V)) hx.1
  have hhi := Real.log_le_log hx0 hx.2
  rw [Real.log_div hM.ne' (by positivity),Real.log_mul (by norm_num) hV.ne'] at hlo
  rw [Real.log_div (by positivity) hV.ne',Real.log_mul (by norm_num) hM.ne'] at hhi
  have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hL h4
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo,hhi,hscale,h34,hh,
    le_abs_self (Real.log M),neg_abs_le (Real.log M),
    le_abs_self (Real.log V),neg_abs_le (Real.log V)]

/-- One pair of constants works for every dilation, including the x*f'(x)
variation envelope. No M- or N-dependent compactness constant is used. -/
theorem scaled_cutoffs (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ Q x : ℝ,
      ‖scaledCutoff F Q x‖ ≤ C0 ∧ ‖(x:ℂ)*deriv (scaledCutoff F Q) x‖ ≤ C1 :=
  PRZZSmoothWeights.cutoff_bounds F hF hs

/-- The polynomial p(w) in [58], (2.1). The missing sigma=0 extension is
not silently chosen. Applications use the explicit separation below. -/
def annihilator (sigma w : ℂ) : ℂ := (sigma^2-(2*w)^2)/sigma^2

/-- Literal [58] (2.1), parametrizing the vertical line by w=2+it.
The source application requires sigma != 0 and x > 0. A closed Gaussian
evaluation and global positive-x bound are supplied by PRZZSourceW. -/
def sourceW (sigma : ℂ) (x : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ t : ℝ,
    (x:ℂ)^(-(2+(t:ℂ)*I))*Complex.exp ((2+(t:ℂ)*I)^2)*
      annihilator sigma (2+(t:ℂ)*I)/(2+(t:ℂ)*I)

theorem annihilator_bound (sigma w : ℂ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hsep : r/L ≤ ‖sigma‖) :
    ‖annihilator sigma w‖ ≤ 1+4*‖w‖^2*(L/r)^2 := by
  have hs : sigma ≠ 0 := norm_pos_iff.mp ((div_pos hr hL).trans_le hsep)
  have hinv : ‖sigma‖⁻¹ ≤ L/r := by
    have hh := one_div_le_one_div_of_le (div_pos hr hL) hsep
    simpa [one_div] using hh
  have he : annihilator sigma w = 1-(2*w)^2/sigma^2 := by
    unfold annihilator; field_simp
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_one,norm_div,norm_pow,norm_pow,norm_mul]
  norm_num
  have hh := mul_le_mul hinv hinv (inv_nonneg.mpr (norm_nonneg _)) (by positivity : 0 ≤ L/r)
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*‖w‖^2)
  rw [div_eq_mul_inv,← inv_pow]
  simp only [pow_two] at hmul ⊢
  nlinarith only [hmul]

theorem annihilator_scaled (A B w : ℂ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hab : r ≤ ‖A+B‖) :
    ‖annihilator ((A+B)/(L:ℂ)) w‖ ≤ 1+4*‖w‖^2*(L/r)^2 := by
  apply annihilator_bound _ w L r hL hr
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  exact div_le_div_of_nonneg_right hab hL.le

def common (d : ℕ) (T M X V : ℝ) (W : ℝ → ℂ) (z : ℂ) : ℝ × ℝ → ℂ :=
  (box T M X V).indicator (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^z))

theorem common_integrable (d : ℕ) (T M X V : ℝ) (W : ℝ → ℂ) (z : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hW : ContinuousOn W (Ioi 0)) : Integrable (common d T M X V W z) := by
  apply (integrable_indicator_iff (isCompact_Icc.prod isCompact_Icc).measurableSet).mpr
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hx : ∀ p ∈ box T M X V, 0 < p.1 := fun p hp => (div_pos hM (by positivity)).trans_le hp.1.1
  have hy : ∀ p ∈ box T M X V, 0 < p.2 := fun p hp => (div_pos hT (by positivity)).trans_le hp.2.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)^z) (box T M X V) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.cpow_const
      (fun p hp => by simpa using hx p hp)
  apply ContinuousOn.div
  · apply hW.comp
      ((continuousOn_const.mul continuous_fst.continuousOn).div continuous_snd.continuousOn
        (fun p hp => (hy p hp).ne'))
    intro p hp
    exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hx p hp)) (hy p hp)
  · exact continuousOn_const.mul hc
  · intro p hp
    exact mul_ne_zero (by exact_mod_cast hd.ne')
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne')))

/-- Uniform elementary outer cost. CW is the explicit W envelope, not
assumed to be a constant independent of the shifts or height. -/
theorem common_mass (d : ℕ) (T M X V K S CW : ℝ) (W : ℝ → ℂ) (z : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hL : 1 ≤ Real.log T) (hK : 0 ≤ K) (hS : 0 ≤ S) (hCW : 0 ≤ CW)
    (hscale : |Real.log M|+|Real.log V| ≤ K*Real.log T)
    (hz : |z.re| ≤ S/Real.log T) (hW : ContinuousOn W (Ioi 0))
    (hbound : ∀ x > 0, ‖W x‖ ≤ CW) :
    (∫ p, ‖common d T M X V W z p‖) ≤
      24*(CW*Real.exp ((K+Real.log 4)*S))*T/((d:ℝ)*X*V) := by
  apply mass_bound T M X V _ d hT hM hX hV (by positivity) (by exact_mod_cast hd)
    _ (common_integrable d T M X V W z hd hT hM hX hV hW)
  · intro p hp
    by_contra hh
    exact hp (by simp [common,hh])
  · intro p hp
    have hx : 0 < p.1 := (div_pos hM (by positivity)).trans_le hp.1.1
    have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hp.2.1
    have hw := hbound _ (by positivity : 0 < 2*Real.pi*p.1/p.2)
    have hi := inverse_power T (K+Real.log 4) S p.1 z (by linarith) hx hS
      (dyadic_log_bound T M V K p.1 hL hM hV hK hscale hp.1) hz
    simp only [common,Set.indicator_of_mem hp,norm_div,norm_mul,Complex.norm_natCast]
    have hh := mul_le_mul hw hi (norm_nonneg _) hCW
    rw [norm_inv] at hh
    simpa [div_eq_mul_inv,mul_inv,mul_assoc,mul_comm,mul_left_comm] using
      div_le_div_of_nonneg_right hh (by positivity : (0:ℝ) ≤ d)

/-- The actual signed frequency sum, on the retained dyadic window.
No estimate on a different arithmetic sum is substituted here. -/
theorem arithmetic_integral_bound (N d : ℕ) (D H T M X V B0 : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hB : 0 ≤ B0) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hb : ∀ p ∈ box T M X V, ∀ t : ℝ,
      ‖PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ B0*(1+|t|)) :
    ‖∫ t : ℝ, ∫ p : ℝ × ℝ, common d T M X V W (α+β) p *
      mellin Phi (t*I)*twist (p.1*p.2/T) t *
      PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤
      (∫ p, ‖common d T M X V W (α+β) p‖)*B0*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let J := fun (p : ℝ × ℝ) (t : ℝ) => common d T M X V W (α+β) p *
    mellin Phi (t*I)*twist (p.1*p.2/T) t *
    PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t
  let m := ∫ p, ‖common d T M X V W (α+β) p‖
  have hc := common_integrable d T M X V W (α+β) hd hT hM hX hV hW
  have hw : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hp : ∀ p t, ‖J p t‖ ≤
      ‖common d T M X V W (α+β) p‖*(B0*((1+|t|)*‖mellin Phi (t*I)‖)) := by
    intro p t
    by_cases hs : p ∈ box T M X V
    · have hx : 0 < p.1 := (div_pos hM (by positivity)).trans_le hs.1.1
      have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hs.2.1
      dsimp only [J]
      rw [norm_mul,norm_mul,norm_mul,twist_norm _ _ (by positivity),mul_one]
      exact (mul_le_mul_of_nonneg_left (hb p hs t) (by positivity)).trans_eq (by ring)
    · simp [J,common,hs]
  have hi (t : ℝ) : ‖∫ p, J p t‖ ≤ m*B0*((1+|t|)*‖mellin Phi (t*I)‖) := by
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ p, ‖common d T M X V W (α+β) p‖*(B0*((1+|t|)*‖mellin Phi (t*I)‖)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (hc.norm.mul_const _) (Filter.Eventually.of_forall (fun p => hp p t))
      _ = _ := by rw [integral_mul_const]; dsimp [m]; ring
  change ‖∫ t, ∫ p, J p t‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t : ℝ, m*B0*((1+|t|)*‖mellin Phi (t*I)‖) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (hw.const_mul _) (Filter.Eventually.of_forall hi)
    _ = _ := by rw [integral_const_mul]

#print axioms inverse_power
#print axioms dyadic_log_bound
#print axioms scaled_cutoffs
#print axioms annihilator_bound
#print axioms annihilator_scaled
#print axioms common_integrable
#print axioms common_mass
#print axioms arithmetic_integral_bound
end XiPrime8845.PRZZDyadicEnvelope
