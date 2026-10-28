import CompactShiftIntegral
import PRZZAsymptotic

/-! Regularity of the literal PRZZ integrals. No main-term evaluation is assumed. -/
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory Complex

namespace XiPrime8845.ArithmeticRegularity
open PRZZ CompactShiftIntegral

def negativeShifts : Set Shift := {p | p.1.re < 0 ∧ p.2.re < 0}
def timeStrip : Set ℂ := {z | 0 < z.re ∧ |z.im| < 1/4}

theorem negativeShifts_open : IsOpen negativeShifts := by
  exact (isOpen_lt (show Continuous (fun p : Shift => p.1.re) by fun_prop) continuous_const).inter
    (isOpen_lt (show Continuous (fun p : Shift => p.2.re) by fun_prop) continuous_const)

theorem timeStrip_open : IsOpen timeStrip := by
  exact (isOpen_lt continuous_const (show Continuous Complex.re by fun_prop)).inter
    (isOpen_lt (show Continuous (fun z : ℂ => |z.im|) by fun_prop) continuous_const)

theorem time_segment (T : ℝ) (hT : 0 < T) :
    ∀ t ∈ Icc T (2*T), (t : ℂ) ∈ timeStrip := by
  intro t ht
  exact ⟨hT.trans_le ht.1, by norm_num⟩

theorem zeta_shift_ne_one (T : ℝ) (hT : 1 < T) (A z : ℂ)
    (hA : A.re < 0) (hz : |z.im| < 1/4) :
    1/2 + A/(Real.log T : ℂ) + z*I ≠ 1 ∧
    1/2 + A/(Real.log T : ℂ) - z*I ≠ 1 := by
  have hlog := Real.log_pos hT
  have hdiv : A.re / Real.log T < 0 := div_neg_of_neg_of_pos hA hlog
  have hz' := abs_lt.mp hz
  constructor <;> intro he <;> have hr := congrArg Complex.re he
  all_goals simp only [add_re, sub_re, div_ofReal_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub] at hr
  all_goals norm_num at hr
  all_goals linarith

theorem gcd_zeta_ne_one (T : ℝ) (hT : 1 < T) (p : Shift) (hp : p ∈ negativeShifts) :
    1+p.1/(Real.log T : ℂ)+p.2/(Real.log T : ℂ) ≠ 1 ∧
    1-p.1/(Real.log T : ℂ)-p.2/(Real.log T : ℂ) ≠ 1 := by
  have hlog := Real.log_pos hT
  have ha := div_neg_of_neg_of_pos hp.1 hlog
  have hb := div_neg_of_neg_of_pos hp.2 hlog
  constructor <;> intro he <;> have hr := congrArg Complex.re he
  all_goals simp only [add_re, sub_re, div_ofReal_re, one_re] at hr
  all_goals linarith

def momentCore (T : ℝ) (q : Shift × ℂ) : ℂ :=
  riemannZeta (1/2 + q.1.1/(Real.log T : ℂ) + q.2*I) *
  riemannZeta (1/2 + q.1.2/(Real.log T : ℂ) - q.2*I)

theorem momentCore_smooth (T : ℝ) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (momentCore T) (negativeShifts ×ˢ timeStrip) := by
  intro q hq
  have ha := (zeta_shift_ne_one T hT q.1.1 q.2 hq.1.1 hq.2.2).1
  have hb := (zeta_shift_ne_one T hT q.1.2 q.2 hq.1.2 hq.2.2).2
  apply ContDiffAt.contDiffWithinAt
  exact ((analyticOn_riemannZeta _ ha).contDiffAt.comp q (by fun_prop)).mul
    ((analyticOn_riemannZeta _ hb).contDiffAt.comp q (by fun_prop))

theorem weight_zero_outside (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (T : ℝ) (hT : 0 < T) (t : ℝ) (ht : t ∉ Icc T (2*T)) : Phi (t/T) = 0 := by
  by_contra hn
  have hs := hPhi.2 hn
  apply ht
  exact ⟨by simpa using (le_div_iff₀ hT).mp hs.1, (div_le_iff₀ hT).mp hs.2⟩

/-- Restriction is exact, not a tail estimate or a smoothing approximation. -/
theorem weighted_integral_restrict (f : ℝ → ℂ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ, f t * (Phi (t/T) : ℂ)) =
      ∫ t in Icc T (2*T), f t * (Phi (t/T) : ℂ) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [weight_zero_outside Phi hPhi T hT t ht]

theorem dirichletPolynomial_continuous (a : ℕ → ℂ) (N : ℕ) :
    Continuous (dirichletPolynomial a N) := by
  apply Differentiable.continuous (𝕜 := ℂ)
  unfold dirichletPolynomial
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
  exact (differentiable_const (a n)).div (differentiable_id.const_cpow (Or.inl hn0))
    (fun s => by simp only [cpow_def_of_ne_zero hn0]; exact exp_ne_zero _)

def momentWeight (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (t : ℝ) : ℂ :=
  dirichletPolynomial (coefficient P theta T) (cutoff theta T) (1/2 + t*I) *
  star (dirichletPolynomial (coefficient Q theta T) (cutoff theta T) (1/2 + t*I)) *
  (Phi (t/T) : ℂ)

theorem momentWeight_continuous (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) : Continuous (momentWeight P Q theta T Phi) := by
  unfold momentWeight
  have hP := dirichletPolynomial_continuous (coefficient P theta T) (cutoff theta T)
  have hQ := dirichletPolynomial_continuous (coefficient Q theta T) (cutoff theta T)
  exact ((hP.comp (by fun_prop)).mul (hQ.comp (by fun_prop)).star).mul
    (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop)))

theorem twistedMoment_smooth (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (fun p : Shift => twistedMoment P Q theta T Phi p.1 p.2) negativeShifts := by
  have h := compact_integral_smooth (momentCore T) (momentWeight P Q theta T Phi)
    T (2*T) negativeShifts timeStrip negativeShifts_open timeStrip_open
    (momentCore_smooth T hT) (momentWeight_continuous P Q theta T Phi hPhi).continuousOn
    (time_segment T (by linarith))
  apply h.congr
  intro p hp
  rw [twistedMoment, weighted_integral_restrict _ Phi hPhi T (by linarith)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight, momentCore, smul_eq_mul]
  ring

def gcdCore (T C : ℝ) (q : Shift × ℂ) : ℂ :=
  let alpha := q.1.1/(Real.log T : ℂ)
  let beta := q.1.2/(Real.log T : ℂ)
  riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
    Complex.exp (Complex.log ((C : ℂ)/q.2) * (alpha+beta))

theorem gcdCore_smooth (T C : ℝ) (hT : 1 < T) (hC : 0 < C) :
    ContDiffOn ℂ ∞ (gcdCore T C) (negativeShifts ×ˢ timeStrip) := by
  intro q hq
  have hz0 : q.2 ≠ 0 := by intro h; have := hq.2.1; simp [h] at this
  have hslit : (C : ℂ)/q.2 ∈ slitPlane := by
    apply Or.inl
    simp only [div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos hC hq.2.1) (normSq_pos.mpr hz0)
  have ha := (gcd_zeta_ne_one T hT q.1 hq.1).1
  have hb := (gcd_zeta_ne_one T hT q.1 hq.1).2
  apply ContDiffAt.contDiffWithinAt
  unfold gcdCore
  exact ((analyticOn_riemannZeta _ ha).contDiffAt.comp q (by fun_prop)).add
    (((analyticOn_riemannZeta _ hb).contDiffAt.comp q (by fun_prop)).mul
      (((Complex.contDiffAt_log hslit).comp q (contDiffAt_const.div contDiffAt_snd hz0)).mul
        (by fun_prop)).cexp)

theorem gcd_integral_smooth (T C : ℝ) (hT : 1 < T) (hC : 0 < C)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) :
    ContDiffOn ℂ ∞ (fun p : Shift => ∫ t : ℝ,
      (riemannZeta (1+p.1/(Real.log T : ℂ)+p.2/(Real.log T : ℂ)) +
        riemannZeta (1-p.1/(Real.log T : ℂ)-p.2/(Real.log T : ℂ)) *
          ((C/t : ℝ) : ℂ)^(p.1/(Real.log T : ℂ)+p.2/(Real.log T : ℂ))) *
        (Phi (t/T) : ℂ)) negativeShifts := by
  have hc : Continuous (fun t : ℝ => (Phi (t/T) : ℂ)) :=
    Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop))
  have h := compact_integral_smooth (gcdCore T C) (fun t : ℝ => (Phi (t/T) : ℂ))
    T (2*T) negativeShifts timeStrip negativeShifts_open timeStrip_open
    (gcdCore_smooth T C hT hC) hc.continuousOn (time_segment T (by linarith))
  apply h.congr
  intro p hp
  rw [weighted_integral_restrict _ Phi hPhi T (by linarith)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < T) ht.1
  have hb : ((C/t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (div_pos hC ht0))
  dsimp only
  rw [cpow_def_of_ne_zero hb]
  simp only [gcdCore, smul_eq_mul, Complex.ofReal_div]
  ring

theorem const_cpow_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (hc : c ≠ 0) (f : E → ℂ) (hf : ContDiff ℂ ∞ f) :
    ContDiff ℂ ∞ (fun x => c^(f x)) := by
  simp only [cpow_def_of_ne_zero hc]
  exact (contDiff_const.mul hf).cexp

theorem gcdMainTerm_smooth (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (fun p : Shift => gcdMainTerm P Q theta T Phi p.1 p.2) negativeShifts := by
  unfold gcdMainTerm
  apply ContDiffOn.sum
  intro d hd
  apply ContDiffOn.sum
  intro e he
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hepos : 0 < e := (Finset.mem_Icc.mp he).1
  have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdpos
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hepos)
  have hg0 : (Nat.gcd d e : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hc : 0 < 2*Real.pi*d*e/(Nat.gcd d e : ℝ)^2 := by positivity
  have hi := gcd_integral_smooth T _ hT hc Phi hPhi
  have hi' : ContDiffOn ℂ ∞ (fun p : Shift => ∫ t : ℝ,
      (riemannZeta (1+p.1/(Real.log T : ℂ)+p.2/(Real.log T : ℂ)) +
        riemannZeta (1-p.1/(Real.log T : ℂ)-p.2/(Real.log T : ℂ)) *
          ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^
            (p.1/(Real.log T : ℂ)+p.2/(Real.log T : ℂ))) * (Phi (t/T) : ℂ)) negativeShifts := by
    have hbase (t : ℝ) : (2*Real.pi*d*e/(Nat.gcd d e : ℝ)^2)/t =
        2*Real.pi*d*e/(t*(Nat.gcd d e : ℝ)^2) := by
      rw [div_div, mul_comm ((Nat.gcd d e : ℝ)^2) t]
    simpa only [hbase] using hi
  apply ContDiffOn.mul _ hi'
  apply ContDiffOn.div
  · exact contDiffOn_const.mul ((const_cpow_smooth _ hg0 _ (by fun_prop)).contDiffOn)
  · exact ((const_cpow_smooth _ hd0 _ (by fun_prop)).mul
      (const_cpow_smooth _ he0 _ (by fun_prop))).contDiffOn
  · intro p hp
    apply mul_ne_zero
    · simp only [cpow_def_of_ne_zero hd0]; exact exp_ne_zero _
    · simp only [cpow_def_of_ne_zero he0]; exact exp_ne_zero _

open PRZZAsymptotic

theorem normalizedError_smooth (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (T : ℝ) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (fun p : Shift => normalizedError Phi T p.1 p.2) negativeShifts := by
  exact ((twistedMoment_smooth witness witness PRZZAsymptotic.theta T Phi hPhi hT).div_const (T : ℂ)).sub
    ((gcdMainTerm_smooth witness witness PRZZAsymptotic.theta T Phi hPhi hT).div_const (T : ℂ))

theorem closed_disc_re_neg (z : ℂ)
    (hz : z ∈ Metric.closedBall (-(R : ℂ)) (R/4)) : z.re < 0 := by
  have hn : ‖z+(R : ℂ)‖ ≤ R/4 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz
  have hr := Complex.re_le_norm (z+(R : ℂ))
  simp only [add_re, ofReal_re] at hr
  have hR := radius_pos
  linarith

theorem normalizedError_right_regular (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (T : ℝ) (hT : 1 < T) (x : ℂ)
    (hx : x ∈ Metric.sphere (-(R : ℂ)) (R/4)) :
    DiffContOnCl ℂ (normalizedError Phi T x) (Metric.ball (-(R : ℂ)) (R/4)) := by
  apply DifferentiableOn.diffContOnCl
  intro y hy
  have hx' := closed_disc_re_neg x (Metric.sphere_subset_closedBall hx)
  have hy' := closed_disc_re_neg y (Metric.closure_ball_subset_closedBall hy)
  have hp : (x,y) ∈ negativeShifts := ⟨hx',hy'⟩
  have hs := ((normalizedError_smooth Phi hPhi T hT (x,y) hp).contDiffAt
    (negativeShifts_open.mem_nhds hp)).comp y (contDiffAt_const.prodMk contDiffAt_id)
  exact (hs.differentiableAt (by simp)).differentiableWithinAt

theorem normalizedError_left_mixed_regular (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (T : ℝ) (hT : 1 < T) (b : ℕ) :
    DiffContOnCl ℂ (fun x => iteratedDeriv b (normalizedError Phi T x) (-R))
      (Metric.ball (-(R : ℂ)) (R/4)) := by
  have hs := rightIterated_smooth b (fun p : Shift => normalizedError Phi T p.1 p.2)
    negativeShifts negativeShifts_open (normalizedError_smooth Phi hPhi T hT)
  apply DifferentiableOn.diffContOnCl
  intro x hx
  have hx' := closed_disc_re_neg x (Metric.closure_ball_subset_closedBall hx)
  have hp : (x, -(R : ℂ)) ∈ negativeShifts :=
    ⟨hx', by simpa only [neg_re, ofReal_re] using (neg_neg_of_pos radius_pos)⟩
  have hd := ((hs (x, -(R : ℂ)) hp).contDiffAt (negativeShifts_open.mem_nhds hp)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  exact (hd.differentiableAt (by simp)).differentiableWithinAt

/-- The actual mixed PRZZ residual tends to zero with no regularity premises left.
This still makes no identification of the gcd main term with the finite kernel. -/
theorem normalized_mixed_error_tendsto (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) (a b : ℕ) :
    Tendsto (fun T : ℝ =>
      iteratedDeriv a (fun x => iteratedDeriv b (normalizedError Phi T x) (-R)) (-R))
      atTop (nhds 0) := by
  apply PRZZAsymptotic.normalized_mixed_error_tendsto Phi hPhi a b
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact normalizedError_right_regular Phi hPhi T hT
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact normalizedError_left_mixed_regular Phi hPhi T hT b

#print axioms momentCore_smooth
#print axioms zeta_shift_ne_one
#print axioms gcd_zeta_ne_one
#print axioms closed_disc_re_neg
#print axioms weighted_integral_restrict
#print axioms twistedMoment_smooth
#print axioms gcdCore_smooth
#print axioms gcd_integral_smooth
#print axioms gcdMainTerm_smooth
#print axioms normalizedError_smooth
#print axioms normalizedError_right_regular
#print axioms normalizedError_left_mixed_regular
#print axioms normalized_mixed_error_tendsto
end XiPrime8845.ArithmeticRegularity
