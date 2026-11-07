import PRZZDualFirstJet

/-! Quantitative series for every positive digamma derivative. Uniform
summability is proved on a fixed right half-plane before differentiating
the series; no derivative of a pointwise asymptotic is taken. -/
noncomputable section
open scoped BigOperators
open Complex Filter Topology Set MeasureTheory
namespace XiPrime8845.PRZZPolygammaSeries
set_option maxHeartbeats 7000000

def term (p n : ℕ) (z : ℂ) : ℂ := 1/(z+(n:ℂ))^(p+2)
def series (p : ℕ) (z : ℂ) : ℂ := ∑' n : ℕ, term p n z
def majorant (p n : ℕ) : ℝ := (16:ℝ)^(p+1)*(((1/4:ℝ)+n)^2)⁻¹

theorem term_bound (p n : ℕ) (z : ℂ) (hz : 1/16 < z.re) :
    ‖term p n z‖ ≤ majorant p n := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hlow : ((1/4:ℝ)+n)/4 ≤ ‖z+(n:ℂ)‖ := by
    have hh := Complex.re_le_norm (z+(n:ℂ))
    simp only [add_re,natCast_re] at hh
    linarith
  have hmin : 1/16 ≤ ‖z+(n:ℂ)‖ := by linarith
  have hpos : 0 < ‖z+(n:ℂ)‖ := by linarith
  have hbase : ‖z+(n:ℂ)‖⁻¹ ≤ 16 := by
    rw [← one_div,div_le_iff₀ hpos]; linarith
  have hsquare : (‖z+(n:ℂ)‖^2)⁻¹ ≤ 16*(((1/4:ℝ)+n)^2)⁻¹ := by
    have hq : 0 < ((1/4:ℝ)+n)^2 := by positivity
    have hh : 1/(‖z+(n:ℂ)‖^2) ≤ 16/((1/4:ℝ)+n)^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hq).mpr
      nlinarith [sq_nonneg (‖z+(n:ℂ)‖-((1/4:ℝ)+n)/4)]
    simpa only [div_eq_mul_inv,one_mul] using hh
  calc
    _ = (‖z+(n:ℂ)‖⁻¹)^p*(‖z+(n:ℂ)‖^2)⁻¹ := by
      simp [term,norm_div,norm_pow,pow_add,inv_pow,mul_comm]
    _ ≤ 16^p*(16*(((1/4:ℝ)+n)^2)⁻¹) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hbase p) hsquare (by positivity) (by positivity)
    _ = _ := by simp only [majorant,pow_succ]; ring

theorem majorant_summable (p : ℕ) : Summable (majorant p) := by
  change Summable (fun n : ℕ => (16:ℝ)^(p+1)*(((1/4:ℝ)+n)^2)⁻¹)
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] using
    (Zeta23.MuFields.summable_quarter_line 0).mul_left ((16:ℝ)^(p+1))

theorem term_derivative (p n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (term p n) (-((p+2:ℕ):ℂ)*term (p+1) n z) z := by
  have hn : z+(n:ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [add_re,natCast_re,zero_re] at he
    have hh : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hd := (hasDerivAt_const z (1:ℂ)).div
    (((hasDerivAt_id z).add_const (n:ℂ)).pow (p+2)) (pow_ne_zero _ hn)
  simp only [Pi.div_apply,Pi.pow_apply,id_eq,zero_mul,one_mul,zero_sub,
    show p+2-1 = p+1 by omega] at hd
  convert hd using 1 <;> first | rfl | (simp only [term]; field_simp [hn,pow_succ] <;> ring)

theorem series_differentiable (p : ℕ) :
    DifferentiableOn ℂ (series p) {z : ℂ | 1/16 < z.re} := by
  apply differentiableOn_tsum_of_summable_norm (majorant_summable p)
    (fun n z hz => (term_derivative p n z (by change 1/16 < z.re at hz; linarith)).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const continuous_re)
  exact fun n z hz => term_bound p n z hz

theorem series_derivative (p : ℕ) (z : ℂ) (hz : 1/16 < z.re) :
    HasDerivAt (series p) (-((p+2:ℕ):ℂ)*series (p+1) z) z := by
  have hopen : IsOpen {z : ℂ | 1/16 < z.re} := isOpen_lt continuous_const continuous_re
  have hh := hasSum_deriv_of_summable_norm (majorant_summable p)
    (fun n w hw => (term_derivative p n w (by change 1/16 < w.re at hw; linarith)).differentiableAt.differentiableWithinAt)
    hopen (fun n w hw => term_bound p n w hw) hz
  have hs : Summable (fun n => term (p+1) n z) :=
    Summable.of_norm_bounded (majorant_summable (p+1)) (fun n => term_bound (p+1) n z hz)
  have he : deriv (series p) z = -((p+2:ℕ):ℂ)*series (p+1) z := by
    have hterms : (fun n => deriv (term p n) z) =
        (fun n => -((p+2:ℕ):ℂ)*term (p+1) n z) :=
      funext (fun n => (term_derivative p n z (by linarith)).deriv)
    rw [hterms] at hh
    exact hh.unique (hs.hasSum.mul_left _)
  rw [← he]
  exact ((series_differentiable p) z hz).differentiableAt (hopen.mem_nhds hz) |>.hasDerivAt

def jet (p : ℕ) (z : ℂ) : ℂ := (-1:ℂ)^p*((p+1).factorial:ℂ)*series p z

theorem jet_derivative (p : ℕ) (z : ℂ) (hz : 1/16 < z.re) :
    HasDerivAt (jet p) (jet (p+1) z) z := by
  convert (series_derivative p z hz).const_mul ((-1:ℂ)^p*((p+1).factorial:ℂ)) using 1 <;>
    first | rfl | (simp only [jet,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; ring)

theorem digamma_iterated (p : ℕ) (z : ℂ) (hz : 1/16 < z.re) (hi : z.im ≠ 0) :
    iteratedDeriv (p+1) digamma z = jet p z := by
  induction p generalizing z with
  | zero =>
    have hzero : z ∈ integerComplement := by
      intro h
      obtain ⟨n,hn⟩ := h
      exact hi (by simpa using (congrArg Complex.im hn).symm)
    simpa [jet,series,term] using (Zeta23.Stirling.hasSum_trigamma hzero).tsum_eq.symm
  | succ p ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (p+1) digamma =ᶠ[𝓝 z] jet p := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz,
        continuous_im.continuousAt.tendsto.eventually (eventually_ne_nhds hi)] with w hw hwi
      exact ih w hw hwi
    rw [he.deriv_eq]
    exact (jet_derivative p z hz).deriv

theorem vertical_term (p n : ℕ) (z : ℂ) (hz : 1/8 ≤ z.re) (hi : 0 < |z.im|) :
    ‖term p n z‖ ≤ (|z.im|⁻¹)^p*
      (4*((((1/4:ℝ)+n)^2+(2*z.im)^2)⁻¹)) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hnorm : |z.im| ≤ ‖z+(n:ℂ)‖ := by simpa using abs_im_le_norm (z+(n:ℂ))
  have hpos : 0 < ‖z+(n:ℂ)‖ := hi.trans_le hnorm
  have hquad : ‖z+(n:ℂ)‖^2 = (z.re+n)^2+z.im^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hcompare : ((1/4:ℝ)+n)^2+(2*z.im)^2 ≤ 4*‖z+(n:ℂ)‖^2 := by
    rw [hquad]
    nlinarith [sq_nonneg (2*(z.re+n)-(1/4+n))]
  have hq : 0 < ((1/4:ℝ)+n)^2+(2*z.im)^2 := by positivity
  have hsquare : (‖z+(n:ℂ)‖^2)⁻¹ ≤ 4*((((1/4:ℝ)+n)^2+(2*z.im)^2)⁻¹) := by
    have hh : 1/(‖z+(n:ℂ)‖^2) ≤ 4/(((1/4:ℝ)+n)^2+(2*z.im)^2) :=
      (div_le_div_iff₀ (sq_pos_of_pos hpos) hq).mpr (by nlinarith)
    simpa only [div_eq_mul_inv,one_mul] using hh
  calc
    _ = (‖z+(n:ℂ)‖⁻¹)^p*(‖z+(n:ℂ)‖^2)⁻¹ := by
      simp [term,norm_div,norm_pow,pow_add,inv_pow,mul_comm]
    _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) (inv_le_inv₀ hpos hi |>.mpr hnorm) p)
      hsquare (by positivity) (by positivity)

/-- All orders gain their own inverse-height power. The summable
quadratic core is bounded once, rather than replaced by a term count. -/
theorem series_height (p : ℕ) (T : ℝ) (z : ℂ) (hT : 1 ≤ T)
    (hz : 1/8 ≤ z.re) (hi : T/4 ≤ |z.im|) :
    ‖series p z‖ ≤ (4/T)^p*(96/T) := by
  have hT0 : 0 < T := by linarith
  have hi0 : 0 < |z.im| := by linarith
  have hs : Summable (fun n => ‖term p n z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => term_bound p n z (by linarith))
      (majorant_summable p)
  have hbase := Zeta23.MuFields.trigamma_tail_le (t := 2*z.im) (by rw [abs_mul]; norm_num; linarith)
  have hsum := (Zeta23.MuFields.summable_quarter_line (2*z.im)).mul_left (|z.im|⁻¹^p*4)
  have hpoint := fun n => vertical_term p n z hz hi0
  calc
    _ ≤ ∑' n, ‖term p n z‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, (|z.im|⁻¹^p*4)*((((1/4:ℝ)+n)^2+(2*z.im)^2)⁻¹) := by
      exact Summable.tsum_le_tsum (fun n => (hpoint n).trans_eq (by ring)) hs hsum
    _ = (|z.im|⁻¹^p*4)*∑' n : ℕ, ((((1/4:ℝ)+n)^2+(2*z.im)^2)⁻¹) := tsum_mul_left
    _ ≤ (|z.im|⁻¹^p*4)*(12/|2*z.im|) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = |z.im|⁻¹^p*(24/|z.im|) := by rw [abs_mul]; norm_num; ring
    _ ≤ (4/T)^p*(96/T) := by
      have hh : |z.im|⁻¹ ≤ 4/T := by
        rw [← one_div]
        exact (div_le_div_iff₀ hi0 hT0).mpr (by nlinarith)
      have hh' : 24/|z.im| ≤ 96/T := (div_le_div_iff₀ hi0 hT0).mpr (by nlinarith)
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hh p) hh' (by positivity) (by positivity)

theorem digamma_height (p : ℕ) (T : ℝ) (z : ℂ) (hT : 1 ≤ T)
    (hz : 1/8 ≤ z.re) (hi : T/4 ≤ |z.im|) :
    ‖iteratedDeriv (p+1) digamma z‖ ≤ ((p+1).factorial:ℝ)*(4/T)^p*(96/T) := by
  rw [digamma_iterated p z (by linarith) (by intro hh; simp only [hh,abs_zero] at hi; linarith)]
  simp only [jet,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (series_height p T z hT hz hi) (Nat.cast_nonneg _)).trans_eq (by ring)

/-- Shift differences gain one more inverse-height power. This is the
cancellation required by higher derivatives of a Gamma quotient; bounding
the two polygamma values separately would lose that power. -/
theorem shifted_difference (p : ℕ) (T : ℝ) (z d : ℂ) (hT : 1 ≤ T)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 1/8 ≤ (z+(u:ℂ)*d).re)
    (hi : ∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |(z+(u:ℂ)*d).im|) :
    ‖iteratedDeriv (p+1) digamma (z+d)-iteratedDeriv (p+1) digamma z‖ ≤
      ‖d‖*(((p+2).factorial:ℝ)*(4/T)^(p+1)*(96/T)) := by
  have hT0 : 0 < T := by linarith
  have hpath : Continuous (fun u : ℝ => z+(u:ℂ)*d) := by fun_prop
  have hd (q : ℕ) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun v : ℝ => jet q (z+(v:ℂ)*d))
        (d*jet (q+1) (z+(u:ℂ)*d)) u := by
    have hh := (jet_derivative q (z+(u:ℂ)*d) (by linarith [hr u hu])).scomp u
      ((((hasDerivAt_id u).ofReal_comp).mul_const d).const_add z)
    simpa only [Function.comp_def,id_eq,Complex.ofReal_one,mul_one,one_mul,smul_eq_mul] using hh
  have hc : ContinuousOn (fun u : ℝ => jet p (z+(u:ℂ)*d)) (Icc 0 1) :=
    fun u hu => (hd p u hu).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (fun u : ℝ => d*jet (p+1) (z+(u:ℂ)*d)) (Icc 0 1) :=
    fun u hu => (continuousAt_const.mul (hd (p+1) u hu).continuousAt).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hc (fun u hu => hd p u ⟨hu.1.le,hu.2.le⟩) (hc'.intervalIntegrable_of_Icc (by norm_num))
  simp only [ofReal_one,ofReal_zero,one_mul,zero_mul,add_zero] at he
  have hn (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : (z+(u:ℂ)*d).im ≠ 0 := by
    intro hh; have hh' := hi u hu; simp only [hh,abs_zero] at hh'; linarith
  have h1 : 1/8 ≤ (z+d).re := by simpa using hr 1 (by norm_num)
  have h0 : 1/8 ≤ z.re := by simpa using hr 0 (by norm_num)
  rw [digamma_iterated p (z+d) (by linarith)
    (by simpa using hn 1 (by norm_num)),digamma_iterated p z
      (by linarith)
      (by simpa using hn 0 (by norm_num)),← he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun u : ℝ => d*jet (p+1) (z+(u:ℂ)*d))
    (C := ‖d‖*(((p+2).factorial:ℝ)*(4/T)^(p+1)*(96/T))) (fun u hu => by
      have hu' : u ∈ Icc (0:ℝ) 1 := by
        simp only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),Set.mem_Ioc] at hu
        exact ⟨hu.1.le,hu.2⟩
      rw [norm_mul]
      have hh := digamma_height (p+1) T (z+(u:ℂ)*d) hT (hr u hu') (hi u hu')
      rw [digamma_iterated (p+1) _ (by linarith [hr u hu']) (hn u hu')] at hh
      exact mul_le_mul_of_nonneg_left hh (norm_nonneg d))
  simpa only [sub_zero,abs_one,mul_one] using hb

#print axioms shifted_difference
#print axioms vertical_term
#print axioms series_height
#print axioms digamma_height
#print axioms term_bound
#print axioms majorant_summable
#print axioms term_derivative
#print axioms series_differentiable
#print axioms series_derivative
#print axioms jet_derivative
#print axioms digamma_iterated
end XiPrime8845.PRZZPolygammaSeries
