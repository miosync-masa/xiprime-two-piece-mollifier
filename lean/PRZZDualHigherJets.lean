import PRZZPolygammaSeries

/-! Actual logarithmic jets of the dual Gamma multiplier. Positive
polygamma orders use the differentiated, uniformly summable series;
shift differences are estimated before taking the Gamma product. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set Filter Topology MeasureTheory Finset
namespace XiPrime8845.PRZZDualHigherJets
open PRZZPolygammaSeries PRZZDualFirstJet
set_option maxHeartbeats 9000000

def point (a : ℂ) (e t : ℝ) : ℂ := (1/2+a)/2+(t:ℂ)*((e:ℂ)*I/2)
def difference (n : ℕ) (a d : ℂ) (e t : ℝ) : ℂ :=
  iteratedDeriv n digamma (point a e t+d)-iteratedDeriv n digamma (point a e t)
def costJet (n : ℕ) (a b : ℂ) (t : ℝ) : ℂ :=
  (I/2)^(n+1)*difference n a (-(a+b)/2) 1 t+
    (-I/2)^(n+1)*difference n b (-(a+b)/2) (-1) t

theorem shift_norm (a b : ℂ) (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) :
    ‖-(a+b)/2‖ ≤ 1/16 := by
  rw [norm_div,norm_neg]
  norm_num only [Complex.norm_ofNat]
  have hh := norm_add_le a b
  linarith

theorem geometry (T t e : ℝ) (a d : ℂ) (hT : 2 ≤ T) (ht : T ≤ t)
    (he : |e| = 1) (ha : ‖a‖ ≤ 1/16) (hd : ‖d‖ ≤ 1/16) :
    (∀ u ∈ Set.Icc (0:ℝ) 1, 1/8 ≤ (point a e t+(u:ℂ)*d).re) ∧
    (∀ u ∈ Set.Icc (0:ℝ) 1, T/4 ≤ |(point a e t+(u:ℂ)*d).im|) := by
  refine ⟨?_,(line_conditions T t e a d hT ht he ha hd).2⟩
  intro u hu
  have huN : ‖(u:ℂ)‖ ≤ 1 := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1,hu.2]
  have hnorm : ‖(u:ℂ)*d‖ ≤ 1/16 := by rw [norm_mul]; nlinarith [norm_nonneg d]
  have hr := (abs_le.mp ((abs_re_le_norm ((u:ℂ)*d)).trans hnorm)).1
  have har := (abs_le.mp ((abs_re_le_norm a).trans ha)).1
  have heq : (point a e t+(u:ℂ)*d).re = (1/2+a.re)/2+((u:ℂ)*d).re := by simp [point]
  rw [heq]; linarith

theorem psi_analytic (n : ℕ) (z : ℂ) (hz : 1/16 < z.re) :
    AnalyticAt ℂ (iteratedDeriv n digamma) z := by
  have ha : AnalyticOnNhd ℂ digamma {w : ℂ | 1/16 < w.re} := by
    intro w hw
    have hg := PRZZGammaPath.gamma_analytic w (by change 1/16 < w.re at hw; linarith)
    have hh := hg.deriv.div hg (Gamma_ne_zero_of_re_pos (by change 1/16 < w.re at hw; linarith))
    exact hh.congr (by filter_upwards with v; simp only [Pi.div_apply,Complex.digamma_def,logDeriv_apply])
  rw [iteratedDeriv_eq_iterate]
  exact ha.iterated_deriv n z hz

theorem psi_derivative (n : ℕ) (z : ℂ) (hz : 1/16 < z.re) :
    HasDerivAt (iteratedDeriv n digamma) (iteratedDeriv (n+1) digamma z) z := by
  rw [iteratedDeriv_succ]
  exact (psi_analytic n z hz).differentiableAt.hasDerivAt

theorem difference_derivative (n : ℕ) (a d : ℂ) (e t : ℝ)
    (hz : 1/16 < (point a e t).re) (hd : 1/16 < (point a e t+d).re) :
    HasDerivAt (difference n a d e) (((e:ℂ)*I/2)*difference (n+1) a d e t) t := by
  have hpath : HasDerivAt (point a e) ((e:ℂ)*I/2) t := by
    change HasDerivAt (fun u : ℝ => (1/2+a)/2+(u:ℂ)*((e:ℂ)*I/2)) _ t
    simpa only [id_eq,Complex.ofReal_one,one_mul] using
      ((((hasDerivAt_id t).ofReal_comp).mul_const ((e:ℂ)*I/2)).const_add ((1/2+a)/2))
  have h0 := (psi_derivative n (point a e t) hz).scomp t hpath
  have h1 := (psi_derivative n (point a e t+d) hd).scomp t (hpath.add_const d)
  convert h1.sub h0 using 1 <;>
    first | rfl | (simp only [Function.comp_def,smul_eq_mul,difference]; ring)

theorem cost_derivative (n : ℕ) (a b : ℂ) (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16)
    (t : ℝ) (ht : 2 ≤ t) : HasDerivAt (costJet n a b) (costJet (n+1) a b t) t := by
  have hL := geometry 2 t 1 a (-(a+b)/2) (by norm_num) ht (by norm_num) ha (shift_norm a b ha hb)
  have hR := geometry 2 t (-1) b (-(a+b)/2) (by norm_num) ht (by norm_num) hb (shift_norm a b ha hb)
  have hdL := difference_derivative n a (-(a+b)/2) 1 t
    (by have h := hL.1 0 (by norm_num); simp only [ofReal_zero,zero_mul,add_zero] at h; linarith)
    (by have h := hL.1 1 (by norm_num); simp only [ofReal_one,one_mul] at h; linarith)
  have hdR := difference_derivative n b (-(a+b)/2) (-1) t
    (by have h := hR.1 0 (by norm_num); simp only [ofReal_zero,zero_mul,add_zero] at h; linarith)
    (by have h := hR.1 1 (by norm_num); simp only [ofReal_one,one_mul] at h; linarith)
  convert (hdL.const_mul ((I/2)^(n+1))).add (hdR.const_mul ((-I/2)^(n+1))) using 1 <;>
    first | rfl | (simp only [costJet,pow_succ,Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul]; ring)

theorem cost_iterated (n : ℕ) (a b : ℂ) (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16)
    (t : ℝ) (ht : 2 < t) : iteratedDeriv n (costJet 0 a b) t = costJet n a b t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (costJet 0 a b) =ᶠ[𝓝 t] costJet n a b := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      exact ih u hu
    rw [he.deriv_eq]
    exact (cost_derivative n a b ha hb t ht.le).deriv

def logConstant : ℕ → ℝ
  | 0 => 102
  | n+1 => 192*((n+2).factorial:ℝ)*4^(n+1)

theorem logConstant_nonneg (n : ℕ) : 0 ≤ logConstant n := by cases n <;> simp [logConstant] <;> positivity

theorem cost_bound (n : ℕ) (T t : ℝ) (a b : ℂ) (hT : 2 ≤ T) (ht : T ≤ t)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) :
    ‖costJet n a b t‖ ≤ logConstant n/T^(n+1) := by
  let d := -(a+b)/2
  have hd := shift_norm a b ha hb
  have hT0 : 0 < T := by linarith
  have hp (e : ℝ) (he : |e| = 1) (c : ℂ) (hc : ‖c‖ ≤ 1/16) :
      ‖((e:ℂ)*I/2)^(n+1)*difference n c d e t‖ ≤ logConstant n/(2*T^(n+1)) := by
    have hg := geometry T t e c d hT ht he hc hd
    have hk : ‖(e:ℂ)*I/2‖ = 1/2 := by simp [he]
    cases n with
    | zero =>
      have hh := digamma_difference T (point c e t) d hT
        (fun u hu => lt_of_lt_of_le (by norm_num) (hg.1 u hu)) hg.2
      simp only [norm_mul,norm_pow,hk,pow_one,difference,iteratedDeriv_zero,logConstant]
      have hcost : (1/2:ℝ)*((100+4*‖d‖)/T) ≤ 102/(2*T) := by
        apply (le_div_iff₀ (by positivity : 0 < 2*T)).mpr
        field_simp
        nlinarith
      simpa only [Nat.zero_add,pow_one] using (mul_le_mul_of_nonneg_left hh (by norm_num)).trans hcost
    | succ n =>
      have hh := shifted_difference n T (point c e t) d (by linarith) hg.1 hg.2
      have hk' : (1/2:ℝ)^(n+1+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      simp only [norm_mul,norm_pow,hk,difference]
      apply (mul_le_mul hk' hh (norm_nonneg _) (by norm_num)).trans
      simp only [one_mul,logConstant]
      have hd1 : ‖d‖ ≤ 1 := by linarith
      calc
        _ ≤ ((n+2).factorial:ℝ)*(4/T)^(n+1)*(96/T) := mul_le_of_le_one_left (by positivity) hd1
        _ = _ := by rw [div_pow]; field_simp [pow_succ]; ring
  have hL := hp 1 (by norm_num) a ha
  have hR := hp (-1) (by norm_num) b hb
  apply (norm_add_le _ _).trans
  convert add_le_add hL hR using 1 <;>
    first | simp only [costJet,Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul,d] | (field_simp <;> ring)

#print axioms shift_norm
#print axioms geometry
#print axioms psi_analytic
#print axioms psi_derivative
#print axioms difference_derivative
#print axioms cost_derivative
#print axioms cost_iterated
#print axioms logConstant_nonneg
#print axioms cost_bound
end XiPrime8845.PRZZDualHigherJets
