import PRZZFullWeightSmooth

/-! Exact all-order reciprocal-phase jets. The envelope is a finite
polynomial with nonnegative coefficients depending only on the order;
the entire frequency/scale dependence is its argument |omega/x|. -/
noncomputable section
open scoped BigOperators
open Polynomial Filter Topology
namespace XiPrime8845.PRZZReciprocalJets

def phase (omega x : ℝ) : ℂ := Complex.exp (Complex.I*(omega/x:ℝ))
def next (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  -X*P.derivative-(C (n:ℂ)+C Complex.I*X)*P
def polys : ℕ → ℂ[X]
  | 0 => 1
  | n+1 => next n (polys n)
def term (n : ℕ) (P : ℂ[X]) (omega x : ℝ) : ℂ :=
  P.eval ((omega/x:ℝ):ℂ)*phase omega x/(x:ℂ)^n

theorem term_deriv (n : ℕ) (P : ℂ[X]) (omega x : ℝ) (hx : 0 < x) :
    HasDerivAt (term n P omega) (term (n+1) (next n P) omega x) x := by
  have hu := (hasDerivAt_const x omega).div (hasDerivAt_id x) hx.ne'
  have hp := (P.hasDerivAt ((omega/x:ℝ):ℂ)).comp_ofReal.scomp x hu
  have he := (hu.ofReal_comp.const_mul Complex.I).cexp
  have hh := (hp.mul he).div (Complex.ofRealCLM.hasDerivAt.pow n)
    (pow_ne_zero n (by change (x:ℂ) ≠ 0; exact_mod_cast hx.ne'))
  convert hh using 1 <;> first | rfl | skip
  simp only [term,next,phase,eval_sub,eval_mul,eval_neg,eval_X,eval_add,eval_C,
    id_eq,Complex.real_smul,Function.comp_apply,Complex.ofRealCLM_apply,
    Pi.pow_apply,Pi.mul_apply,Pi.div_apply,Complex.ofReal_one]
  push_cast
  cases n <;> simp only [Nat.add_sub_cancel,pow_zero,pow_succ,Nat.cast_zero,
    zero_mul,mul_zero,sub_zero]
  all_goals field_simp <;> ring

theorem iterated (n : ℕ) (omega x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (phase omega) x = term n (polys n) omega x := by
  induction n generalizing x with
  | zero => simp [term,polys]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (phase omega) =ᶠ[𝓝 x] term n (polys n) omega := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (term_deriv n (polys n) omega x hx).deriv

def envelope (n : ℕ) (R : ℝ) : ℝ :=
  ∑ i ∈ (polys n).support, ‖(polys n).coeff i‖*R^i

theorem phase_norm (omega x : ℝ) : ‖phase omega x‖ = 1 := by
  simp [phase,Complex.norm_exp]

theorem bound (n : ℕ) (omega x R : ℝ) (hx : 0 < x) (hR : |omega/x| ≤ R) :
    ‖iteratedDeriv n (phase omega) x‖ ≤ envelope n R/x^n := by
  rw [iterated n omega x hx,term,norm_div,norm_mul,phase_norm,mul_one,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Polynomial.eval_eq_sum]
  apply (norm_sum_le _ _).trans
  unfold envelope
  apply Finset.sum_le_sum
  intro i hi
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  gcongr

theorem envelope_nonneg (n : ℕ) (R : ℝ) (hR : 0 ≤ R) : 0 ≤ envelope n R := by
  unfold envelope
  exact Finset.sum_nonneg (by intro i hi; positivity)

/-- Ready for the scaled Leibniz rule; no constant depends on omega or x. -/
theorem scaled_bound (n : ℕ) (omega x R : ℝ) (hx : 0 < x) (hR : |omega/x| ≤ R) :
    ‖(x:ℂ)^n*iteratedDeriv n (phase omega) x‖ ≤ envelope n R := by
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left (bound n omega x R hx hR) (pow_nonneg hx.le n)
  exact hh.trans_eq (by field_simp)

#print axioms scaled_bound
#print axioms envelope_nonneg
#print axioms term_deriv
#print axioms iterated
#print axioms phase_norm
#print axioms bound
end XiPrime8845.PRZZReciprocalJets
