import PRZZSourceDecay

/-! All logarithmic derivatives of the two real constituents of sourceW.
The polynomial recurrence retains every coefficient. This is not yet the
gamma-ratio AFE kernel or the change from log derivatives to x derivatives. -/
noncomputable section
open Polynomial MeasureTheory Filter Topology
namespace XiPrime8845.PRZZGaussianDerivatives

def weighted (P : Polynomial ℝ) (l : ℝ) : ℝ := P.eval l*Real.exp (-l^2/4)
def step (P : Polynomial ℝ) : Polynomial ℝ := P.derivative-C (1/2)*X*P
def iterate (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | n+1 => step (iterate P n)

theorem weighted_hasDerivAt (P : Polynomial ℝ) (l : ℝ) :
    HasDerivAt (weighted P) (weighted (step P) l) l := by
  have hg : HasDerivAt (fun u : ℝ => Real.exp (-u^2/4))
      ((-l/2)*Real.exp (-l^2/4)) l := by
    convert (((hasDerivAt_id l).pow 2).neg.div_const 4).exp using 1 <;>
      simp only [Pi.neg_apply,Pi.pow_apply,id_eq] <;> ring
  convert (P.hasDerivAt l).mul hg using 1 <;>
    first | rfl | (simp only [weighted,step,eval_sub,eval_mul,eval_C,eval_X]; ring)

theorem weighted_iterated (P : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (weighted P) = weighted (iterate P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext l
    exact (weighted_hasDerivAt _ l).deriv

/-- In particular, every positive-order derivative of the actual tail is
a polynomial times the same Gaussian. Even and odd orders are retained. -/
theorem tail_iterated (n : ℕ) :
    iteratedDeriv (n+1) PRZZSourceW.tail = weighted (iterate (-1) n) := by
  rw [iteratedDeriv_succ']
  have he : deriv PRZZSourceW.tail = weighted (-1) := by
    funext l
    rw [(PRZZSourceDecay.tail_hasDerivAt l).deriv]
    simp [weighted]
  rw [he,weighted_iterated]

theorem correction_iterated (n : ℕ) :
    iteratedDeriv n (fun l : ℝ => l*Real.exp (-l^2/4)) =
      weighted (iterate X n) := by
  have he : weighted X = fun l : ℝ => l*Real.exp (-l^2/4) := by
    funext l; simp [weighted]
  rw [← he]
  exact weighted_iterated X n

/-- Absolute integrability is supplied for every polynomial in the
recurrence; it is not an assumption about the differentiated kernel. -/
theorem weighted_integrable (P : Polynomial ℝ) : Integrable (weighted P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : weighted (P+Q) = weighted P + weighted Q := by
      funext l; simp [weighted,add_mul]
    rw [he]; exact hP.add hQ
  | monomial n c =>
    have hi := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)
      (show (-1:ℝ) < (n:ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have he : weighted (monomial n c) =
        fun l : ℝ => c*(l^(n:ℝ)*Real.exp (-(1/4:ℝ)*l^2)) := by
      funext l
      simp only [weighted,Polynomial.eval_monomial,Real.rpow_natCast]
      rw [show -l^2/4 = -(1/4:ℝ)*l^2 by ring]
      ring
    rw [he]
    exact hi.const_mul c

theorem tail_derivatives_integrable (n : ℕ) :
    Integrable (iteratedDeriv (n+1) PRZZSourceW.tail) := by
  rw [tail_iterated]; exact weighted_integrable _

theorem correction_derivatives_integrable (n : ℕ) :
    Integrable (iteratedDeriv n (fun l : ℝ => l*Real.exp (-l^2/4))) := by
  rw [correction_iterated]; exact weighted_integrable _

/-- Removing a real logarithmic cutoff for every differentiated Gaussian
constituent. This is not removal of the AFE arithmetic cutoff. -/
theorem weighted_cutoff_removed (P : Polynomial ℝ) (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ l in (-R)..R, iteratedDeriv n (weighted P) l)
      atTop (nhds (∫ l, iteratedDeriv n (weighted P) l)) := by
  rw [weighted_iterated]
  exact intervalIntegral_tendsto_integral (weighted_integrable _)
    tendsto_neg_atTop_atBot tendsto_id

/-- Exact integral identity for consecutive members of the recurrence. -/
theorem weighted_integral (P : Polynomial ℝ) (a b : ℝ) :
    (∫ l in a..b, weighted (step P) l) = weighted P b-weighted P a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun l _ => weighted_hasDerivAt P l) (weighted_integrable _).intervalIntegrable

#print axioms weighted_cutoff_removed
#print axioms weighted_integral
#print axioms weighted_integrable
#print axioms tail_derivatives_integrable
#print axioms correction_derivatives_integrable
#print axioms weighted_hasDerivAt
#print axioms weighted_iterated
#print axioms tail_iterated
#print axioms correction_iterated
end XiPrime8845.PRZZGaussianDerivatives
