import WitnessMomentBound
import Zeta23.XiPrime.Seam

/-! Exact entry to the Wu counting argument for the certified witness.
The auxiliary function uses genuine derivatives of xi, not zeta in their place.
The translated mollifier agrees with the original moment on the left line.
Zero detection below is set-theoretic, NOT a multiplicity or argument-count
inequality. Stirling transfer, removal of smoothing, right-boundary estimates
and the Littlewood/phase-counting argument remain separate obligations. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory
namespace XiPrime8845.WuAuxiliary
open Zeta23.XiPrime ZetaMomentPolynomial WitnessMomentBound
set_option maxHeartbeats 1000000

def rCoeff : ℕ → ℝ
  | 0 => 0.09491351
  | 1 => 0.997010185
  | 2 => 2.089866
  | 4 => -2.29671034
  | 6 => 1.7701948
  | _ => 0

/-- Exact rational arithmetic: r(u)=q(1/2-u), including zero cubic/quintic terms. -/
theorem translated_polynomial (u : ℂ) :
    (∑ n ∈ Finset.range 7, (rCoeff n : ℂ)*u^n) =
      ∑ n ∈ Finset.range 7, NumericalGate.qCoeff n*(1/2-u)^n := by
  norm_num [Finset.sum_range_succ, rCoeff, NumericalGate.qCoeff]
  ring

theorem operator_polynomial (z : ℂ) :
    (∑ n ∈ Finset.range 7, (rCoeff n : ℂ)*(1/2+z)^n) =
      ∑ n ∈ Finset.range 7, NumericalGate.qCoeff n*(-z)^n := by
  rw [translated_polynomial]
  congr 1
  funext n
  congr 2
  ring

theorem r_at_half : (∑ n ∈ Finset.range 7, (rCoeff n : ℂ)*(1/2)^n) = 1 := by
  norm_num [Finset.sum_range_succ, rCoeff]

theorem linear_coefficient_pos : 0 < rCoeff 1 := by norm_num [rCoeff]

theorem xi_derivative_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n xi (conj s) = conj (iteratedDeriv n xi s) := by
  induction n generalizing s with
  | zero => exact xi_conj s
  | succ n ih =>
    have he : conj ∘ iteratedDeriv n xi ∘ conj = iteratedDeriv n xi := by
      funext z
      simp only [Function.comp_def, ih, Complex.conj_conj]
    have hh := congrFun (deriv_conj_conj (f := iteratedDeriv n xi)) (conj s)
    rw [he] at hh
    simpa only [iteratedDeriv_succ, Function.comp_def, Complex.conj_conj] using hh

theorem xi_derivative_one_sub (n : ℕ) (s : ℂ) :
    iteratedDeriv n xi (1-s) = (-1:ℂ)^n*iteratedDeriv n xi s := by
  have he : (fun z : ℂ => xi (1-z)) = xi := funext xi_one_sub
  have hh := congrFun (iteratedDeriv_comp_const_sub (n:=n) (f:=xi) (s:=(1:ℂ))) (1-s)
  simpa only [he, sub_sub_cancel, smul_eq_mul] using hh

def critical (t : ℝ) : ℂ := 1/2+(t:ℂ)*Complex.I

theorem xi_derivative_critical (n : ℕ) (t : ℝ) :
    conj (iteratedDeriv n xi (critical t)) = (-1:ℂ)^n*iteratedDeriv n xi (critical t) := by
  rw [← xi_derivative_conj]
  have he : conj (critical t) = 1-critical t := by
    apply Complex.ext <;> norm_num [critical]
  rw [he, xi_derivative_one_sub]

theorem xi_even_im (m : ℕ) (t : ℝ) :
    (iteratedDeriv (2*m) xi (critical t)).im = 0 := by
  have h := congrArg Complex.im (xi_derivative_critical (2*m) t)
  simp only [pow_mul, neg_one_sq, one_pow, one_mul, Complex.conj_im] at h
  linarith

theorem xi_odd_re (m : ℕ) (t : ℝ) :
    (iteratedDeriv (2*m+1) xi (critical t)).re = 0 := by
  have h := congrArg Complex.re (xi_derivative_critical (2*m+1) t)
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
    neg_one_mul, Complex.neg_re, Complex.conj_re] at h
  linarith

/-- L is held fixed in the analytic variable s. -/
def eta (L : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 7, (rCoeff n : ℂ)/(L:ℂ)^n*iteratedDeriv n xi s

theorem eta_entire (L : ℝ) : Differentiable ℂ (eta L) := by
  have hx : ContDiff ℂ ⊤ xi := xi_differentiable.contDiff
  unfold eta
  apply Differentiable.fun_sum
  intro n hn
  exact (differentiable_const _).mul (hx.differentiable_iteratedDeriv n (by simp))

theorem eta_im (L t : ℝ) :
    (eta L (critical t)).im = (rCoeff 1/L)*(xiDeriv (critical t)).im := by
  have h0 := xi_even_im 0 t
  have h2 := xi_even_im 1 t
  have h4 := xi_even_im 2 t
  have h6 := xi_even_im 3 t
  norm_num only at h0 h2 h4 h6
  simp only [eta, Finset.sum_range_succ, Finset.sum_range_zero, rCoeff]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, zero_add, zero_div, div_one, pow_zero, pow_one,
    h0, h2, h4, h6, mul_zero, iteratedDeriv_one, xiDeriv]

/-- Exact detection of xi' zeros; no multiplicity statement is inferred. -/
theorem eta_im_zero_iff (L t : ℝ) (hL : L ≠ 0) :
    (eta L (critical t)).im = 0 ↔ xiDeriv (critical t) = 0 := by
  have hr : rCoeff 1/L ≠ 0 := div_ne_zero linear_coefficient_pos.ne' hL
  have hre : (xiDeriv (critical t)).re = 0 := by
    simpa only [Nat.mul_zero, Nat.zero_add, iteratedDeriv_one, xiDeriv] using xi_odd_re 0 t
  rw [eta_im, mul_eq_zero, or_iff_right hr]
  constructor
  · intro hi
    exact Complex.ext (by simpa using hre) (by simpa using hi)
  · intro h; simp [h]

/-- The analytic mollifier has its R/log T translation built into the exponent. -/
def psi (T : ℝ) (s : ℂ) : ℂ :=
  PRZZ.dirichletPolynomial (PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T)
    (PRZZ.cutoff PRZZAsymptotic.theta T) (s+(PRZZAsymptotic.R/Real.log T:ℝ))

def leftPoint (T t : ℝ) : ℂ := (1/2-PRZZAsymptotic.R/Real.log T:ℝ)+(t:ℂ)*Complex.I

theorem psi_entire (T : ℝ) : Differentiable ℂ (psi T) := by
  unfold psi PRZZ.dirichletPolynomial
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n:ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
  exact (differentiable_const _).div
    ((differentiable_id.add_const _).const_cpow (Or.inl hn0))
    (fun s => by simp only [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _)

theorem psi_left (T t : ℝ) :
    psi T (leftPoint T t) =
      PRZZ.dirichletPolynomial (PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T)
        (PRZZ.cutoff PRZZAsymptotic.theta T) (critical t) := by
  unfold psi leftPoint critical
  congr 1
  push_cast
  ring

def U (T : ℝ) (s : ℂ) : ℂ :=
  differentialPolynomial 6 (fun n => (qReal n:ℂ)) T s

def smoothedMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t : ℝ, ‖U T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T))/T

/-- Finite-T identity, with no shift, cutoff or smoothing approximation. -/
theorem smoothedMoment_eq (Phi : ℝ → ℝ) (T : ℝ) :
    smoothedMoment Phi T = witnessMoment Phi T := by
  unfold smoothedMoment
  simp_rw [psi_left]
  rfl

theorem smoothedMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    Tendsto (smoothedMoment Phi) atTop (nhds (NumericalGate.actual.re*mass Phi)) := by
  change Tendsto (fun T => smoothedMoment Phi T) atTop _
  simpa only [smoothedMoment_eq] using witnessMoment_tendsto Phi hPhi

/-- This is still a fixed smooth-weight moment bound, not a zero-count bound. -/
theorem smoothedMoment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : 0 < mass Phi) :
    (0.8845:ℝ) < 1-Real.log countingCap/NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ smoothedMoment Phi T/mass Phi ∧ smoothedMoment Phi T/mass Phi < countingCap := by
  simpa only [smoothedMoment_eq, normalizedMoment] using witness_moment_bound Phi hPhi hPhi0 hm

/-- The separate derivative moments needed by a later uniform Stirling transfer. -/
def derivativeMoment (k : ℕ) (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t : ℝ, ‖ZetaMomentIntegral.scaledZeta k T (leftPoint T t)*
    psi T (leftPoint T t)‖^2*Phi (t/T))/T

theorem single_operator (k : ℕ) (T : ℝ) (s : ℂ) :
    differentialPolynomial k (fun n => ((if n=k then 1 else 0 : ℝ):ℂ)) T s =
      (-1:ℂ)^k*ZetaMomentIntegral.scaledZeta k T s := by
  simp [differentialPolynomial, apply_ite, ite_mul]

theorem derivativeMoment_eq (k : ℕ) (Phi : ℝ → ℝ) (T : ℝ) :
    derivativeMoment k Phi T = squareMoment k (fun n => if n=k then 1 else 0)
      PRZZ.witness PRZZAsymptotic.theta T Phi (1/2-PRZZAsymptotic.R/Real.log T) := by
  unfold derivativeMoment
  simp_rw [psi_left]
  simp only [squareMoment, single_operator,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, leftPoint, critical]

/-- One eventual bound works for all seven orders. Phi is fixed, not uniform.
This supplies bounded derivative moments, not a bound for eta/H-U. -/
theorem derivativeMoments_bounded (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ k ≤ 6, |derivativeMoment k Phi T| ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, |derivativeMoment k Phi T| ≤ C := by
    have h := ZetaMomentMainTerm.squareMoment_exactEvaluator_tendsto k
      (fun n => if n=k then 1 else 0) Phi hPhi
    simp only [← derivativeMoment_eq] at h
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Tendsto (fun T => derivativeMoment k Phi T) atTop (nhds c) := ⟨_, h⟩
    refine ⟨|c|+1, by positivity, ?_⟩
    exact (hc.abs.eventually (gt_mem_nhds (lt_add_one _))).mono (fun T hT => hT.le)
  choose c hc hbound using hb
  refine ⟨∑ k ∈ Finset.range 7, c k, ?_, ?_⟩
  · exact Finset.sum_pos (fun k _ => hc k) (by simp)
  have hall : ∀ᶠ T : ℝ in atTop, ∀ k ∈ Finset.range 7, |derivativeMoment k Phi T| ≤ c k :=
    (eventually_all_finset _).mpr (fun k _ => hbound k)
  filter_upwards [hall] with T hT
  intro k hk
  have hk' : k ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  exact (hT k hk').trans (Finset.single_le_sum (fun j _ => (hc j).le) hk')

#print axioms translated_polynomial
#print axioms operator_polynomial
#print axioms r_at_half
#print axioms linear_coefficient_pos
#print axioms xi_derivative_conj
#print axioms xi_derivative_one_sub
#print axioms xi_derivative_critical
#print axioms xi_even_im
#print axioms xi_odd_re
#print axioms eta_entire
#print axioms eta_im
#print axioms eta_im_zero_iff
#print axioms psi_entire
#print axioms psi_left
#print axioms smoothedMoment_eq
#print axioms smoothedMoment_tendsto
#print axioms smoothedMoment_bound
#print axioms single_operator
#print axioms derivativeMoment_eq
#print axioms derivativeMoments_bounded
end XiPrime8845.WuAuxiliary
