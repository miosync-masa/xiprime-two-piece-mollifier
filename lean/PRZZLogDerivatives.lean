import PRZZGaussianDerivatives

/-! Conversion from logarithmic to ordinary derivatives on x>0.
No identity at x=0 is used. Each ordinary derivative has its exact x^-n
factor and a recursively computed polynomial in log x. -/
noncomputable section
open Polynomial Filter Topology
namespace XiPrime8845.PRZZLogDerivatives
open PRZZGaussianDerivatives

def scaled (n : ℕ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  weighted P (Real.log x)/x^n
def next (n : ℕ) (P : Polynomial ℝ) : Polynomial ℝ := step P-C (n:ℝ)*P
def polys (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | n+1 => next n (polys P n)

theorem scaled_hasDerivAt (n : ℕ) (P : Polynomial ℝ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (scaled n P) (scaled (n+1) (next n P) x) x := by
  have hh := ((weighted_hasDerivAt P (Real.log x)).comp x
    (Real.hasDerivAt_log hx.ne')).div ((hasDerivAt_id x).pow n) (pow_ne_zero n hx.ne')
  convert hh using 1 <;> first | rfl | skip
  simp only [scaled,next,weighted,eval_sub,eval_mul,eval_C,id_eq,
    Pi.pow_apply,Function.comp_apply]
  cases n <;> simp only [Nat.add_sub_cancel,pow_zero,pow_succ,Nat.cast_zero,zero_mul,mul_zero,sub_zero]
  all_goals field_simp

/-- All ordinary derivatives of a polynomial Gaussian in log x. -/
theorem ordinary_iterated (P : Polynomial ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun y => weighted P (Real.log y)) x = scaled n (polys P n) x := by
  induction n generalizing x with
  | zero => simp [scaled,polys]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : (fun y => iteratedDeriv n (fun z => weighted P (Real.log z)) y) =ᶠ[𝓝 x]
        scaled n (polys P n) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (scaled_hasDerivAt n (polys P n) x hx).deriv

/-- A single exponential majorant absorbs every fixed monomial. -/
theorem monomial_decay (n : ℕ) (a l : ℝ) :
    |l|^n*Real.exp (-l^2/4) ≤
      (n.factorial:ℝ)*Real.exp ((|a|+1)^2)*Real.exp (-a*l) := by
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp |l| (abs_nonneg l) n)
  have he : Real.exp (|l|-l^2/4) ≤ Real.exp ((|a|+1)^2-a*l) := by
    apply Real.exp_le_exp.mpr
    have hh : a*l ≤ |a| * |l| := by simpa [abs_mul] using le_abs_self (a*l)
    nlinarith [sq_nonneg (|l|-2*(|a|+1)),sq_abs l]
  calc
    _ ≤ (Real.exp |l| * (n.factorial:ℝ))*Real.exp (-l^2/4) := by gcongr
    _ = (n.factorial:ℝ)*Real.exp (|l|-l^2/4) := by
      rw [show |l|-l^2/4 = |l|+(-l^2/4) by ring,Real.exp_add]; ring
    _ ≤ (n.factorial:ℝ)*Real.exp ((|a|+1)^2-a*l) := by gcongr
    _ = _ := by
      rw [show (|a|+1)^2-a*l = (|a|+1)^2+(-a*l) by ring,Real.exp_add]
      ring

/-- Uniform in the logarithmic variable, for any prescribed decay rate. -/
theorem weighted_decay (P : Polynomial ℝ) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l, |weighted P l| ≤ C*Real.exp (-a*l) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨C,hC,hP⟩ := hP
    obtain ⟨D,hD,hQ⟩ := hQ
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro l
    have he : weighted (P+Q) l = weighted P l+weighted Q l := by simp [weighted,add_mul]
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (hP l) (hQ l)).trans_eq (by ring))
  | monomial n c =>
    refine ⟨|c| * (n.factorial:ℝ)*Real.exp ((|a|+1)^2),by positivity,?_⟩
    intro l
    have h := mul_le_mul_of_nonneg_left (monomial_decay n a l) (abs_nonneg c)
    simpa [weighted,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _),mul_assoc] using h

theorem ordinary_decay (P : Polynomial ℝ) (n : ℕ) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      |iteratedDeriv n (fun y => weighted P (Real.log y)) x| ≤ C*x^(-a)/x^n := by
  obtain ⟨C,hC,h⟩ := weighted_decay (polys P n) a
  refine ⟨C,hC,?_⟩
  intro x hx
  rw [ordinary_iterated P n x hx,scaled,abs_div,abs_of_pos (pow_pos hx n)]
  have he : Real.exp (-a*Real.log x) = x^(-a) := by
    rw [Real.rpow_def_of_pos hx]; congr 1; ring
  have hh := h (Real.log x)
  rw [he] at hh
  exact div_le_div_of_nonneg_right hh (by positivity)

def tailPolys : ℕ → Polynomial ℝ
  | 0 => -1
  | n+1 => next (n+1) (tailPolys n)

theorem tail_ordinary (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv (n+1) (fun y => PRZZSourceW.tail (Real.log y)) x =
      scaled (n+1) (tailPolys n) x := by
  induction n generalizing x with
  | zero =>
    rw [iteratedDeriv_one]
    have hh := (PRZZSourceDecay.tail_hasDerivAt (Real.log x)).comp x
      (Real.hasDerivAt_log hx.ne')
    dsimp only [Function.comp_def] at hh
    rw [hh.deriv]
    simp [scaled,tailPolys,weighted,div_eq_mul_inv]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : (fun y => iteratedDeriv (n+1) (fun z => PRZZSourceW.tail (Real.log z)) y)
        =ᶠ[𝓝 x] scaled (n+1) (tailPolys n) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (scaled_hasDerivAt (n+1) (tailPolys n) x hx).deriv

theorem tail_ordinary_decay (n : ℕ) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      |iteratedDeriv (n+1) (fun y => PRZZSourceW.tail (Real.log y)) x| ≤
        C*x^(-a)/x^(n+1) := by
  obtain ⟨C,hC,h⟩ := weighted_decay (tailPolys n) a
  refine ⟨C,hC,?_⟩
  intro x hx
  rw [tail_ordinary n x hx,scaled,abs_div,abs_of_pos (pow_pos hx (n+1))]
  have he : Real.exp (-a*Real.log x) = x^(-a) := by
    rw [Real.rpow_def_of_pos hx]; congr 1; ring
  have hh := h (Real.log x)
  rw [he] at hh
  exact div_le_div_of_nonneg_right hh (by positivity)

#print axioms tail_ordinary
#print axioms tail_ordinary_decay
#print axioms monomial_decay
#print axioms weighted_decay
#print axioms ordinary_decay
#print axioms scaled_hasDerivAt
#print axioms ordinary_iterated
end XiPrime8845.PRZZLogDerivatives
