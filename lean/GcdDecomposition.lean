import ArithmeticRegularity

/-! Exact direct/dual separation of the literal PRZZ gcd main term.
No Euler-product asymptotic or inverse-Mellin identity is assumed. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory
namespace XiPrime8845.GcdDecomposition
open PRZZ ArithmeticRegularity

def gcdWeight (d e : ℕ) (alpha beta : ℂ) : ℂ :=
  (Nat.gcd d e : ℂ)^(alpha+beta) / ((d : ℂ)^alpha * (e : ℂ)^beta)

def arithmeticSum (a b : ℕ → ℂ) (N : ℕ) (alpha beta : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
    a d * star (b e) / (Nat.lcm d e : ℂ) * gcdWeight d e alpha beta

def mass (Phi : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc T (2*T), (Phi (t/T) : ℂ)

def heightFactor (Phi : ℝ → ℝ) (T : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Icc T (2*T), ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ)

theorem positive_cpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ)^s = Complex.exp ((Real.log x : ℂ)*s) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

theorem gcdWeight_exp (d e : ℕ) (hd : 0 < d) (he : 0 < e) (alpha beta : ℂ) :
    gcdWeight d e alpha beta = Complex.exp
      ((Real.log (Nat.gcd d e) : ℂ)*(alpha+beta) -
        (Real.log d : ℂ)*alpha - (Real.log e : ℂ)*beta) := by
  have hg : 0 < (Nat.gcd d e : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  unfold gcdWeight
  rw [← Complex.ofReal_natCast d, ← Complex.ofReal_natCast e,
    ← Complex.ofReal_natCast (Nat.gcd d e), positive_cpow _ hg,
    positive_cpow _ hd', positive_cpow _ he', ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring

/-- The reflected shifts are (-beta,-alpha), with no exchange of profiles. -/
theorem dual_weight (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (t : ℝ) (ht : 0 < t) (alpha beta : ℂ) :
    gcdWeight d e alpha beta *
        ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta) =
      ((2*Real.pi/t : ℝ) : ℂ)^(alpha+beta) * gcdWeight d e (-beta) (-alpha) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  have hg : 0 < (Nat.gcd d e : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left e hd
  rw [gcdWeight_exp d e hd he, gcdWeight_exp d e hd he,
    positive_cpow _ (by positivity), positive_cpow _ (by positivity),
    ← Complex.exp_add, ← Complex.exp_add]
  have hlog : Real.log (2*Real.pi*d*e/(t*(Nat.gcd d e : ℝ)^2)) =
      Real.log (2*Real.pi/t) + Real.log d + Real.log e - 2*Real.log (Nat.gcd d e) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity : 2*Real.pi*(d:ℝ) ≠ 0) he'.ne',
      Real.log_mul (by positivity : 2*Real.pi ≠ 0) hd'.ne',
      Real.log_mul ht.ne' (by positivity), Real.log_pow,
      Real.log_div (by positivity) ht.ne']
    ring
  rw [hlog]
  push_cast
  congr 1
  ring

theorem weight_integrable (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) (T : ℝ) :
    IntegrableOn (fun t => (Phi (t/T) : ℂ)) (Set.Icc T (2*T)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop))).continuousOn

theorem phase_weight_integrable (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (T : ℝ) (hT : 0 < T) (s : ℂ) :
    IntegrableOn (fun t => ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ))
      (Set.Icc T (2*T)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have heq : Set.EqOn (fun t => ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ))
      (fun t => Complex.exp ((Real.log (2*Real.pi/t) : ℂ)*s) * (Phi (t/T) : ℂ))
      (Set.Icc T (2*T)) := by
    intro t ht
    dsimp only
    rw [positive_cpow _ (div_pos (by positivity) (hT.trans_le ht.1))]
  apply ContinuousOn.congr _ heq
  apply ContinuousOn.mul _ (by
    exact (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop))).continuousOn)
  apply ContinuousOn.cexp
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.log
  · exact continuousOn_const.div continuousOn_id (fun t ht => (hT.trans_le ht.1).ne')
  · intro t ht
    exact (div_pos (by positivity) (hT.trans_le ht.1)).ne'

theorem integrated_term (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) (T : ℝ) (hT : 0 < T)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (alpha beta : ℂ) :
    gcdWeight d e alpha beta * (∫ t : ℝ,
      (riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
        ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ)) =
      riemannZeta (1+alpha+beta) * gcdWeight d e alpha beta * mass Phi T +
      riemannZeta (1-alpha-beta) * gcdWeight d e (-beta) (-alpha) * heightFactor Phi T (alpha+beta) := by
  rw [weighted_integral_restrict _ Phi hPhi T hT, ← integral_const_mul]
  have heq : (∫ t in Set.Icc T (2*T), gcdWeight d e alpha beta *
      ((riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
        ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ))) =
      ∫ t in Set.Icc T (2*T),
        (riemannZeta (1+alpha+beta) * gcdWeight d e alpha beta) * (Phi (t/T) : ℂ) +
        (riemannZeta (1-alpha-beta) * gcdWeight d e (-beta) (-alpha)) *
          (((2*Real.pi/t : ℝ) : ℂ)^(alpha+beta) * (Phi (t/T) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have h := dual_weight d e hd he t (hT.trans_le ht.1) alpha beta
    linear_combination riemannZeta (1-alpha-beta) * (Phi (t/T) : ℂ) * h
  rw [heq, integral_add ((weight_integrable Phi hPhi T).const_mul _)
    ((phase_weight_integrable Phi hPhi T hT _).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

theorem gcdMainTerm_split (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 0 < T) (A B : ℂ) :
    gcdMainTerm P Q theta T Phi A B =
      riemannZeta (1+A/(Real.log T : ℂ)+B/(Real.log T : ℂ)) *
        arithmeticSum (coefficient P theta T) (coefficient Q theta T) (cutoff theta T)
          (A/(Real.log T : ℂ)) (B/(Real.log T : ℂ)) * mass Phi T +
      riemannZeta (1-A/(Real.log T : ℂ)-B/(Real.log T : ℂ)) *
        arithmeticSum (coefficient P theta T) (coefficient Q theta T) (cutoff theta T)
          (-(B/(Real.log T : ℂ))) (-(A/(Real.log T : ℂ))) *
        heightFactor Phi T (A/(Real.log T : ℂ)+B/(Real.log T : ℂ)) := by
  unfold gcdMainTerm arithmeticSum
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have h := integrated_term Phi hPhi T hT d e (Finset.mem_Icc.mp hd).1
    (Finset.mem_Icc.mp he).1 (A/(Real.log T : ℂ)) (B/(Real.log T : ℂ))
  simp only [gcdWeight] at h ⊢
  linear_combination (coefficient P theta T d * star (coefficient Q theta T e) /
    (Nat.lcm d e : ℂ)) * h

/-- The arithmetic quantity whose uniform limit must still be identified with
the sum of the four H kernels. The factor log T is essential. -/
def scaledArithmetic (P Q : Profiles) (theta T : ℝ) (A B : ℂ) : ℂ :=
  (Real.log T : ℂ) * arithmeticSum (coefficient P theta T) (coefficient Q theta T)
    (cutoff theta T) (A/(Real.log T : ℂ)) (B/(Real.log T : ℂ))

theorem normalized_gcd_split (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) :
    gcdMainTerm P Q theta T Phi A B / (T : ℂ) =
      (riemannZeta (1+(A+B)/(Real.log T : ℂ))/(Real.log T : ℂ)) *
        scaledArithmetic P Q theta T A B * (mass Phi T/(T : ℂ)) +
      (riemannZeta (1-(A+B)/(Real.log T : ℂ))/(Real.log T : ℂ)) *
        scaledArithmetic P Q theta T (-B) (-A) *
        (heightFactor Phi T ((A+B)/(Real.log T : ℂ))/(T : ℂ)) := by
  rw [gcdMainTerm_split P Q theta T Phi hPhi (by linarith) A B]
  simp only [scaledArithmetic, add_div, neg_div]
  have hp : 1 + A/(Real.log T : ℂ) + B/(Real.log T : ℂ) =
      1 + (A/(Real.log T : ℂ)+B/(Real.log T : ℂ)) := by ring
  have hm : 1 - A/(Real.log T : ℂ) - B/(Real.log T : ℂ) =
      1 - (A/(Real.log T : ℂ)+B/(Real.log T : ℂ)) := by ring
  rw [hp, hm]
  have hL : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  field_simp

#print axioms positive_cpow
#print axioms gcdWeight_exp
#print axioms dual_weight
#print axioms weight_integrable
#print axioms phase_weight_integrable
#print axioms integrated_term
#print axioms gcdMainTerm_split
#print axioms normalized_gcd_split
end XiPrime8845.GcdDecomposition
