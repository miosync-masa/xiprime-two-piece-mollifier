import PRZZLocalization
import GcdDecomposition

/-! Exact gcd decomposition on the expanded fixed support [1/2,5/2].
The height T, cutoff, profiles and reflected shifts are unchanged. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory
namespace XiPrime8845.ExpandedGcd
open PRZZ PRZZLocalization GcdDecomposition

def mass (Phi : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (T/2) (5/2*T), (Phi (t/T) : ℂ)

def heightFactor (Phi : ℝ → ℝ) (T : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Icc (T/2) (5/2*T), ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ)

theorem weighted_integral_restrict (f : ℝ → ℂ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) (T : ℝ) (hT : 0 < T) :
    (∫ t, f t * (Phi (t/T) : ℂ)) =
      ∫ t in Set.Icc (T/2) (5/2*T), f t * (Phi (t/T) : ℂ) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : Phi (t/T) = 0 := by
    by_contra hh
    have hs := scaled_support hPhi hT t hh
    exact ht (by simpa only [one_div_mul_eq_div] using hs)
  simp [hz]

theorem weight_integrable (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) (T : ℝ) :
    IntegrableOn (fun t => (Phi (t/T) : ℂ)) (Set.Icc (T/2) (5/2*T)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop))).continuousOn

theorem phase_weight_integrable (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi)
    (T : ℝ) (hT : 0 < T) (s : ℂ) :
    IntegrableOn (fun t => ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ))
      (Set.Icc (T/2) (5/2*T)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have heq : Set.EqOn (fun t => ((2*Real.pi/t : ℝ) : ℂ)^s * (Phi (t/T) : ℂ))
      (fun t => Complex.exp ((Real.log (2*Real.pi/t) : ℂ)*s) * (Phi (t/T) : ℂ))
      (Set.Icc (T/2) (5/2*T)) := by
    intro t ht
    dsimp only
    rw [positive_cpow _ (div_pos (by positivity) ((half_pos hT).trans_le ht.1))]
  apply ContinuousOn.congr _ heq
  apply ContinuousOn.mul _ (by
    exact (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop))).continuousOn)
  apply ContinuousOn.cexp
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.log
  · exact continuousOn_const.div continuousOn_id (fun t ht => ((half_pos hT).trans_le ht.1).ne')
  · intro t ht
    exact (div_pos (by positivity) ((half_pos hT).trans_le ht.1)).ne'

theorem integrated_term (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) (T : ℝ) (hT : 0 < T)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (alpha beta : ℂ) :
    gcdWeight d e alpha beta * (∫ t : ℝ,
      (riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
        ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ)) =
      riemannZeta (1+alpha+beta) * gcdWeight d e alpha beta * mass Phi T +
      riemannZeta (1-alpha-beta) * gcdWeight d e (-beta) (-alpha) * heightFactor Phi T (alpha+beta) := by
  rw [weighted_integral_restrict _ Phi hPhi T hT, ← integral_const_mul]
  have heq : (∫ t in Set.Icc (T/2) (5/2*T), gcdWeight d e alpha beta *
      ((riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
        ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ))) =
      ∫ t in Set.Icc (T/2) (5/2*T),
        (riemannZeta (1+alpha+beta) * gcdWeight d e alpha beta) * (Phi (t/T) : ℂ) +
        (riemannZeta (1-alpha-beta) * gcdWeight d e (-beta) (-alpha)) *
          (((2*Real.pi/t : ℝ) : ℂ)^(alpha+beta) * (Phi (t/T) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have h := dual_weight d e hd he t ((half_pos hT).trans_le ht.1) alpha beta
    linear_combination riemannZeta (1-alpha-beta) * (Phi (t/T) : ℂ) * h
  rw [heq, integral_add ((weight_integrable Phi hPhi T).const_mul _)
    ((phase_weight_integrable Phi hPhi T hT _).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

theorem gcdMainTerm_split (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) (hT : 0 < T) (A B : ℂ) :
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

theorem normalized_gcd_split (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) :
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


#print axioms weighted_integral_restrict
#print axioms integrated_term
#print axioms gcdMainTerm_split
#print axioms normalized_gcd_split
end XiPrime8845.ExpandedGcd

