import ConreyOuter

/-! Exact adapter from the original PRZZ coefficient double sum (Feng profile
zero) to the actual Conrey diagonal sum. No asymptotic input is used in the
finite identity; real profile coefficients discharge the conjugation. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.ConreyCoefficientBridge
open ElementaryGcd GcdDecomposition
set_option maxHeartbeats 1000000

def profile (P : Polynomial ℝ) : PRZZ.Profiles := ⟨P, 0⟩
def complexify (P : Polynomial ℝ) : Polynomial ℂ := P.map Complex.ofRealHom

theorem complexify_eval (P : Polynomial ℝ) (x : ℝ) :
    (complexify P).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  change (P.map Complex.ofRealHom).eval (Complex.ofRealHom x) = Complex.ofRealHom (P.eval x)
  exact Polynomial.eval_map_apply _ _

theorem length_exp (θ T : ℝ) (hT : 1 < T) :
    PRZZ.length θ T = Real.exp (Real.log T * θ) := by
  exact Real.rpow_def_of_pos (by linarith) θ

theorem cutoff_eq (θ T : ℝ) (hT : 1 < T) :
    PRZZ.cutoff θ T = ⌊Real.exp (Real.log T * θ)⌋₊ := by
  simp only [PRZZ.cutoff, length_exp θ T hT]

theorem coefficient_star (P : Polynomial ℝ) (θ T : ℝ) (n : ℕ) :
    star (PRZZ.coefficient (profile P) θ T n) = PRZZ.coefficient (profile P) θ T n := by
  unfold PRZZ.coefficient
  split_ifs <;> simp

theorem coefficient_in_range (P : Polynomial ℝ) (θ T : ℝ) (_hθ : 0 < θ) (hT : 1 < T)
    (n : ℕ) (hn : n ∈ Icc 1 (PRZZ.cutoff θ T)) :
    PRZZ.coefficient (profile P) θ T n =
      (μ n : ℂ) * (complexify P).eval
        (((θ-Real.log n/Real.log T)/θ : ℝ) : ℂ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hlen : 0 < PRZZ.length θ T := by rw [length_exp θ T hT]; positivity
  have hsupport : 1 ≤ n ∧ (n : ℝ) ≤ PRZZ.length θ T :=
    ⟨(mem_Icc.mp hn).1, (Nat.le_floor_iff hlen.le).mp (mem_Icc.mp hn).2⟩
  rw [PRZZ.coefficient, if_pos hsupport]
  simp only [profile, Polynomial.eval_zero, mul_zero, zero_div, add_zero,
    PRZZ.muReal, ArithmeticFunction.coe_mk, Complex.ofReal_mul, Complex.ofReal_intCast,
    complexify_eval]
  congr 2
  rw [Real.log_div hlen.ne' hn0.ne', length_exp θ T hT, Real.log_exp]
  field_simp

theorem reciprocal_shift (n : ℕ) (hn : 0 < n) (A : ℂ) (L : ℝ) :
    1/(n : ℂ)^(1+A/L) = Complex.exp (-A*(Real.log n/L : ℝ)) / n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_add _ _ hn0, Complex.cpow_one,
    ← Complex.ofReal_natCast n, positive_cpow _ (by exact_mod_cast hn)]
  simp only [one_div, mul_inv_rev]
  rw [← Complex.exp_neg]
  have he : -((Real.log n : ℂ)*(A/(L : ℂ))) = -A*(Real.log n/L : ℝ) := by
    push_cast
    ring
  rw [he]
  ring

theorem inner_coefficient (P : Polynomial ℝ) (θ T : ℝ) (hθ : 0 < θ) (hT : 1 < T)
    (g : ℕ) (hg : 0 < g) (A : ℂ) :
    (∑ n ∈ Icc 1 (PRZZ.cutoff θ T/g),
      PRZZ.coefficient (profile P) θ T (g*n)/(n : ℂ)^(1+A/(Real.log T : ℂ))) =
      (μ g : ℂ) * CoprimeShift.coprimeInner
        ⌊Real.exp (Real.log T*(θ-Real.log g/Real.log T))⌋₊ g
        (Real.log T) (θ-Real.log g/Real.log T) θ (complexify P) A := by
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hcut : PRZZ.cutoff θ T/g =
      ⌊Real.exp (Real.log T*(θ-Real.log g/Real.log T))⌋₊ := by
    rw [cutoff_eq θ T hT, CoprimeShift.translated_cutoff _ _ _ hL hg.ne']
  rw [CoprimeShift.coprimeInner, ← hcut, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hgn : g*n ∈ Icc 1 (PRZZ.cutoff θ T) := by
    refine mem_Icc.mpr ⟨Nat.mul_pos hg hn0, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp (mem_Icc.mp hn).2
  rw [coefficient_in_range P θ T hθ hT _ hgn, SmoothMobius.moebius_mul_indicator]
  have harg : (θ-Real.log ((g*n : ℕ) : ℝ)/Real.log T)/θ =
      ((θ-Real.log g/Real.log T)-Real.log n/Real.log T)/θ := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hn0.ne')]
    ring
  rw [harg]
  have hr := reciprocal_shift n hn0 A (Real.log T)
  by_cases hcop : n.Coprime g
  · rw [if_pos hcop, if_pos hcop]
    unfold ShiftWeights.weight
    calc
      _ = (μ g : ℂ)*(μ n : ℂ) *
          (complexify P).eval (((θ-Real.log g/Real.log T-Real.log n/Real.log T)/θ : ℝ) : ℂ) *
          (1/(n : ℂ)^(1+A/(Real.log T : ℂ))) := by ring
      _ = _ := by rw [hr]; ring
  · simp only [if_neg hcop, mul_zero, zero_mul, zero_div]

/-- Exact identification with the original coefficient arithmetic sum.
No zero-endpoint assumptions on the profiles are needed in this identity. -/
theorem scaledArithmetic_eq_actualSum (P Q : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (A B : ℂ) :
    scaledArithmetic (profile P) (profile Q) θ T A B =
      ConreyOuter.actualSum (Real.log T) θ (complexify P) (complexify Q) A B := by
  have hL : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  rw [scaledArithmetic, arithmeticSum_diagonal_quotient]
  simp_rw [coefficient_star]
  unfold ConreyOuter.actualSum
  have hs : Icc 1 (PRZZ.cutoff θ T) = Ioc 0 (CoprimeEndpoint.cutoff (Real.log T) θ) := by
    rw [cutoff_eq θ T hT]
    ext n
    simp only [mem_Icc, mem_Ioc, CoprimeEndpoint.cutoff]
    omega
  rw [← hs, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g hg
  have hg0 := (mem_Icc.mp hg).1
  rw [inner_coefficient P θ T hθ hT g hg0 A,
    inner_coefficient Q θ T hθ hT g hg0 B]
  unfold BareEuler.weight CoprimeApproximation.actual LogProfileSum.coordinate
  field_simp

/-- The original PRZZ coefficient arithmetic sum now has its H00 limit.
This specializes to the Conrey component only, not the Feng cross terms. -/
theorem scaledArithmetic_twoBidiscs (P Q : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (profile P) (profile Q)
        PRZZAsymptotic.theta T p.1 p.2)
      (fun p => BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta (complexify P) (complexify Q))
      atTop ElementaryGcd.twoBidiscs := by
  have hPc : (complexify P).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero, hP] using complexify_eval P 0
  have hQc : (complexify Q).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero, hQ] using complexify_eval Q 0
  have h := ConreyOuter.actualSum_twoBidiscs (complexify P) (complexify Q) hPc hQc
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp h eps heps)] with T hT hlim
  intro p hp
  rw [scaledArithmetic_eq_actualSum P Q _ T (by norm_num [PRZZAsymptotic.theta]) hT]
  exact hlim p hp

theorem scaledArithmetic_reflected (P Q : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (profile P) (profile Q)
        PRZZAsymptotic.theta T (-p.2) (-p.1))
      (fun p => BetaKernel.H 0 0 (-p.2) (-p.1) PRZZAsymptotic.theta (complexify P) (complexify Q))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (scaledArithmetic_twoBidiscs P Q hP hQ)

/-- Exact original gcd-main-term interface: both arithmetic factors are
replaced by their diagonal sums, with the original swapped dual retained. -/
theorem normalized_gcdMainTerm_eq (P Q : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (A B : ℂ) :
    PRZZ.gcdMainTerm (profile P) (profile Q) θ T Phi A B / (T : ℂ) =
      (riemannZeta (1+(A+B)/(Real.log T : ℂ))/(Real.log T : ℂ)) *
        ConreyOuter.actualSum (Real.log T) θ (complexify P) (complexify Q) A B * (mass Phi T/(T : ℂ)) +
      (riemannZeta (1-(A+B)/(Real.log T : ℂ))/(Real.log T : ℂ)) *
        ConreyOuter.actualSum (Real.log T) θ (complexify P) (complexify Q) (-B) (-A) *
        (heightFactor Phi T ((A+B)/(Real.log T : ℂ))/(T : ℂ)) := by
  rw [normalized_gcd_split _ _ _ _ _ hPhi hT,
    scaledArithmetic_eq_actualSum P Q θ T hθ hT,
    scaledArithmetic_eq_actualSum P Q θ T hθ hT]

#print axioms coefficient_in_range
#print axioms inner_coefficient
#print axioms scaledArithmetic_eq_actualSum
#print axioms scaledArithmetic_twoBidiscs
#print axioms scaledArithmetic_reflected
#print axioms normalized_gcdMainTerm_eq
end XiPrime8845.ConreyCoefficientBridge
