import FengCoefficientBridge
import FengOutsideMainTerm

/-! Exact theta^-2 normalization of the ordered mixed PRZZ coefficient sums.
Both H02 and H20 follow from the actual three-block limit on both bidiscs.
No K22, moment identification or zero-counting assertion is made here. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengCrossCoefficient
open GcdDecomposition ConreyCoefficientBridge FengCoefficientBridge
set_option maxHeartbeats 1000000

theorem feng_coefficient_in_range (G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (n : ℕ) (hn : n ∈ Icc 1 (PRZZ.cutoff θ T)) :
    PRZZ.coefficient (fengProfile G) θ T n =
      (PRZZ.fengArithmetic n : ℂ) *
        (complexify G).eval (((θ-Real.log n/Real.log T)/θ : ℝ) : ℂ) /
          ((θ : ℂ)^2*(Real.log T : ℂ)^2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hlen : 0 < PRZZ.length θ T := by rw [length_exp θ T hT]; positivity
  have hsupport : 1 ≤ n ∧ (n : ℝ) ≤ PRZZ.length θ T :=
    ⟨(mem_Icc.mp hn).1, (Nat.le_floor_iff hlen.le).mp (mem_Icc.mp hn).2⟩
  rw [feng_coefficient, if_pos hsupport]
  have he : Real.log (PRZZ.length θ T/n)/Real.log (PRZZ.length θ T) =
      (θ-Real.log n/Real.log T)/θ := by
    rw [Real.log_div hlen.ne' hn0.ne',length_exp θ T hT,Real.log_exp]
    field_simp [(Real.log_pos hT).ne',hθ.ne']
  rw [he,complexify_eval,length_exp θ T hT,Real.log_exp]
  push_cast
  ring

/-- L times the original Feng inner coefficient is fengBlock/theta^2.
The full fengArithmetic(g*n), including non-squarefree terms, is retained. -/
theorem feng_inner_scaled (G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (g : ℕ) (hg : 0 < g) (A : ℂ) :
    (Real.log T : ℂ)*inner (fengProfile G) θ T g A =
      FengAtG.fengBlock ⌊Real.exp (Real.log T*(θ-Real.log g/Real.log T))⌋₊
        g (Real.log T) (θ-Real.log g/Real.log T) θ (complexify G) A / (θ : ℂ)^2 := by
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hcut : PRZZ.cutoff θ T/g =
      ⌊Real.exp (Real.log T*(θ-Real.log g/Real.log T))⌋₊ := by
    rw [cutoff_eq θ T hT,CoprimeShift.translated_cutoff _ _ _ hL hg.ne']
  unfold FengCoefficientBridge.inner FengAtG.fengBlock
  rw [← hcut,Finset.mul_sum,Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hgn : g*n ∈ Icc 1 (PRZZ.cutoff θ T) := by
    refine mem_Icc.mpr ⟨Nat.mul_pos hg hn0,?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp (mem_Icc.mp hn).2
  rw [feng_coefficient_in_range G θ T hθ hT _ hgn]
  have harg : (θ-Real.log ((g*n : ℕ) : ℝ)/Real.log T)/θ =
      ((θ-Real.log g/Real.log T)-Real.log n/Real.log T)/θ := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hn0.ne')]
    ring
  rw [harg,div_eq_mul_one_div _ ((n:ℂ)^(1+A/(Real.log T:ℂ))),
    reciprocal_shift n hn0 A (Real.log T)]
  unfold ShiftWeights.weight
  ring

theorem conrey_inner_scaled (P : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (g : ℕ) (hg : 0 < g) (A : ℂ) :
    (Real.log T : ℂ)*inner (profile P) θ T g A =
      FengMixedInterior.conrey (Real.log T) g (θ-Real.log g/Real.log T) θ (complexify P) A := by
  rw [FengCoefficientBridge.inner,inner_coefficient P θ T hθ hT g hg A]
  unfold FengMixedInterior.conrey CoprimeApproximation.actual
  ring

/-- Exact finite bridge; no vanishing profile endpoint is needed. -/
theorem scaledArithmetic02_eq (P G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (A B : ℂ) :
    scaledArithmetic (profile P) (fengProfile G) θ T A B =
      FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) A B / (θ:ℂ)^2 := by
  have hL : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  have hs : Icc 1 (PRZZ.cutoff θ T) = Ioc 0 (CoprimeEndpoint.cutoff (Real.log T) θ) := by
    rw [cutoff_eq θ T hT]
    ext n
    simp only [mem_Icc,mem_Ioc,CoprimeEndpoint.cutoff]
    omega
  rw [scaledArithmetic_diagonal,FengCrossAssembly.fullSum,← hs]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro g hg
  have hc := conrey_inner_scaled P θ T hθ hT g (mem_Icc.mp hg).1 A
  have hf := feng_inner_scaled G θ T hθ hT g (mem_Icc.mp hg).1 B
  unfold FengMixedShift.rawWeight LogProfileSum.coordinate
  rw [← hc]
  calc
    _ = ElementaryGcd.generalizedTotient (1+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) g /
          (g:ℂ)^(2+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) *
          ((Real.log T:ℂ)*inner (profile P) θ T g A) *
          ((Real.log T:ℂ)*inner (fengProfile G) θ T g B) / (Real.log T:ℂ) := by
      field_simp
    _ = _ := by rw [hf]; ring

/-- Transposition exchanges profiles AND shifts, with real coefficients
discharging star. It does not identify the two ordered terms at fixed shifts. -/
theorem scaledArithmetic_swap (P Q : PRZZ.Profiles) (θ T : ℝ) (A B : ℂ) :
    scaledArithmetic P Q θ T A B = scaledArithmetic Q P θ T B A := by
  simp only [scaledArithmetic,arithmeticSum,FengCoefficientBridge.coefficient_star]
  rw [Finset.sum_comm]
  congr 1
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  unfold gcdWeight
  rw [Nat.gcd_comm e d,Nat.lcm_comm e d,add_comm (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))]
  ring

theorem scaledArithmetic20_eq (G P : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (A B : ℂ) :
    scaledArithmetic (fengProfile G) (profile P) θ T A B =
      FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) B A / (θ:ℂ)^2 := by
  rw [scaledArithmetic_swap,scaledArithmetic02_eq P G θ T hθ hT]

theorem swap_mem_twoBidiscs (p : ℂ × ℂ) (hp : p ∈ ElementaryGcd.twoBidiscs) :
    (p.2,p.1) ∈ ElementaryGcd.twoBidiscs := by
  rcases hp with hp | hp
  · exact Or.inl ⟨hp.2,hp.1⟩
  · apply Or.inr
    rw [ElementaryGcd.reflectedBidisc_center] at hp ⊢
    exact ⟨hp.2,hp.1⟩

theorem scaledArithmetic02_twoBidiscs (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (profile P) (fengProfile G)
        PRZZAsymptotic.theta T p.1 p.2)
      (fun p => BetaKernel.H 0 2 p.1 p.2 PRZZAsymptotic.theta (complexify P) (complexify G))
      atTop ElementaryGcd.twoBidiscs := by
  have hPc : (complexify P).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero,hP] using complexify_eval P 0
  have hGc : (complexify G).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero,hG] using complexify_eval G 0
  have h := FengOutsideMainTerm.fullSum_twoBidiscs (complexify P) (complexify G) hPc hGc
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hden : 0 < ‖(PRZZAsymptotic.theta : ℂ)^2‖ := norm_pos_iff.mpr (pow_ne_zero _ (by exact_mod_cast hθ.ne'))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp h (eps*‖(PRZZAsymptotic.theta:ℂ)^2‖)
      (mul_pos heps hden))] with T hT hh
  intro p hp
  have ht := hh p hp
  rw [dist_comm,dist_eq_norm] at ht ⊢
  rw [scaledArithmetic02_eq P G _ T hθ hT,BetaKernel.H]
  simp only [Nat.zero_add,← sub_div,norm_div]
  exact (div_lt_iff₀ hden).mpr ht

theorem scaledArithmetic20_twoBidiscs (G P : Polynomial ℝ)
    (hG : G.eval 0 = 0) (hP : P.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (fengProfile G) (profile P)
        PRZZAsymptotic.theta T p.1 p.2)
      (fun p => BetaKernel.H 2 0 p.1 p.2 PRZZAsymptotic.theta (complexify G) (complexify P))
      atTop ElementaryGcd.twoBidiscs := by
  have h := scaledArithmetic02_twoBidiscs P G hP hG
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hh
  intro p hp
  rw [scaledArithmetic_swap,← BetaKernel.H02_swap]
  exact hh (p.2,p.1) (swap_mem_twoBidiscs p hp)

theorem scaledArithmetic02_reflected (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (profile P) (fengProfile G)
        PRZZAsymptotic.theta T (-p.2) (-p.1))
      (fun p => BetaKernel.H 0 2 (-p.2) (-p.1) PRZZAsymptotic.theta (complexify P) (complexify G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (scaledArithmetic02_twoBidiscs P G hP hG)

theorem scaledArithmetic20_reflected (G P : Polynomial ℝ)
    (hG : G.eval 0 = 0) (hP : P.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (fengProfile G) (profile P)
        PRZZAsymptotic.theta T (-p.2) (-p.1))
      (fun p => BetaKernel.H 2 0 (-p.2) (-p.1) PRZZAsymptotic.theta (complexify G) (complexify P))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (scaledArithmetic20_twoBidiscs G P hG hP)


/-- Exact original gcd interface for the ordered 02 component. The two
theta^-2 factors and the swapped reflected arithmetic arguments are explicit. -/
theorem normalized_gcd02_eq (P G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (A B : ℂ) :
    PRZZ.gcdMainTerm (profile P) (fengProfile G) θ T Phi A B/(T:ℂ) =
      (riemannZeta (1+(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) A B/(θ:ℂ)^2) *
        (mass Phi T/(T:ℂ)) +
      (riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) (-B) (-A)/(θ:ℂ)^2) *
        (heightFactor Phi T ((A+B)/(Real.log T:ℂ))/(T:ℂ)) := by
  rw [normalized_gcd_split _ _ _ _ _ hPhi hT,
    scaledArithmetic02_eq P G θ T hθ hT,scaledArithmetic02_eq P G θ T hθ hT]

/-- In the 20 component transposition changes the dual arguments to (-A,-B)
inside the 02-oriented fullSum; the original PRZZ dual remains (-B,-A). -/
theorem normalized_gcd20_eq (G P : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (A B : ℂ) :
    PRZZ.gcdMainTerm (fengProfile G) (profile P) θ T Phi A B/(T:ℂ) =
      (riemannZeta (1+(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) B A/(θ:ℂ)^2) *
        (mass Phi T/(T:ℂ)) +
      (riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengCrossAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) (-A) (-B)/(θ:ℂ)^2) *
        (heightFactor Phi T ((A+B)/(Real.log T:ℂ))/(T:ℂ)) := by
  rw [normalized_gcd_split _ _ _ _ _ hPhi hT,
    scaledArithmetic20_eq G P θ T hθ hT,scaledArithmetic20_eq G P θ T hθ hT]

#print axioms normalized_gcd02_eq
#print axioms normalized_gcd20_eq

#print axioms feng_coefficient_in_range
#print axioms feng_inner_scaled
#print axioms conrey_inner_scaled
#print axioms scaledArithmetic02_eq
#print axioms scaledArithmetic_swap
#print axioms scaledArithmetic20_eq
#print axioms swap_mem_twoBidiscs
#print axioms scaledArithmetic02_twoBidiscs
#print axioms scaledArithmetic20_twoBidiscs
#print axioms scaledArithmetic02_reflected
#print axioms scaledArithmetic20_reflected
end XiPrime8845.FengCrossCoefficient
