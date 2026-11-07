import PRZZLargeSpatialFamily
import PRZZScaledReplacement
import PRZZOptimalOuter

/-! Computed mollifier mass and logarithmic shift costs in large-M
pruning. The bound is uniform in both original cutoffs and in X; choosing
X=T^b can therefore be done before height, rather than depending on L. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex Set Filter
namespace XiPrime8845.PRZZLargeSpatialHeight
open PRZZLargeSpatialFamily PRZZLargeSpatialKernel PRZZGCoefficient
set_option maxHeartbeats 7000000

theorem coefficient_mass (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    mass (fun n => (coefficient js n:ℂ)) N t ≤ 2*Real.sqrt N*(Real.log N)^degree js := by
  unfold mass
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (Real.log N)^degree js*(1/Real.sqrt n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_div,← Complex.ofReal_natCast n,norm_cpow_eq_rpow_re_of_pos hn0]
      have he : (1/2+(t:ℂ)*I).re = (1/2:ℝ) := by simp
      rw [he,← Real.sqrt_eq_rpow]
      have hc : ‖(coefficient js n:ℂ)‖ ≤ (Real.log N)^degree js := by
        simpa using coefficient_bound js N hN n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
      exact (div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _)).trans_eq (by ring)
    _ = (Real.log N)^degree js*(∑ n ∈ Icc 1 N, 1/Real.sqrt n) := by rw [mul_sum]
    _ ≤ (Real.log N)^degree js*(2*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (PRZZReplacementMass.reciprocal_sqrt_sum N)
        (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)
    _ = _ := by ring

theorem constant_scaled (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (A B : ℂ),
      1 ≤ L → r ≤ ‖A+B‖ → constant ((A+B)/(L:ℂ)) ≤ C*L^2 := by
  let D := Real.exp (16:ℝ)/(8*Real.sqrt Real.pi)
  let E := 10*Real.exp (16:ℝ)/Real.sqrt Real.pi
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨D+E/r^2+1,by positivity,?_⟩
  intro L A B hL hsep
  have hh := PRZZJetUniform.shift_cost D E r L A B hE hr (by linarith) hsep
  have he : constant ((A+B)/(L:ℂ)) = D+E/‖(A+B)/(L:ℂ)‖^2 := by
    dsimp [constant,D,E]
    ring
  rw [he]
  apply hh.trans
  have hL2 : 1 ≤ L^2 := by nlinarith
  have he2 : E*L^2/r^2 = (E/r^2)*L^2 := by ring
  rw [he2]
  nlinarith [mul_le_mul_of_nonneg_left hL2 hD]

/-- All mollifier coefficients and the shift singularity are supplied.
The constant precedes N,T,X,L and every original coefficient index. -/
theorem retained_uniform (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (js : List ℕ) (Z r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N : ℕ) (A B : ℂ) (t X : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      t ∈ Icc T (2*T) → 0 < X →
      ‖PRZZWRowLimit.retained L N (fun y => (S y:ℂ)) (fun s _ => X ≤ (2:ℝ)^s)
        (fun n => (coefficient js n:ℂ)) (fun n => (coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^6/X^2 := by
  obtain ⟨Cs,hCs,hshift⟩ := constant_scaled r hr
  obtain ⟨Cl,hCl,hlog⟩ := PRZZOptimalOuter.power_log_absorbed (2*degree js+2) 0 1 (by norm_num)
  let D := 16*Cs*PRZZWeightTail.squareMass^2/Real.pi^4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D*Cl+1,by positivity,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually Z (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hsmall hT
  intro L N A B t X hN hNT hA hB hsep ht hX
  have hT0 : 0 < T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have ha := (abs_le.mp ((abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA))).1
  have hb := (abs_le.mp ((abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB))).1
  have hbase := retained_large_bound S hm hlo hhi hleft hright L N
    (fun n => (coefficient js n:ℂ)) (fun n => (coefficient js n:ℂ))
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hs (by linarith) (by linarith) T t X hT0 ht hX
  rw [← add_div] at hbase
  have hc := hshift (Real.log T) A B hsmall.1 hsep
  have hmass := coefficient_mass js N hN t
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hm0 : 0 ≤ mass (fun n => (coefficient js n:ℂ)) N t := sum_nonneg (fun n hn => norm_nonneg _)
  have hlogs : (Real.log N)^degree js ≤ (Real.log T)^degree js := by gcongr
  have hlogT : 0 ≤ Real.log T := by linarith [hsmall.1]
  have hmassT : mass (fun n => (coefficient js n:ℂ)) N t ≤
      2*Real.sqrt N*(Real.log T)^degree js :=
    hmass.trans (mul_le_mul_of_nonneg_left hlogs (by positivity))
  have hh := hlog T (by linarith)
  simp only [Real.rpow_zero,one_mul,Real.rpow_one] at hh
  apply hbase.trans
  calc
    _ ≤ (4*(Cs*(Real.log T)^2)*(T/Real.pi)^4/X^2)*PRZZWeightTail.squareMass^2*
        (2*Real.sqrt N*(Real.log T)^degree js)*(2*Real.sqrt N*(Real.log T)^degree js) := by
      gcongr
    _ = D*T^4*(Real.sqrt N)^2*(Real.log T)^(2*degree js+2)/X^2 := by
      dsimp [D]
      rw [show 2*degree js+2 = degree js+degree js+2 by omega,pow_add,pow_add]
      ring
    _ = D*T^4*(N:ℝ)*(Real.log T)^(2*degree js+2)/X^2 := by
      rw [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)]
    _ ≤ D*T^5*(Real.log T)^(2*degree js+2)/X^2 := by
      calc
        _ ≤ D*T^4*T*(Real.log T)^(2*degree js+2)/X^2 := by gcongr
        _ = _ := by ring
    _ = (D*T^5/X^2)*(Real.log T)^(2*degree js+2) := by ring
    _ ≤ (D*T^5/X^2)*(Cl*T) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (D*Cl)*T^6/X^2 := by ring
    _ ≤ _ := by gcongr; linarith

#print axioms coefficient_mass
#print axioms constant_scaled
#print axioms retained_uniform
end XiPrime8845.PRZZLargeSpatialHeight
