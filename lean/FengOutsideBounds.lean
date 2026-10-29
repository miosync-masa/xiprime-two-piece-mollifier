import FengPrimeMass
import FengLogEndpoint

/-! Endpoint-safe off-g prime-power bounds. The finite replacement error is
controlled by an explicit input envelope, not asserted to tend to zero. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengOutsideBounds
open FengAtG FengOutside CoprimeShift ShiftWeights ShiftedEndpoint WeightedMobius
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem mark_support_bound (r : ℕ) (L U C : ℝ) (A : ℂ)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hr : r ∈ Icc 1 ⌊Real.exp (L*U)⌋₊) :
    ‖mark r*supportFactor r L A‖ ≤
      Real.exp (C*U)*(ArithmeticFunction.vonMangoldt r*Real.log r/(r:ℝ)) := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp hr).1
  have hr0 : (0:ℝ) < r := by linarith
  have hlog : Real.log r ≤ L*U := (Real.log_le_iff_le_exp hr0).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2)
  have ht := normalized_log_mem r L U hr1 hL hlog
  have hb := exp_weight_bound A (Real.log r/L) C U hA
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hm : 0 ≤ ArithmeticFunction.vonMangoldt r*Real.log r :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_nonneg hr1)
  have hmnorm : ‖mark r‖ = ArithmeticFunction.vonMangoldt r*Real.log r := by
    rw [mark,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  rw [norm_mul,hmnorm,supportFactor,norm_div,Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hb hr0.le) hm
  convert! hh using 1 <;> ring

/-- The convolution has a bounded operator norm, uniform in every g. -/
theorem transform_uniform_error_bound (g : ℕ) (L U C D : ℝ) (A : ℂ)
    (X Y : ℕ → ℂ) (hL : 0 < L) (hU : 0 ≤ U) (hA : ‖A‖ ≤ C) (hD : 0 ≤ D)
    (hXY : ∀ r ∈ (Icc 1 ⌊Real.exp (L*U)⌋₊).filter (fun r => r.Coprime g),
      ‖X r-Y r‖ ≤ D) :
    ‖transform ⌊Real.exp (L*U)⌋₊ g L A X-transform ⌊Real.exp (L*U)⌋₊ g L A Y‖ ≤
      2*U^2*Real.exp (C*U)*D := by
  have hs : (∑ r ∈ (Icc 1 ⌊Real.exp (L*U)⌋₊).filter (fun r => r.Coprime g),
      ‖mark r*supportFactor r L A‖*‖X r-Y r‖) ≤
      Real.exp (C*U)*D*FengPrimeMass.mass ⌊Real.exp (L*U)⌋₊ := by
    calc
      _ ≤ ∑ r ∈ (Icc 1 ⌊Real.exp (L*U)⌋₊).filter (fun r => r.Coprime g),
          Real.exp (C*U)*D*(ArithmeticFunction.vonMangoldt r*Real.log r/(r:ℝ)) := by
        apply sum_le_sum
        intro r hr
        have hm := mark_support_bound r L U C A hL hA (mem_filter.mp hr).1
        have hh := mul_le_mul hm (hXY r hr) (norm_nonneg _) ((norm_nonneg _).trans hm)
        convert hh using 1 <;> ring
      _ ≤ ∑ r ∈ Icc 1 ⌊Real.exp (L*U)⌋₊,
          Real.exp (C*U)*D*(ArithmeticFunction.vonMangoldt r*Real.log r/(r:ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro r hr _
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hD)
          (div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hr).1))) (Nat.cast_nonneg _))
      _ = _ := by rw [FengPrimeMass.mass,Finset.mul_sum]
  have h := (transform_error_bound _ g L A X Y).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))
  have hm := mul_le_mul_of_nonneg_right (FengPrimeMass.scaled_mass_bound L U hL hU)
    (mul_nonneg (Real.exp_pos (C*U)).le hD)
  rw [abs_of_pos hL] at h
  apply h.trans
  convert hm using 1 <;> ring

/-- Actual off-g block, including u=0 and all growing g, with one Euler envelope. -/
theorem outsideBlock_euler_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ D*SupportTail.eulerMass g 0 := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let B := coprimeCap P θ C U K
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le
    (scaledCap_nonneg P θ C U K hθ hC hU hK)
  refine ⟨2*U^2*Real.exp (C*U)*B,by positivity,?_⟩
  intro L hL g hg u hu A hA
  have he := CoprimeEndpoint.euler_nonneg g hg
  have hb : ∀ r ∈ (Icc 1 ⌊Real.exp (L*u)⌋₊).filter (fun r => r.Coprime g),
      ‖coprimeScaled (⌊Real.exp (L*u)⌋₊/r) g L (u-Real.log r/L) θ P A-(0:ℂ)‖ ≤
        B*SupportTail.eulerMass g 0 := by
    intro r hr
    have hr' := (mem_filter.mp hr).1
    have hr0 : r ≠ 0 := by have := (mem_Icc.mp hr').1; omega
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp hr').1
    have hlog := (Real.log_le_iff_le_exp (by linarith : (0:ℝ)<r)).mpr
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr').2)
    have ht := normalized_log_mem r L u hr1 hL hlog
    have hv : u-Real.log r/L ∈ Set.Icc 0 U := ⟨by linarith [ht.2],by linarith [ht.1,hu.2]⟩
    rw [sub_zero,translated_cutoff L u r hL.ne' hr0]
    exact (scaled_coprime_common_bound P hP A g L _ θ C U K hL hθ hA hv hK hbound).trans
      (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hB)
  have hh := transform_uniform_error_bound g L u C (B*SupportTail.eulerMass g 0) A
    (fun r => coprimeScaled (⌊Real.exp (L*u)⌋₊/r) g L (u-Real.log r/L) θ P A)
    (fun _ => 0) hL hu.1 hA (mul_nonneg hB he) hb
  simp only [transform,mul_zero,Finset.sum_const_zero,sub_zero] at hh
  rw [outsideBlock_transform]
  change _ ≤ _ at hh
  apply hh.trans
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hC)
  have hx := mul_le_mul (mul_le_mul_of_nonneg_left hu2 (by norm_num : (0:ℝ)≤2)) hexp
    (Real.exp_pos _).le (by positivity : (0:ℝ)≤2*U^2)
  have hy := mul_le_mul_of_nonneg_right hx (mul_nonneg hB he)
  convert hy using 1 <;> ring

/-- Both reflected regions use the same constant, without a fixed-g restriction. -/
theorem outsideBlock_twoBidiscs (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ U : ℝ) (hθ : 0 < θ) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      ∀ u ∈ Set.Icc 0 U, ∀ p ∈ ElementaryGcd.twoBidiscs,
        ‖outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.1‖ ≤ D*SupportTail.eulerMass g 0 ∧
        ‖outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.2‖ ≤ D*SupportTail.eulerMass g 0 := by
  obtain ⟨D,hD,h⟩ := outsideBlock_euler_bound P hP θ (5*PRZZAsymptotic.R/4) U hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hU
  refine ⟨D,hD,?_⟩
  intro L hL g hg u hu p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact ⟨h L hL g hg u hu p.1 hs.1,h L hL g hg u hu p.2 hs.2⟩

#print axioms mark_support_bound
#print axioms transform_uniform_error_bound
#print axioms outsideBlock_euler_bound
#print axioms outsideBlock_twoBidiscs
end XiPrime8845.FengOutsideBounds
