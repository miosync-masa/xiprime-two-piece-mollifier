import PRZZZeroGapTime

/-! Evaluate the actual uncut zero-frequency field by the reflected
diagonal correction. The reciprocal scale and the arithmetic P^sigma
factor are retained exactly. -/
noncomputable section
open scoped ContDiff
open scoped BigOperators
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZActualZeroReflection
open PRZZCosineGapMellin PRZZZeroNormalization PRZZZeroGapTime
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def density (sigma : ℂ) (P t : ℝ) : ℂ :=
  -exp (sigma*(Real.log P:ℂ))*((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
    (PRZZDiagonalMellin.diagonal (-sigma) (t/(2*Real.pi*P))-riemannZeta (1-sigma))

theorem positive_power (sigma : ℂ) (t : ℝ) (ht : 0 < t) :
    exp (-sigma*(Real.log t:ℂ)) = (t:ℂ)^(-sigma) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast ht.ne'),← Complex.ofReal_log ht.le]
  congr 1
  ring

/-- This is the actual cosineField, not a definition by a cancelling term. -/
theorem actual_field (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T P : ℝ) (sigma : ℂ) (hT : 0 < T) (hP : 0 < P)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∫ x in Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T P sigma x) =
      ∫ t in Icc T (2*T), Phi (t/T)*density sigma P t := by
  rw [PRZZZeroOuterMellin.actual_field Phi hPhi hcPhi hsPhi T P sigma hT hP hs hn]
  let c : ℂ := -(2*exp (sigma*(Real.log P:ℂ))*(1/(2*Real.pi):ℂ))
  have he (n : ℕ) : 2*(∫ t in Icc T (2*T), PRZZZeroRowMellin.value Phi T P sigma ((n+1:ℕ):ℝ) t) =
      c*(∫ t in Icc T (2*T), weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau)) := by
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [value_normalization Phi T P t sigma n hP (hT.trans_le ht.1)]
    dsimp [c,weight]
    ring
  simp_rw [he]
  rw [tsum_mul_left,time_gap_exchange Phi hPhi.continuous T P sigma hT hP hs hn,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 < t := hT.trans_le ht.1
  have hg := PRZZCosineGapCorrection.evaluated_gap_correction sigma hs hn P t hP ht0
  have hp := positive_power sigma t ht0
  dsimp [density,c,weight]
  rw [hp]
  linear_combination (norm := ring_nf) (-exp (sigma*(Real.log P:ℂ))*Phi (t/T))*hg

theorem weighted_density (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (t : ℝ) (hu : 0 < u) (hv : 0 < v) :
    PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
      density (alpha+beta) ((u:ℝ)*v) t =
      -PRZZDiagonalAssembly.coefficient a F1 F2 (-beta) (-alpha) d u v *
        ((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*
          (PRZZDiagonalMellin.diagonal (-(alpha+beta)) (t/(2*Real.pi*((u:ℝ)*v)))-riemannZeta (1-(alpha+beta))) := by
  have he := coefficient_reflection a F1 F2 alpha beta d u v hu hv
  unfold density
  linear_combination (norm := ring_nf)
    (-((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*
      (PRZZDiagonalMellin.diagonal (-(alpha+beta)) (t/(2*Real.pi*((u:ℝ)*v)))-riemannZeta (1-(alpha+beta))))*he

theorem actual_arithmetic (N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    PRZZZeroOuterMellin.arithmeticZero N a F1 F2 Phi alpha beta T =
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          -PRZZDiagonalAssembly.coefficient a F1 F2 (-beta) (-alpha) d u v *
            (∫ t in Set.Icc T (2*T), Phi (t/T)*((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*
              (PRZZDiagonalMellin.diagonal (-(alpha+beta)) (t/(2*Real.pi*((u:ℝ)*v)))-riemannZeta (1-(alpha+beta)))) else 0 := by
  unfold PRZZZeroOuterMellin.arithmeticZero
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    have hv0 : 0 < v := (Finset.mem_Icc.mp hv).1
    have hP : (0:ℝ) < (u:ℝ)*v := by exact_mod_cast mul_pos hu0 hv0
    rw [if_pos had,if_pos had,actual_field Phi hPhi hcPhi hsPhi T _ _ hT hP hs hn,
      ← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    have hh := weighted_density a F1 F2 alpha beta d u v t hu0 hv0
    linear_combination (norm := ring_nf) Phi (t/T)*hh
  · rw [if_neg had,if_neg had]

#print axioms positive_power
#print axioms actual_field
#print axioms weighted_density
#print axioms actual_arithmetic
end XiPrime8845.PRZZActualZeroReflection
