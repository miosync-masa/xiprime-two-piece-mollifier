import PRZZAllPoissonAFE

/-! Actual finite spatial/gap zero exhaustion to the reflected correction.
Finite gcd sums are exchanged with time using supplied row continuity.
No Gamma-weighted exhaustion is inferred from an unweighted limit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Finset Filter Topology
namespace XiPrime8845.PRZZZeroExhaustionCross
open PRZZActualZeroReflection PRZZZeroOuterMellin PRZZZeroCross
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem density_continuous (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (T : ℝ) (hT : 0 < T) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (density sigma ((u:ℝ)*v)) (Icc T (2*T)) := by
  have hr : -1 ≤ (-sigma).re := by
    have h := (abs_le.mp ((abs_re_le_norm sigma).trans hn)).2
    simp only [neg_re]; linarith
  have hd := PRZZDiagonalAssembly.diagonal_time_continuous (-sigma) (neg_ne_zero.mpr hs)
    hr T hT u v hu hv
  have hp := PRZZZeroCoupled.power_continuous (-sigma) T hT
  have hd' : ContinuousOn (fun t : ℝ => PRZZDiagonalMellin.diagonal (-sigma)
      (t/(2*Real.pi*((u:ℝ)*v)))) (Icc T (2*T)) := by
    simpa only [mul_assoc] using hd
  unfold density
  exact (continuousOn_const.mul hp).mul
    (hd'.sub continuousOn_const)

theorem actual_zero_time (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    arithmeticZero N a (fun _ => 1) (fun _ => 1) Phi alpha beta T =
      ∫ t in Icc T (2*T), Phi (t/T)*zero N a alpha beta t := by
  let f := fun d u v : ℕ => fun t : ℝ => Phi (t/T)*
    (if PRZZDiagonalAssembly.admissible N d u v then
      PRZZDiagonalAssembly.coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v*
        density (alpha+beta) ((u:ℝ)*v) t else 0)
  have hi (d : ℕ) (hd : d ∈ Finset.Icc 1 N) (u : ℕ) (hu : u ∈ Finset.Icc 1 N)
      (v : ℕ) (hv : v ∈ Finset.Icc 1 N) : IntegrableOn (f d u v) (Icc T (2*T)) := by
    by_cases had : PRZZDiagonalAssembly.admissible N d u v
    · simp only [f,if_pos had]
      exact ((hPhi.continuous.comp (continuous_id.div_const T)).continuousOn.mul
        ((density_continuous (alpha+beta) hs hn T hT u v (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1).const_mul _)).integrableOn_compact isCompact_Icc
    · simp only [f,if_neg had,mul_zero]
      exact integrableOn_zero
  have hu (d : ℕ) (hd : d ∈ Finset.Icc 1 N) (u : ℕ) (hu : u ∈ Finset.Icc 1 N) :=
    integrable_finsetSum (Finset.Icc 1 N) (hi d hd u hu)
  have hd (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :=
    integrable_finsetSum (Finset.Icc 1 N) (hu d hd)
  have he : (∫ t in Icc T (2*T), Phi (t/T)*zero N a alpha beta t) =
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        ∫ t in Icc T (2*T), f d u v t := by
    unfold zero
    simp only [Finset.mul_sum]
    rw [integral_finsetSum (Finset.Icc 1 N) hd]
    apply sum_congr rfl
    intro d hdd
    rw [integral_finsetSum (Finset.Icc 1 N) (hu d hdd)]
    apply sum_congr rfl
    intro u huu
    exact integral_finsetSum (Finset.Icc 1 N) (hi d hdd u huu)
  rw [he]
  unfold arithmeticZero
  apply sum_congr rfl
  intro d hdd
  apply sum_congr rfl
  intro u huu
  apply sum_congr rfl
  intro v hvv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had,f]
    rw [PRZZActualZeroReflection.actual_field Phi hPhi hcPhi hsPhi T _ _ hT
      (by have := (Finset.mem_Icc.mp huu).1; have := (Finset.mem_Icc.mp hvv).1; positivity) hs hn,
      ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [if_pos had]
    ring
  · simp only [if_neg had,f,mul_zero,integral_zero]

theorem actual_zero_correction (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    arithmeticZero N a (fun _ => 1) (fun _ => 1) Phi alpha beta T =
      -(∫ t in Icc T (2*T), Phi (t/T)*((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*
        PRZZCoupledAFE.correction N a (-beta) (-alpha) t) := by
  rw [actual_zero_time N a Phi alpha beta T hPhi hcPhi hsPhi hT hs hn,← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [zero_correction N a alpha beta hs hn t (hT.trans_le ht.1)]
  ring

theorem exhaustion_correction (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => finiteArithmeticZero S L N a (fun _ => 1) (fun _ => 1) Phi alpha beta T)
      atTop (𝓝 (-(∫ t in Icc T (2*T), Phi (t/T)*((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*
        PRZZCoupledAFE.correction N a (-beta) (-alpha) t))) := by
  rw [← actual_zero_correction N a Phi alpha beta T hPhi hcPhi hsPhi hT hs hn]
  exact arithmetic_exhaustion S hS hm hlo hhi hleft hright N a _ _ Phi alpha beta T
    hPhi hcPhi hsPhi hT hs hn

#print axioms density_continuous
#print axioms actual_zero_time
#print axioms actual_zero_correction
#print axioms exhaustion_correction
end XiPrime8845.PRZZZeroExhaustionCross
