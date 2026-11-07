import PRZZZeroIntegerReindex

/-! Exact gap completion of the ORIGINAL zero cell.  The omitted term
is the actual paired-gap tail already estimated, not a proxy error. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroCompleteCell
open Finset PRZZZeroOmittedGaps PRZZDiagonalAssembly
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def paired (F Phi : ℝ → ℂ) (M T u v : ℝ) (sigma : ℂ) (n : ℕ) : ℂ :=
  value F Phi M T u v ((n+1:ℕ):ℝ) sigma+
    value F Phi M T u v (-((n+1:ℕ):ℝ)) sigma

theorem paired_integral (F Phi : ℝ → ℂ) (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (M T u v : ℝ) (sigma : ℂ) (n : ℕ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hv : 0 < v) (hs : sigma ≠ 0) :
    paired F Phi M T u v sigma n =
      ∫ x in Set.Ioi (0:ℝ), PRZZZeroGapExchange.pair F Phi (M/v) T (u*v) sigma n x := by
  have hi (delta : ℝ) := (PRZZZeroGapExchange.row_integrable F Phi hF hPhi hsF hsPhi
    (M/v) T (u*v) sigma delta (by positivity) hT (mul_pos hu hv) hs).integrableOn (s := Set.Ioi (0:ℝ))
  unfold paired value PRZZZeroGapExchange.pair
  simp_rw [PRZZZeroGap.kernel_time]
  exact (integral_add (hi _) (hi _)).symm

theorem paired_summable (F Phi : ℝ → ℂ) (hF : Continuous F)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hcap : ∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1)
    (M T u v : ℝ) (sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hv : 0 < v)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Summable (paired F Phi M T u v sigma) := by
  obtain ⟨hi,ha⟩ := PRZZZeroGapExchange.absolute_exchange F Phi hF hPhi hcPhi hsF hsPhi hcap
    sigma (M/v) T (u*v) hs hn (by positivity) hT (mul_pos hu hv)
  apply ha.of_norm_bounded
  intro n
  rw [paired_integral F Phi hF hPhi.continuous hsF hsPhi M T u v sigma n hM hT hu hv hs]
  exact norm_integral_le_integral_norm _

theorem completed_pair (F Phi : ℝ → ℂ) (M T Q d u v eps : ℝ) (sigma : ℂ)
    (hs : Summable (paired F Phi M T u v sigma)) :
    (∑' n : ℕ, if ((n+1:ℕ):ℝ) < PRZZSourceCutoffs.deltaCutoff T M Q eps/d then
      paired F Phi M T u v sigma n else 0)+
      (∑' n : ℕ, omitted F Phi M T Q d u v eps sigma n) =
        ∑' n : ℕ, paired F Phi M T u v sigma n := by
  have hr : Summable (fun n : ℕ => if ((n+1:ℕ):ℝ) < PRZZSourceCutoffs.deltaCutoff T M Q eps/d then
      paired F Phi M T u v sigma n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    split_ifs <;> simp
  have ho : Summable (omitted F Phi M T Q d u v eps sigma) := by
    apply hs.norm.of_norm_bounded
    intro n
    unfold omitted
    split_ifs <;> simp [paired]
  rw [← hr.tsum_add ho]
  apply tsum_congr
  intro n
  exact PRZZZeroOmittedGaps.split F Phi M T Q d u v eps sigma n

def complete (N d : ℕ) (T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then coefficient a G H alpha beta d u v*
      (∑' n : ℕ, paired F Phi M T u v (alpha+beta) n) else 0

theorem native_completion (N d : ℕ) (T M Q eps : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : Continuous F) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hcap : ∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1)
    (hd : 0 < d) (hM : 0 < M) (hT : 0 < T)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    PRZZCentralArithmeticJoin.zeroCell N d (PRZZSourceCutoffs.deltaCutoff T M Q eps)
        T M a F G H Phi alpha beta+
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if admissible N d u v then coefficient a G H alpha beta d u v*
          (∑' n : ℕ, omitted F Phi M T Q d u v eps (alpha+beta) n) else 0) =
      complete N d T M a F G H Phi alpha beta := by
  rw [PRZZZeroIntegerReindex.cell_paired_sum N d _ T M a F G H Phi alpha beta hd]
  unfold complete
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  by_cases had : admissible N d u v
  · simp only [if_pos had,← mul_add]
    congr 1
    exact completed_pair F Phi M T Q d u v eps (alpha+beta)
      (paired_summable F Phi hF hPhi hcPhi hsF hsPhi hcap M T u v (alpha+beta)
        hM hT (by exact_mod_cast (Finset.mem_Icc.mp hu).1)
        (by exact_mod_cast (Finset.mem_Icc.mp hv).1) hs hn)
  · simp only [if_neg had,zero_add]

#print axioms paired_integral
#print axioms paired_summable
#print axioms completed_pair
#print axioms native_completion
end XiPrime8845.PRZZZeroCompleteCell
