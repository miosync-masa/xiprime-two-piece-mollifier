import PRZZCentralArithmeticJoin
import PRZZRejectedExhaustion

/-! Exact interface from the literal full-minus-prefix tail to the native
row tail. The native gap and small-ratio masks are retained. Rejected
rows are displayed rather than silently charged to a selected-row bound. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZActualTailNative
open PRZZFourierExhaustion PRZZNativeCentralLiteral PRZZCentralArithmeticJoin
open PRZZLiteralFourierLimit
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def tailTerm (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ) (T M : ℝ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (t : ℝ) : ℂ :=
  Phi (t/T)*(coefficient d G H a alpha beta z *
    ∑' k, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
      z alpha beta (alpha+beta) J k t)

theorem row_tail_time (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hs : alpha+beta ≠ 0) :
    (∑' k, integratedPair d F G H Phi a T M alpha beta z (k+J)) =
      ∫ t in Icc T (2*T), tailTerm d J F G H Phi a T M alpha beta z t := by
  have he (k : ℕ) (t : ℝ) :
      pairTerm d F G H Phi a T M alpha beta z (k+J) t =
        (Phi (t/T)*coefficient d G H a alpha beta z)*
          PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
            z alpha beta (alpha+beta) J k t := by
    simp [pairTerm,PRZZFrozenTail.pair,Nat.cast_add,add_comm,add_assoc,mul_assoc]
  have hh := PRZZFrozenTail.time_swap F hF hsF T M 1
    (PRZZCentralTail.residue z/z.1.2) z alpha beta (alpha+beta) J
    hT hM (by norm_num) hu hv hs
    (fun y => Phi y*coefficient d G H a alpha beta z) (hPhi.mul continuous_const)
  simp only [integratedPair,he]
  rw [hh]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [tailTerm,tsum_mul_left,mul_assoc]

theorem cell_tail_series (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    cellTail N d J D T M a F G H Phi alpha beta =
      ∑ z ∈ PRZZAStar.indices N d D 2,
        ∑' k, integratedPair d F G H Phi a T M alpha beta z (k+J) := by
  rw [cellTail,cellPrefix_time N d J D T M a F G H Phi alpha beta
    hF hPhi hsF hsPhi hT hM hs]
  unfold PRZZLiteralFourierLimit.cellFull
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro z hz
  have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  have hu := (mem_Icc.mp hp.1).1
  have hv := (mem_Icc.mp hp.2).1
  have ht := central_time_eq d J F G H Phi a hF hPhi hsF hsPhi T M alpha beta z hT hM hu hv hs
  have hsum := (pair_integrable_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs).2
  have hh := hsum.sum_add_tsum_nat_add J
  unfold allModes
  rw [ht]
  linear_combination -hh

theorem cell_tail_time (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    cellTail N d J D T M a F G H Phi alpha beta =
      ∑ z ∈ PRZZAStar.indices N d D 2,
        ∫ t in Icc T (2*T), tailTerm d J F G H Phi a T M alpha beta z t := by
  rw [cell_tail_series N d J D T M a F G H Phi alpha beta hF hPhi hsF hsPhi hT hM hs]
  apply sum_congr rfl
  intro z hz
  have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  exact row_tail_time d J F G H Phi a hF hPhi hsF T M alpha beta z hT hM
    (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs

def rejectedTail (L N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then 0 else
    ∫ t in Icc T (2*T), tailTerm d J F G H Phi a T M alpha beta z t

theorem native_split (L N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    cellTail N d J D T M a F G H Phi alpha beta =
      (∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then
        ∫ t in Icc T (2*T), Phi (t/T)*PRZZNativeComponents.row .tail L J
          F G H M z alpha beta a d t else 0)+
      rejectedTail L N d J D T M a F G H Phi alpha beta := by
  classical
  rw [cell_tail_time N d J D T M a F G H Phi alpha beta hF hPhi hsF hsPhi hT hM hs]
  unfold rejectedTail
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro z hz
  by_cases hg : good L N d M z
  · simp only [if_pos hg,add_zero]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [tailTerm,PRZZNativeComponents.row,if_pos hg.2,coefficient]
  · simp only [if_neg hg,zero_add]

#print axioms row_tail_time
#print axioms cell_tail_series
#print axioms cell_tail_time
#print axioms native_split

/-- The actual native row mass, with no replacement of the valued
arithmetic cutoffs. The rejected rectangle remains a separate charge. -/
theorem native_bound (L N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    ‖cellTail N d J D T M a F G H Phi alpha beta‖ ≤
      (∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then
        ∫ t in Icc T (2*T), ‖Phi (t/T)*PRZZNativeComponents.row .tail L J
          F G H M z alpha beta a d t‖ else 0)+
      ‖rejectedTail L N d J D T M a F G H Phi alpha beta‖ := by
  rw [native_split L N d J D T M a F G H Phi alpha beta hF hPhi hsF hsPhi hT hM hs]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro z hz
  split_ifs
  · exact norm_integral_le_integral_norm _
  · simp

#print axioms native_bound

/-- Native exhaustion is independent of the already fixed spatial
window. Its threshold precedes J and all analytic parameters. The native
budgets are uniform in this exhaustion index, so no height loss is spent
on choosing it after T. -/
theorem rejected_tail_eventually (N d : ℕ) (G : ℝ → ℂ) (Q T M eps : ℝ)
    (hQ : 0 < Q) (hT : 0 < T) (hM : 0 ≤ M) (hd : 0 < d)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ R : ℕ in atTop, ∀ (J : ℕ) (F H Phi : ℝ → ℂ) (a : ℕ → ℂ)
      (alpha beta : ℂ),
      rejectedTail R N d J (PRZZSourceCutoffs.deltaCutoff T M Q eps) T M a
        F (PRZZMellinSeparation.scaledCutoff G Q) H Phi alpha beta = 0 := by
  filter_upwards [PRZZRejectedExhaustion.rectangle_eventually N d
    (PRZZSourceCutoffs.deltaCutoff T M Q eps) hd] with R hR
  intro J F H Phi a alpha beta
  unfold rejectedTail
  apply sum_eq_zero
  intro z hz
  by_cases hg : PRZZMellinSeparation.scaledCutoff G Q ((d:ℝ)*z.1.1) = 0
  · split_ifs <;> simp [tailTerm,coefficient,PRZZUnfrozenPoisson.arithmetic,hg]
  · have hdel := (mem_filter.mp (mem_product.mp (mem_product.mp hz).2).1).2.2
    have hsmall := PRZZRejectedExhaustion.source_small_gap G Q T M eps d z.1.1 z.2.1
      hQ hT hM hd hsG hg hheight hdel
    exact if_pos ⟨hR z hz,hsmall⟩

#print axioms rejected_tail_eventually
end XiPrime8845.PRZZActualTailNative
