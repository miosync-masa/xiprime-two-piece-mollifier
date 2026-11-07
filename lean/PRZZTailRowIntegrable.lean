import PRZZActualTailNative

/-! Actual infinite tail rows are integrable on the original time window.
The summable Fourier envelope is supplied by the actual smooth weight,
not by an integrability premise on a reconstructed field. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZTailRowIntegrable
open PRZZFourierExhaustion PRZZActualTailNative
set_option maxHeartbeats 8000000

theorem tail_integrable (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hs : alpha+beta ≠ 0) :
    IntegrableOn (tailTerm d J F G H Phi a T M alpha beta z) (Icc T (2*T)) := by
  obtain ⟨E,hE,he⟩ := pair_domination d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs
  let f := fun k t => pairTerm d F G H Phi a T M alpha beta z (k+J) t
  let b := fun k : ℕ => E*(1/(((k+J:ℕ):ℝ)+1)^2)
  have hb : Summable b := (summable_nat_add_iff J).mpr (PRZZWeightTail.square_summable.mul_left E)
  have hn (t : ℝ) (ht : t ∈ Icc T (2*T)) : Summable (fun k => ‖f k t‖) := by
    exact hb.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => (he (k+J)).2 t ht)
  have hm : AEStronglyMeasurable (fun t => ∑' k, f k t) (volume.restrict (Icc T (2*T))) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => Finset.aestronglyMeasurable_sum (range n) (fun k hk => (he (k+J)).1))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Finset.sum_apply] using (Summable.of_norm (hn t ht)).hasSum.tendsto_sum_nat
  have hi : IntegrableOn (fun t => ∑' k, f k t) (Icc T (2*T)) := by
    have hc : Integrable (fun _ : ℝ => ∑' k, b k) (volume.restrict (Icc T (2*T))) :=
      continuous_const.integrableOn_Icc
    apply hc.mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (norm_tsum_le_tsum_norm (hn t ht)).trans
      ((hn t ht).tsum_le_tsum (fun k => (he (k+J)).2 t ht) hb)
  have hep (k : ℕ) (t : ℝ) : f k t =
      (Phi (t/T)*coefficient d G H a alpha beta z)*
        PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
          z alpha beta (alpha+beta) J k t := by
    simp [f,pairTerm,PRZZFrozenTail.pair,Nat.cast_add,add_comm,add_assoc,mul_assoc]
  have hh (t : ℝ) : (∑' k, f k t) = tailTerm d J F G H Phi a T M alpha beta z t := by
    simp only [hep,tsum_mul_left,tailTerm,mul_assoc]
  exact hi.congr (Eventually.of_forall hh)

theorem native_integrable (L d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hs : alpha+beta ≠ 0) :
    IntegrableOn (fun t => Phi (t/T)*PRZZNativeComponents.row .tail L J F G H M z alpha beta a d t)
      (Icc T (2*T)) := by
  by_cases hsmall : |(z.2.1:ℝ)| ≤ M*z.1.1/4
  · have he : (fun t => Phi (t/T)*PRZZNativeComponents.row .tail L J F G H M z alpha beta a d t) =
        tailTerm d J F G H Phi a T M alpha beta z := by
      funext t
      simp only [tailTerm,coefficient,PRZZNativeComponents.row,if_pos hsmall]
    rw [he]
    exact tail_integrable d J F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs
  · simp only [PRZZNativeComponents.row,if_neg hsmall,mul_zero]
    exact integrableOn_zero

#print axioms tail_integrable
#print axioms native_integrable
end XiPrime8845.PRZZTailRowIntegrable
