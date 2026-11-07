import PRZZCentralTail
import PRZZInverseProfile

/-! Keep the intermediate frequency band when enlarging a cutoff.
Aggregation retains the row-dependent inverse-profile mass v/M * B.
The common height bound for that mass is not assumed to be supplied here. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators ContDiff
namespace XiPrime8845.PRZZExpandedCutoff
open PRZZFrozenTail PRZZCentralTail PRZZAStar
set_option maxHeartbeats 3000000

def band (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t : ℝ) (H G : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (G-H), pair F M q residue z alpha beta sigma H j t

theorem central_extend (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t : ℝ) (H G : ℕ) (hHG : H ≤ G) :
    central F M q residue z alpha beta sigma t G =
      central F M q residue z alpha beta sigma t H +
        band F M q residue z alpha beta sigma t H G := by
  unfold central band
  rw [show G = H+(G-H) from (Nat.add_sub_of_le hHG).symm, Finset.sum_range_add]
  simp only [Nat.add_sub_cancel_left, pair, Nat.cast_add, Nat.cast_zero, zero_add]
  ring

theorem poisson_expand (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M q residue t : ℝ) (z : Index) (alpha beta sigma : ℂ) (H G : ℕ)
    (hHG : H ≤ G) (hM : 0 < M) (hq : 0 < q) (ht : 0 < t)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hs : sigma ≠ 0) :
    (∑' j : ℤ, frozen F M z alpha beta sigma t (residue+q*j)) =
      central F M q residue z alpha beta sigma t H +
        band F M q residue z alpha beta sigma t H G +
          ∑' j : ℕ, pair F M q residue z alpha beta sigma G j t := by
  rw [poisson_split F hF hsF M q residue t z alpha beta sigma G hM hq ht hn hm hs,
    central_extend F M q residue z alpha beta sigma t H G hHG]

/-- Row-specific enlarged cutoffs, with all original prefactors retained. -/
theorem rows_extend (N d : ℕ) (D H M t : ℝ) (a : ℕ → ℂ)
    (F1 F2 F : ℝ → ℂ) (alpha beta sigma : ℂ) (J G : Index → ℕ)
    (hJG : ∀ z ∈ indices N d D H, J z ≤ G z) :
    (∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      central F M z.1.2 (residue z) z alpha beta sigma t (G z)) =
    (∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      central F M z.1.2 (residue z) z alpha beta sigma t (J z)) +
    ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      band F M z.1.2 (residue z) z alpha beta sigma t (J z) (G z) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [central_extend F M z.1.2 (residue z) z alpha beta sigma t (J z) (G z) (hJG z hz), mul_add]

/-- Original smooth progression sums, minus the old central block and
the intermediate band, equal the tails at the row-specific new cutoff. -/
theorem rows_remainder (N d : ℕ) (D H M t : ℝ) (a : ℕ → ℂ)
    (F1 F2 F : ℝ → ℂ) (alpha beta sigma : ℂ) (J G : Index → ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (ht : 0 < t) (hs : sigma ≠ 0)
    (hJG : ∀ z ∈ indices N d D H, J z ≤ G z) :
    (∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      ((∑' j : ℤ, frozen F M z alpha beta sigma t (residue z+(z.1.2:ℝ)*j)) -
        central F M z.1.2 (residue z) z alpha beta sigma t (J z) -
        band F M z.1.2 (residue z) z alpha beta sigma t (J z) (G z))) =
    ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      ∑' j : ℕ, pair F M z.1.2 (residue z) z alpha beta sigma (G z) j t := by
  apply Finset.sum_congr rfl
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hn1 : 0 < z.1.1 := by have := (Finset.mem_Icc.mp hn.1).1; omega
  have hn2 : 0 < z.1.2 := by have := (Finset.mem_Icc.mp hn.2).1; omega
  rw [poisson_expand F hF hsF M z.1.2 (residue z) t z alpha beta sigma
    (J z) (G z) (hJG z hz) hM (by exact_mod_cast hn2) ht hn1 hn2 hs]
  ring

/-- A dominated finite arithmetic sum under a time integral. The mass is
weighted row by row, not replaced by a cardinality or an unproved constant.
Use B for the derivative/frequency budget and v/M for its Jacobian cost. -/
theorem mass_time {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (v M B : ι → ℝ) (E : ι → ℝ → ℂ) (w : ℝ → ℂ)
    (hw : Continuous w) (A Z : ℝ)
    (hE : ∀ t ∈ Icc A Z, ∀ i ∈ s, ‖E i t‖ ≤ (v i/M i)*B i) :
    ‖∫ t in Icc A Z, w t * ∑ i ∈ s, c i*E i t‖ ≤
      (∑ i ∈ s, ‖c i‖*(v i/M i)*B i) * ∫ t in Icc A Z, ‖w t‖ := by
  let C := ∑ i ∈ s, ‖c i‖*(v i/M i)*B i
  have hc : Continuous (fun t => C*‖w t‖) := continuous_const.mul hw.norm
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    hc.integrableOn_Icc ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans
    have hh : (∑ i ∈ s, ‖c i*E i t‖) ≤ C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hE t ht i hi) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Apply the retained tail masses to the actual full-minus-central-minus-band
integral. The per-row tail bounds remain explicit inputs, so this does not
assert that the source's full height budget has already been supplied. -/
theorem original_remainder_bound (N d : ℕ) (D H M T : ℝ) (a : ℕ → ℂ)
    (F1 F2 F w : ℝ → ℂ) (alpha beta sigma : ℂ) (J G : Index → ℕ)
    (B : Index → ℝ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hw : Continuous w)
    (hM : 0 < M) (hT : 0 < T) (hs : sigma ≠ 0)
    (hJG : ∀ z ∈ indices N d D H, J z ≤ G z)
    (hB : ∀ t ∈ Icc T (2*T), ∀ z ∈ indices N d D H,
      ‖∑' j : ℕ, pair F M z.1.2 (residue z) z alpha beta sigma (G z) j t‖ ≤
        ((z.1.2:ℝ)/M)*B z) :
    ‖∫ t in Icc T (2*T), w t *
      ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        ((∑' j : ℤ, frozen F M z alpha beta sigma t (residue z+(z.1.2:ℝ)*j)) -
          central F M z.1.2 (residue z) z alpha beta sigma t (J z) -
          band F M z.1.2 (residue z) z alpha beta sigma t (J z) (G z))‖ ≤
      (∑ z ∈ indices N d D H, ‖prefactor a F1 F2 d alpha beta z‖ *
        ((z.1.2:ℝ)/M)*B z) * ∫ t in Icc T (2*T), ‖w t‖ := by
  have he : (∫ t in Icc T (2*T), w t *
      ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        ((∑' j : ℤ, frozen F M z alpha beta sigma t (residue z+(z.1.2:ℝ)*j)) -
          central F M z.1.2 (residue z) z alpha beta sigma t (J z) -
          band F M z.1.2 (residue z) z alpha beta sigma t (J z) (G z))) =
      ∫ t in Icc T (2*T), w t * ∑ z ∈ indices N d D H,
        prefactor a F1 F2 d alpha beta z *
          ∑' j : ℕ, pair F M z.1.2 (residue z) z alpha beta sigma (G z) j t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [rows_remainder N d D H M t a F1 F2 F alpha beta sigma J G
      hF hsF hM (hT.trans_le ht.1) hs hJG]
  rw [he]
  exact mass_time _ _ (fun z => (z.1.2:ℝ)) (fun _ => M) B _ w hw T (2*T) hB

#print axioms original_remainder_bound
#print axioms central_extend
#print axioms poisson_expand
#print axioms rows_extend
#print axioms rows_remainder
#print axioms mass_time
end XiPrime8845.PRZZExpandedCutoff
