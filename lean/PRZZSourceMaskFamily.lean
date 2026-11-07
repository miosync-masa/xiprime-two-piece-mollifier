import PRZZAllPoissonRows
import PRZZDualDiscardedIBP

/-! Exact source-mask classification on the original finite AFE indices.
The discarded endpoint is closed; its complementary retained endpoint is
strict. Both actual cutoff values survive. No growing label count is paid.
This does not identify the phase-free time-zero coefficient with its
oscillatory reconstruction, nor supply uniform Gamma derivative bounds. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set MeasureTheory
namespace XiPrime8845.PRZZSourceMaskFamily
open PRZZAFEIndices PRZZWRowReindex PRZZWRowLimit
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def discarded (T Q eps : ℝ) (s : ℕ) (z : Label) : Prop :=
  PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps ≤
    (z.1:ℝ)*|(z.2.1:ℝ)|

theorem raw_gap (i : Index) :
    |(i.1.2:ℝ)*i.2.2-(i.1.1:ℝ)*i.2.1| =
      ((label i).1:ℝ)*|((label i).2.1:ℝ)| := by
  have h := congrArg (fun z : ℤ => (z:ℝ)) (gap_eq i)
  push_cast at h
  rw [abs_sub_comm,h,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]

/-- The support selector disappears only after multiplying the actual
left cutoff value. In particular it is not asserted to be identically one. -/
theorem mask_values (L : ℕ) (P : ℝ → ℝ) (G H : ℝ → ℂ)
    (T Q eps : ℝ) (i : Index) (hm : 0 < i.1.1) (hk : 0 < i.1.2) :
    (G i.2.1*H i.2.2)*PRZZDiscardedOuter.sourceMask P G (L+2)
      T 1 Q 1 eps i.2.1 i.2.2 (i.1.1-1,i.1.2-1) =
    ∑ s ∈ range (L+2), if discarded T Q eps s (label i) then
      PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
        (G i.2.1*H i.2.2) else 0 := by
  have hm' : i.1.1-1+1 = i.1.1 := by omega
  have hk' : i.1.2-1+1 = i.1.2 := by omega
  have hmR : ((i.1.1-1:ℕ):ℝ)+1 = (i.1.1:ℝ) := by exact_mod_cast hm'
  have hkR : ((i.1.2-1:ℕ):ℝ)+1 = (i.1.2:ℝ) := by exact_mod_cast hk'
  by_cases hg : G i.2.1 = 0
  · simp [PRZZDiscardedOuter.sourceMask,hg]
  · simp only [PRZZDiscardedOuter.sourceMask,one_mul,if_neg hg,
      PRZZDiscardedPartition.mask,hmR,hkR,mul_one,div_one,Finset.mul_sum]
    apply sum_congr rfl; intro s hs
    rw [raw_gap]
    simp only [discarded]
    split_ifs <;> simp_all [mul_comm,mul_assoc] <;> linarith

/-- Exact same original finite four-index sum, not an enlarged grid. -/
def masked (L N : ℕ) (P : ℝ → ℝ) (G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ indices L N,
    ((G i.2.1*H i.2.2)*PRZZDiscardedOuter.sourceMask P G (L+2)
      T 1 Q 1 eps i.2.1 i.2.2 (i.1.1-1,i.1.2-1))*
      PRZZL1Finite.term a a alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
        t i.1.1 i.1.2 i.2.1 i.2.2

theorem masked_selected (L N : ℕ) (P : ℝ → ℝ) (G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (hT : 0 < T) (hQ : 0 < Q) (alpha beta : ℂ) (t : ℝ) :
    masked L N P G H a T Q eps alpha beta t =
      PRZZAllOffDiagonalRows.selected L N (fun x => (P x:ℂ)) G H a
        (discarded T Q eps) alpha beta t := by
  have hcut (s : ℕ) : 0 < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hm : masked L N P G H a T Q eps alpha beta t =
      ∑ s ∈ range (L+2), ∑ i ∈ indices L N,
        if discarded T Q eps s (label i) then
          PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
            PRZZL1Finite.term (leftCoefficient a G) (rightCoefficient a H)
              alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
                t i.1.1 i.1.2 i.2.1 i.2.2 else 0 := by
    unfold masked
    rw [sum_comm]
    apply sum_congr rfl; intro i hi
    obtain ⟨hmk,hnr⟩ := mem_product.mp hi
    obtain ⟨hmi,hki⟩ := mem_product.mp hmk
    rw [mask_values L P G H T Q eps i (mem_Icc.mp hmi).1 (mem_Icc.mp hki).1,sum_mul]
    apply sum_congr rfl; intro s hs
    rw [term_cutoffs]
    split_ifs <;> ring
  rw [hm]
  unfold PRZZAllOffDiagonalRows.selected
  apply sum_congr rfl; intro s hs
  rw [grouped]
  apply sum_congr rfl; intro z hz
  have he : (∑ i ∈ fibre L N z,
      PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
        PRZZL1Finite.term (leftCoefficient a G) (rightCoefficient a H)
          alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
            t i.1.1 i.1.2 i.2.1 i.2.2) =
      literalRows L N (fun x => (P x:ℂ)) s z a G H alpha beta t := by
    rw [PRZZExplicitDomain.fibre_explicit]
    exact row_reindex L N s z _ G H a alpha beta t
  by_cases hd : discarded T Q eps s z
  · have hne : z.2.1 ≠ 0 := by
      intro hzero
      have hh := hd
      simp only [discarded,hzero,Int.cast_zero,abs_zero,mul_zero] at hh
      linarith [hcut s]
    simp only [if_pos (And.intro hne hd)]
    rw [← he]
    apply sum_congr rfl; intro i hi
    rw [(mem_filter.mp hi).2,if_pos hd]
  · simp only [show ¬(z.2.1 ≠ 0 ∧ discarded T Q eps s z) from fun h => hd h.2,if_false]
    apply sum_eq_zero; intro i hi
    rw [(mem_filter.mp hi).2,if_neg hd]

/-- Any selected source region is a literal subfamily of the very same
resolved Poisson family. The original small-gap test still chooses the
full central+tail-boundary+freeze formula versus the unaltered row. -/
def selectedFamily (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ labels L N, if z.2.1 ≠ 0 ∧ R s z then
    ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, if pairMatches z n r then
      PRZZAllPoissonRows.resolved L J (profile F) G H ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-z.2.1,1)) alpha beta a (Nat.gcd n r) t
    else 0 else 0

theorem selected_resolved (L J N : ℕ) (F G H : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hlo : ∀ y ≤ (1/2:ℝ), F y = 1)
    (hhi : ∀ y, 1 ≤ y → F y = 0) (a : ℕ → ℂ) (R : ℕ → Label → Prop)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    PRZZAllOffDiagonalRows.selected L N F G H a R alpha beta t =
      selectedFamily L J N F G H a R alpha beta t := by
  have hf := profile_regular F hF hlo hhi
  unfold PRZZAllOffDiagonalRows.selected selectedFamily literalRows
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro z hz
  split_ifs with hsel
  · apply sum_congr rfl; intro n hn
    apply sum_congr rfl; intro r hr
    split_ifs with hp
    · have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hr0 : 0 < r := (mem_Icc.mp hr).1
      have hd : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn0
      exact PRZZAllPoissonRows.row_resolved L J (profile F) G H hf.1 hf.2.2 _ _
        alpha beta a _ t (by positivity) ht hd
        (Nat.div_pos (Nat.gcd_le_left r hn0) hd)
        (Nat.div_pos (Nat.gcd_le_right n hr0) hd) (Nat.coprime_div_gcd_div_gcd hd) hab
    · rfl
  · rfl

theorem family_partition (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F G H a alpha beta t =
      selectedFamily L J N F G H a R alpha beta t+
      selectedFamily L J N F G H a (fun s z => ¬R s z) alpha beta t := by
  unfold PRZZAllPoissonRows.family selectedFamily
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro z hz
  by_cases hg : z.2.1 ≠ 0 <;> by_cases hr : R s z <;> simp [hg,hr]

/-- Substitute the actual source mask into the corresponding original
family, including its sharp cutoffs, spatial partition and all correction
terms. There is no frozen-phase coefficient premise in this identity. -/
theorem masked_family (L J N : ℕ) (P : ℝ → ℝ) (G H : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0)
    (a : ℕ → ℂ) (T Q eps : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    masked L N P G H a T Q eps alpha beta t =
      selectedFamily L J N (fun x => (P x:ℂ)) G H a
        (discarded T Q eps) alpha beta t := by
  rw [masked_selected L N P G H a T Q eps hT hQ]
  exact selected_resolved L J N _ G H hP
    (by intro y hy; simp [hlo y hy]) (by intro y hy; simp [hhi y hy])
    a _ alpha beta hab t ht

/-- The genuine dual multiplier remains inside the time integral. Both
kernel shifts are reflected and the original discarded endpoint is kept. -/
theorem dual_time (L J N : ℕ) (P : ℝ → ℝ) (G H phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0)
    (a : ℕ → ℂ) (T Q eps : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) :
    (∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      masked L N P G H a T Q eps (-beta) (-alpha) t) =
    ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      selectedFamily L J N (fun x => (P x:ℂ)) G H a
        (discarded T Q eps) (-beta) (-alpha) t := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [masked_family L J N P G H hP hlo hhi a T Q eps hT hQ (-beta) (-alpha)
    (by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hab)
    t (hT.trans_le ht.1)]

#print axioms masked_family
#print axioms dual_time
#print axioms raw_gap
#print axioms mask_values
#print axioms masked_selected
#print axioms selected_resolved
#print axioms family_partition
end XiPrime8845.PRZZSourceMaskFamily
