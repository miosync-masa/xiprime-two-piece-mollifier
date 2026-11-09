import PRZZWindowNativeTail
import PRZZCappedWindowTime

/-! Lossless native-gap and dyadic reindex for arbitrary coefficients.
The source mask endpoints, signed gaps and native membership are unchanged. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex
namespace XiPrime8845.PRZZCappedNativeTail
open PRZZWindowGrids PRZZCappedWindowMass PRZZResolvedTailMass PRZZWindowNativeTail
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def nativeMass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ p ∈ PRZZPrefactorMass.pairs N d j l,
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2),
          if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*p.1/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
            ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(-delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
                (PRZZCentralTail.residue (p,(-delta,1))/p.2) p‖ else 0

def flatMass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*u/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
            ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B ((u,v),(-delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
                (PRZZCentralTail.residue ((u,v),(-delta,1))/v) (u,v)‖ else 0
      else 0

theorem flat_eq (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    flatMass F G W c L N dual T Q V b eD eH t A B =
      nativeMass F G W c L N dual T Q V b eD eH t A B := by
  unfold flatMass nativeMass
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro d hd
  exact pair_partition (E := ℝ) N d (fun p =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2),
      if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*p.1/4 ∧
        |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
        ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(-delta,1)) *
          PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
            (PRZZCentralTail.residue (p,(-delta,1))/p.2) p‖ else 0)

theorem native_eq (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    nativeMass F G W c L N dual T Q V b eD eH t A B =
      mass F G W c L N dual T Q V b eD eH t A B := by
  unfold nativeMass mass
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro l hl
  have hd1 := (Finset.mem_Icc.mp hd).1
  have he (p : ℕ × ℕ) := gap_reindex (PRZZNativeFamily.gaps L N (d*p.1) (d*p.2))
    (fun delta => ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(delta,1)) *
      PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B delta 1
        (PRZZCentralTail.residue (p,(delta,1))/p.2) p‖)
    T ((2:ℝ)^k) Q b eD d p.1 hT (by positivity) (mem_filter.mp hk).2 hQ hQT hd1
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl; intro delta hg
  unfold term nativePairs
  rw [sum_filter]
  by_cases hs : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d
  · simp only [if_pos hs]
    apply sum_congr rfl; intro p hp
    simp only [hs,and_true]
  · simp only [hs,and_false,if_false,sum_const_zero]

theorem native_wide_zero (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (hwide : 2*T < Q) :
    nativeMass F G W c L N dual T Q V b eD eH t A B = 0 := by
  unfold nativeMass
  apply sum_eq_zero; intro k hk
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro j hj
  apply sum_eq_zero; intro l hl
  apply sum_eq_zero; intro p hp
  have hpair := mem_filter.mp hp
  have hdu : (d:ℝ)*p.1 ≤ T := (by exact_mod_cast hpair.2.2.1 : (d:ℝ)*p.1 ≤ N).trans hNT
  have hz : PRZZMellinSeparation.scaledCutoff F Q ((d:ℝ)*p.1) = 0 := by
    by_contra hz
    have hh := (PRZZCappedWindowTime.scaled_support F Q hQ hs hz).1
    linarith
  apply sum_eq_zero; intro delta hg
  split_ifs <;> simp [PRZZCappedTailMass.coeff,PRZZUnfrozenPoisson.arithmetic,hz]

/-- Equality for all positive cutoff scales: the out-of-range scale is
supplied as a zero arithmetic row, not assumed absent. -/
theorem native_eq_all (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    nativeMass F G W c L N dual T Q V b eD eH t A B =
      mass F G W c L N dual T Q V b eD eH t A B := by
  by_cases hQT : Q ≤ 2*T
  · exact native_eq F G W c L N dual T Q V b eD eH t A B hT hQ.le hQT
  · rw [native_wide_zero F G W c L N dual T Q V b eD eH t A B hNT hQ hs (lt_of_not_ge hQT),
      PRZZCappedWindowTime.wide_zero F G W c L N dual T Q V b eD eH t A B hNT hQ hs (lt_of_not_ge hQT)]

#print axioms flat_eq
#print axioms native_eq
#print axioms native_wide_zero
#print axioms native_eq_all
end XiPrime8845.PRZZCappedNativeTail
