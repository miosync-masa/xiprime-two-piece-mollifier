import PRZZAllPoissonRows

/-! Lossless original-label to original-pair/gap reindexing. The gap set
is the image of the actual matching labels, not an enlarged rectangle or
the progression gaps of one pair. All original filters can remain in f. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZNativeFamily
open PRZZAFEIndices PRZZWRowReindex
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

def pairLabel (n r : ℕ) (gap : ℤ) : Label :=
  (Nat.gcd n r,gap,Nat.log 2 (n/Nat.gcd n r),Nat.log 2 (r/Nat.gcd n r))

def gaps (L N n r : ℕ) : Finset ℤ :=
  ((labels L N).filter (fun z => pairMatches z n r)).image (fun z => z.2.1)

theorem matching_label (z : Label) (n r : ℕ) (h : pairMatches z n r) :
    pairLabel n r z.2.1 = z := by
  rcases z with ⟨d,delta,j,l⟩
  rcases h with ⟨hd,hj,hl⟩
  dsimp only at hd hj hl
  unfold pairLabel
  rw [hj,hl,hd]

theorem mem_gaps (L N n r : ℕ) (delta : ℤ) :
    delta ∈ gaps L N n r ↔ pairLabel n r delta ∈ labels L N := by
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := mem_image.mp h
    obtain ⟨hz,hp⟩ := mem_filter.mp hz
    rw [← he,matching_label z n r hp]
    exact hz
  · intro h
    apply mem_image.mpr
    exact ⟨pairLabel n r delta,mem_filter.mpr ⟨h,by simp [pairMatches,pairLabel]⟩,rfl⟩

/-- For a fixed original pair, the matching label is determined by its
signed gap. Thus there is no gcd/dyadic-label multiplicity to estimate. -/
theorem label_sum {E : Type*} [AddCommMonoid E]
    (L N n r : ℕ) (f : ℤ → E) :
    (∑ z ∈ labels L N, if pairMatches z n r then f z.2.1 else 0) =
      ∑ delta ∈ gaps L N n r, f delta := by
  rw [← sum_filter]
  apply sum_bij (fun z _ => z.2.1)
  · intro z hz
    exact mem_image_of_mem _ hz
  · intro z hz w hw he
    have hz' := matching_label z n r (mem_filter.mp hz).2
    have hw' := matching_label w n r (mem_filter.mp hw).2
    rw [← hz',← hw',he]
  · intro delta hd
    obtain ⟨z,hz,he⟩ := mem_image.mp hd
    exact ⟨z,hz,he⟩
  · intro z hz
    rfl

theorem all_pairs {E : Type*} [AddCommMonoid E] (L N : ℕ)
    (f : ℤ → ℕ → ℕ → E) :
    (∑ z ∈ labels L N, ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      if pairMatches z n r then f z.2.1 n r else 0) =
      ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, ∑ delta ∈ gaps L N n r, f delta n r := by
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  exact label_sum L N n r (fun delta => f delta n r)

/-- The full original family, not a supplied decomposition. All sharp
cutoffs, covers, the small-gap test and the original Fourier cutoff J
are still inside the same resolved row after this bijective reindex. -/
theorem family (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F F1 F2 a alpha beta t =
      ∑ s ∈ range (L+2), ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        ∑ delta ∈ gaps L N n r, if delta ≠ 0 then
          PRZZAllPoissonRows.resolved L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
            ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta a (Nat.gcd n r) t else 0 := by
  unfold PRZZAllPoissonRows.family
  apply sum_congr rfl
  intro s hs
  rw [← all_pairs]
  apply sum_congr rfl
  intro z hz
  by_cases hd : z.2.1 ≠ 0
  · simp only [if_pos hd]
  · simp [hd]

#print axioms matching_label
#print axioms mem_gaps
#print axioms label_sum
#print axioms all_pairs
#print axioms family
end XiPrime8845.PRZZNativeFamily
