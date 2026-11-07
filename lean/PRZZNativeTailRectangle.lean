import PRZZActualTailCollector

/-! Exact native-gap reindexing for real absolute tail densities.
The literal H=2 rectangle has one auxiliary h=1; no row is duplicated. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZNativeTailRectangle
open PRZZNativeCentralLiteral
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000

theorem gap_reindex {E : Type*} [AddCommMonoid E] (g : Finset ℤ) (B : ℝ) (f : ℤ → E) :
    (∑ delta ∈ g, if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < B then f (-delta) else 0) =
      ∑ delta ∈ gapRectangle B, if -delta ∈ g then f delta else 0 := by
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun delta _ => -delta)
  · intro delta hd
    obtain ⟨hg,hh⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨(PRZZAStar.delta_cutoff_iff B (-delta)).mpr (by simpa using hh),by simpa using hg⟩
  · intro x hx y hy he; exact neg_injective he
  · intro delta hd
    obtain ⟨hg,hh⟩ := mem_filter.mp hd
    refine ⟨-delta,mem_filter.mpr ⟨hh,?_⟩,by simp⟩
    have hz := (PRZZAStar.delta_cutoff_iff B delta).mp hg
    simpa using hz
  · intro delta hd; rfl

theorem rectangle {E : Type*} [AddCommMonoid E] (R N d : ℕ) (D M : ℝ)
    (f : PRZZAStar.Index → E) :
    (∑ z ∈ PRZZAStar.indices N d D 2, if good R N d M z then f z else 0) =
      ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps R N (d*u) (d*v),
            if delta ≠ 0 ∧ |(delta:ℝ)| < D/d then
              if |((-delta:ℤ):ℝ)| ≤ M*u/4 then f ((u,v),(-delta,1)) else 0
            else 0
        else 0 := by
  symm
  have h2 : (Icc 1 ⌊(2:ℝ)⌋₊).filter (fun h : ℕ => (h:ℝ)<2) = {1} := by
    ext h
    rw [PRZZAStar.h_cutoff_iff,mem_singleton]
    constructor
    · intro hh
      have : h < 2 := by exact_mod_cast hh.2
      omega
    · intro hh; subst h; norm_num
  unfold PRZZAStar.indices
  rw [h2]
  simp only [Finset.product_eq_sprod,sum_product,sum_filter,sum_singleton]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    have he := gap_reindex (PRZZNativeFamily.gaps R N (d*u) (d*v)) (D/d)
      (fun delta => if |(delta:ℝ)| ≤ M*u/4 then f ((u,v),(delta,1)) else 0)
    calc
      _ = ∑ delta ∈ PRZZNativeFamily.gaps R N (d*u) (d*v),
          if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d then
            (if |((-delta:ℤ):ℝ)| ≤ M*u/4 then f ((u,v),(-delta,1)) else 0) else 0 := by
        apply sum_congr rfl; intro delta hd
        have hz : delta ≠ 0 ↔ 0 < |(delta:ℝ)| := by
          rw [abs_pos]; exact_mod_cast (Iff.rfl : delta ≠ 0 ↔ delta ≠ 0)
        simp only [hz]
      _ = _ := by
        rw [he]
        unfold gapRectangle good
        rw [sum_filter]
        apply sum_congr rfl; intro delta hd
        dsimp only
        split_ifs <;> simp_all
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had']

#print axioms gap_reindex
#print axioms rectangle
end XiPrime8845.PRZZNativeTailRectangle
