import PRZZSpatialErrorJoin

/-! Exact native sign/gap and active dyadic-grid bookkeeping for freezing
integral charges. Zero cutoff values are removed before applying the
active identity. This compares actual row integrals, not assumed errors. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZNativeFreezeEnvelope
open PRZZNativeCentralLiteral PRZZPrefactorMass PRZZActiveFreezeBudget
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem gap_sum {E : Type*} [AddCommMonoid E] (g : Finset ℤ) (B : ℝ) (f : ℤ → E) :
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
    simpa using (PRZZAStar.delta_cutoff_iff B delta).mp hg
  · intro delta hd; rfl

theorem native_rectangle {E : Type*} [AddCommMonoid E] (L N d : ℕ) (D : ℝ) (f : PRZZAStar.Index → E) :
    (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d then f ((u,v),(-delta,1)) else 0 else 0) =
    ∑ z ∈ PRZZAStar.indices N d D 2,
      if -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) then f z else 0 := by
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
    have hh := gap_sum (PRZZNativeFamily.gaps L N (d*u) (d*v)) (D/d) (fun delta => f ((u,v),(delta,1)))
    simpa only [gapRectangle,sum_filter] using hh
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp [had,had']

/-- Every positive original pair appears in exactly one dyadic cell. -/
theorem active_grid {E : Type*} [AddCommMonoid E] (N d : ℕ) (D : ℝ)
    (F1 F2 : ℝ → ℂ) (f : PRZZAStar.Index → E) :
    (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ z ∈ active N d j l D 2 F1 F2, f z) =
    ∑ z ∈ (PRZZAStar.indices N d D 2).filter (fun z => F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0), f z := by
  let s := (PRZZAStar.indices N d D 2).filter (fun z => F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0)
  have he (p : ℕ × ℕ) : s.filter (fun z => (Nat.log 2 z.1.1,Nat.log 2 z.1.2) = p) = active N d p.1 p.2 D 2 F1 F2 := by
    rcases p with ⟨j,l⟩
    ext z
    simp only [s,active,local_indices_eq,PRZZDyadic.cell,mem_filter,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hz,hf⟩,hp⟩
      have huv := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
      exact ⟨⟨hz,⟨huv.1,hp.1⟩,⟨huv.2,hp.2⟩⟩,hf⟩
    · rintro ⟨⟨hz,hu,hv⟩,hf⟩; exact ⟨⟨hz,hf⟩,hu.2,hv.2⟩
  calc
    _ = ∑ p ∈ range (Nat.log 2 N+1) ×ˢ range (Nat.log 2 N+1),
        ∑ z ∈ active N d p.1 p.2 D 2 F1 F2, f z := by simp only [sum_product]
    _ = _ := by
      simp_rw [← he]
      apply sum_fiberwise_of_maps_to
      intro z hz
      have huv := mem_product.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hz).1).1).1
      have hlu : Nat.log 2 z.1.1 ≤ Nat.log 2 N := Nat.log_mono_right (mem_Icc.mp huv.1).2
      have hlv : Nat.log 2 z.1.2 ≤ Nat.log 2 N := Nat.log_mono_right (mem_Icc.mp huv.2).2
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hlu),mem_range.mpr (Nat.lt_succ_of_le hlv)⟩

theorem freeze_zero (L J d : ℕ) (F F1 F2 phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hz : F1 ((d:ℝ)*z.1.1) = 0 ∨ F2 ((d:ℝ)*z.1.2) = 0) :
    (∫ t in Set.Icc T (2*T), phi t*PRZZNativeComponents.row .freeze L J F F1 F2 M z alpha beta a d t) = 0 := by
  rcases hz with hz | hz <;>
    simp [PRZZNativeComponents.row,PRZZUnfrozenPoisson.arithmetic,hz]

def charge (L J N K : ℕ) (F G H phi : ℝ → ℂ) (js : List ℕ)
    (T M Q V eps : ℝ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ s ∈ range K, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s*M) Q eps/d then
          ‖∫ t in Set.Icc T (2*T), phi t*PRZZNativeComponents.row .freeze L J F
            (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
            ((2:ℝ)^s*M) ((u,v),(-delta,1)) alpha beta
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t‖ else 0 else 0

theorem dominates (L J N K : ℕ) (F G H phi : ℝ → ℂ) (js : List ℕ)
    (T M Q V eps eH : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q)
    (hs : alpha+beta ≠ 0) (hheight : 8 ≤ T^(1-eps)) :
    charge L J N K F G H phi js T M Q V eps alpha beta ≤
      PRZZFullFreezeBudget.fullMass L J F phi js N K T M Q V eps eH G H alpha beta (alpha+beta) := by
  unfold charge PRZZFullFreezeBudget.fullMass
  apply sum_le_sum; intro d hd
  have rotate (s t u : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) = ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, f i j k := by
    calc
      _ = ∑ i ∈ s, ∑ k ∈ u, ∑ j ∈ t, f i j k := by
        apply sum_congr rfl; intro i hi; rw [sum_comm]
      _ = _ := sum_comm
  let g := fun j l k => ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
      (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V),
      ‖PRZZActualPoissonError.rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta (alpha+beta)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V) phi‖
  change _ ≤ ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1), ∑ k ∈ range K, g j l k
  apply le_trans _ (le_of_eq (rotate (range (Nat.log 2 N+1)) (range (Nat.log 2 N+1)) (range K) g).symm)
  apply sum_le_sum; intro s hss
  let F1 := PRZZMellinSeparation.scaledCutoff G Q
  let F2 := PRZZMellinSeparation.scaledCutoff H V
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let D := PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s*M) Q eps
  let f := fun z => ‖∫ t in Set.Icc T (2*T), phi t*PRZZNativeComponents.row .freeze L J F F1 F2
    ((2:ℝ)^s*M) z alpha beta a d t‖
  rw [native_rectangle L N d D f]
  have he : (∑ z ∈ (PRZZAStar.indices N d D 2).filter
      (fun z => F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0), f z) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ z ∈ active N d j l D 2 F1 F2,
          ‖PRZZActualPoissonError.rowIntegral L J F ((2:ℝ)^s*M) T z alpha beta (alpha+beta) a d F1 F2 phi‖ := by
    rw [← active_grid N d D F1 F2 f]
    apply sum_congr rfl; intro j hj
    apply sum_congr rfl; intro l hl
    apply sum_congr rfl; intro z hz
    exact congrArg norm (PRZZFullFreezeBudget.active_freeze_identity L J N d j l F hF hsF T
      ((2:ℝ)^s*M) Q eps z alpha beta a F1 F2 phi (mem_Icc.mp hd).1 hT (by positivity) hs
      (PRZZWindowTailTime.scaled_support G Q hQ hsG) hheight hz).symm
  apply le_trans _ he.le
  rw [sum_filter]
  apply sum_le_sum; intro z hz
  by_cases hc : F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0
  · rw [if_pos hc]
    split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  · have hz0 : F1 ((d:ℝ)*z.1.1) = 0 ∨ F2 ((d:ℝ)*z.1.2) = 0 := by tauto
    have hf : f z = 0 := by
      dsimp [f]
      rw [freeze_zero L J d F F1 F2 phi a T ((2:ℝ)^s*M) alpha beta z hz0,norm_zero]
    simp only [if_neg hc]
    change (if -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) then f z else 0) ≤ 0
    simp only [hf,ite_self,le_refl]

#print axioms gap_sum
#print axioms native_rectangle
#print axioms active_grid
#print axioms freeze_zero
#print axioms dominates
end XiPrime8845.PRZZNativeFreezeEnvelope
