import PRZZWindowTailTime

/-! Lossless source-gap reindex for the actual native label set. This
identifies the full outer absolute tail mass, not merely its grid count.
The frequency cutoff is the row-local source cutoff used by tail. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex
namespace XiPrime8845.PRZZWindowNativeTail
open PRZZWindowGrids PRZZWindowTailMass PRZZResolvedTailMass
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem gap_reindex {E : Type*} [AddCommMonoid E] (G : Finset ℤ) (f : ℤ → E)
    (T M Q b eD : ℝ) (d u : ℕ) (hT : 1 ≤ T) (hM : 0 ≤ M) (hMT : M ≤ T^b)
    (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) (hd : 1 ≤ d) :
    (∑ delta ∈ G, if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ M*u/4 ∧
      |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d
      then f (-delta) else 0) =
    ∑ delta ∈ gaps T b eD, if -delta ∈ G ∧ delta ≠ 0 ∧ |(delta:ℝ)| ≤ M*u/4 ∧
      |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d then f delta else 0 := by
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun delta _ => -delta)
  · intro delta hh
    obtain ⟨hG,hne,hsmall,hsource⟩ := mem_filter.mp hh
    exact mem_filter.mpr ⟨source_gap T M Q b eD d (-delta) hT hM hMT hQ hQT hd hsource,
      by simpa only [neg_neg,ne_eq,neg_eq_zero] using And.intro hG ⟨hne,hsmall,hsource⟩⟩
  · intro delta hh delta' hh' he
    exact neg_injective he
  · intro delta hh
    obtain ⟨hg,hG,hne,hsmall,hsource⟩ := mem_filter.mp hh
    refine ⟨-delta,mem_filter.mpr ⟨hG,?_⟩,neg_neg delta⟩
    simpa only [neg_neg,ne_eq,neg_eq_zero] using And.intro hne ⟨hsmall,hsource⟩
  · intro delta hh
    rfl

/-- Both dyadic partitions are inserted exactly once. In particular the
budget does not bound a sum with duplicated original pairs. -/
theorem pair_partition {E : Type*} [AddCommMonoid E] (N d : ℕ) (f : ℕ × ℕ → E) :
    (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then f (u,v) else 0) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ p ∈ PRZZPrefactorMass.pairs N d j l, f p := by
  have hp (g : ℕ → E) : (∑ n ∈ Finset.Icc 1 N, g n) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ n ∈ PRZZDyadic.cell N j, g n := by
    symm
    apply sum_fiberwise_of_maps_to
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Icc.mp hn).2))
  calc
    _ = ∑ j ∈ range (Nat.log 2 N+1), ∑ u ∈ PRZZDyadic.cell N j,
        ∑ v ∈ Finset.Icc 1 N, if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then f (u,v) else 0 := hp _
    _ = ∑ j ∈ range (Nat.log 2 N+1), ∑ u ∈ PRZZDyadic.cell N j,
        ∑ l ∈ range (Nat.log 2 N+1), ∑ v ∈ PRZZDyadic.cell N l,
          if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then f (u,v) else 0 := by
      apply sum_congr rfl; intro j hj
      apply sum_congr rfl; intro u hu
      exact hp _
    _ = _ := by
      simp only [PRZZPrefactorMass.pairs,sum_filter,sum_product]
      apply sum_congr rfl; intro j hj
      rw [sum_comm]

def nativeMass (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ p ∈ PRZZPrefactorMass.pairs N d j l,
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2),
          if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*p.1/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
            ‖branch dual A B T t * coeff F G js d Q V T A B (p,(-delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
                (PRZZCentralTail.residue (p,(-delta,1))/p.2) p‖ else 0

def flatMass (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*u/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
            ‖branch dual A B T t * coeff F G js d Q V T A B ((u,v),(-delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
                (PRZZCentralTail.residue ((u,v),(-delta,1))/v) (u,v)‖ else 0
      else 0

theorem flat_eq (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    flatMass F G W js L N dual T Q V b eD eH t A B =
      nativeMass F G W js L N dual T Q V b eD eH t A B := by
  unfold flatMass nativeMass
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro d hd
  exact pair_partition (E := ℝ) N d (fun p =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2),
      if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*p.1/4 ∧
        |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
        ‖branch dual A B T t * coeff F G js d Q V T A B (p,(-delta,1)) *
          PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B (-delta) 1
            (PRZZCentralTail.residue (p,(-delta,1))/p.2) p‖ else 0)

theorem native_eq (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    nativeMass F G W js L N dual T Q V b eD eH t A B =
      mass F G W js L N dual T Q V b eD eH t A B := by
  unfold nativeMass mass
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro l hl
  have hd1 := (Finset.mem_Icc.mp hd).1
  have he (p : ℕ × ℕ) := gap_reindex (PRZZNativeFamily.gaps L N (d*p.1) (d*p.2))
    (fun delta => ‖branch dual A B T t * coeff F G js d Q V T A B (p,(delta,1)) *
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

theorem native_wide_zero (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (hwide : 2*T < Q) :
    nativeMass F G W js L N dual T Q V b eD eH t A B = 0 := by
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
    have hh := (PRZZWindowTailTime.scaled_support F Q hQ hs hz).1
    linarith
  apply sum_eq_zero; intro delta hg
  split_ifs <;> simp [coeff,PRZZUnfrozenPoisson.arithmetic,hz]

/-- Equality for all positive cutoff scales: the out-of-range scale is
supplied as a zero arithmetic row, not assumed absent. -/
theorem native_eq_all (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    nativeMass F G W js L N dual T Q V b eD eH t A B =
      mass F G W js L N dual T Q V b eD eH t A B := by
  by_cases hQT : Q ≤ 2*T
  · exact native_eq F G W js L N dual T Q V b eD eH t A B hT hQ.le hQT
  · rw [native_wide_zero F G W js L N dual T Q V b eD eH t A B hNT hQ hs (lt_of_not_ge hQT),
      PRZZWindowTailTime.wide_zero F G W js L N dual T Q V b eD eH t A B hNT hQ hs (lt_of_not_ge hQT)]

/-- The native full outer mass, including actual label membership,
gcd and both dyadic grids, lies in the PRZZ common error budget. The
standard time-cutoff L1 mass is explicit. -/
theorem native_przz_time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 ≤ P → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Icc T (2*T), ‖phi t‖) ≤ P*T →
      (∫ t in Icc T (2*T), ‖phi t‖*nativeMass F G W js L N dual T Q V b eD eH t A B) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZWindowTailTime.przz_time F G W hF hG hcF hcG hsF hW hsW
    js a b S r eD eH delta ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,Filter.eventually_ge_atTop (1:ℝ)] with T h hT
  intro L N dual Q V P A B phi hN hNT hQ hP hA hB hsep hphi hmass
  simp_rw [native_eq_all F G W js L N dual T Q V b eD eH _ A B hT hNT hQ hsF]
  exact h L N dual Q V P A B phi hN hNT hQ hP hA hB hsep hphi hmass

#print axioms native_wide_zero
#print axioms pair_partition
#print axioms flat_eq
#print axioms native_eq_all
#print axioms native_przz_time
#print axioms gap_reindex
#print axioms native_eq
end XiPrime8845.PRZZWindowNativeTail
