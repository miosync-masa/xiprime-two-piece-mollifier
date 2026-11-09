import PRZZBodyTailMass
import PRZZCappedNativeTail
import PRZZCappedWindowBand
import PRZZCappedSubunitMass

/-! Absolute mass of the actual native body-cut tail. Cutoff transport is
an equality before norms: body tail = source tail + subunit - transfer.
The strict source selection is enlarged only to its closed majorant;
the native gap labels and the actual arithmetic coefficient stay intact. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZCappedBodyMass
open PRZZMellinSeparation PRZZNativeComponents PRZZSelectedLocalFourier
open PRZZWindowCentralAssembly PRZZWindowGrids PRZZResolvedTailMass
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem row_transport (L d s u v : ℕ) (gap : ℤ) (F G W : ℝ → ℂ)
    (a : ℕ → ℂ) (T V eH t : ℝ) (alpha beta : ℂ)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < v) (hs : alpha+beta ≠ 0) :
    row .tail L (bodyCut T V eH s d u v gap) W F G ((2:ℝ)^s)
      ((u,v),(-gap,1)) alpha beta a d t =
    row .tail L (sourceCutoff T eH s d u v gap) W F G ((2:ℝ)^s)
      ((u,v),(-gap,1)) alpha beta a d t+
    (row .central L (windowCut T V eH s d u v gap) W F G ((2:ℝ)^s)
        ((u,v),(-gap,1)) alpha beta a d t-
      row .central L (bodyCut T V eH s d u v gap) W F G ((2:ℝ)^s)
        ((u,v),(-gap,1)) alpha beta a d t)-
    (row .central L (windowCut T V eH s d u v gap) W F G ((2:ℝ)^s)
        ((u,v),(-gap,1)) alpha beta a d t-
      row .central L (sourceCutoff T eH s d u v gap) W F G ((2:ℝ)^s)
        ((u,v),(-gap,1)) alpha beta a d t) := by
  have hh := row_central_tail L (bodyCut T V eH s d u v gap)
    (sourceCutoff T eH s d u v gap) d W F G ((2:ℝ)^s) ((u,v),(-gap,1))
    a alpha beta t hW hsW (by positivity) ht hu hv hs
  linear_combination hh

def mass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ s ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then
        ∑ gap ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if gap ≠ 0 ∧ |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
            |((-gap:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d then
            ‖branch dual A B T t *
              row .tail L (bodyCut T V eH s d u v gap) W (scaledCutoff F Q)
                (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(-gap,1))
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                c d t‖ else 0
      else 0

theorem mass_nonneg (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    0 ≤ mass F G W c L N dual T Q V b eD eH t A B := by
  unfold mass
  positivity

/-- A comparison of the actual absolute row masses, not just the norm
of their sum. Thus it can feed the literal collector's pairedMass. -/
theorem mass_bound (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (hT : 1 ≤ T) (hQ : 0 < Q) (hQT : Q ≤ 2*T) (ht : 0 < t)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    mass F G W c L N dual T Q V b eD eH t A B ≤
      PRZZCappedNativeTail.nativeMass F G W c L N dual T Q V b eD eH t A B+
      PRZZCappedSubunitMass.mass F G W c L N dual T Q V b eD eH t A B+
      PRZZCappedWindowBand.mass F G W c L N dual T Q V b eD eH t A B := by
  rw [← PRZZCappedNativeTail.flat_eq,
    ← PRZZCappedSubunitMass.native_mass F G W c L N dual T Q V b eD eH t A B hT hQ.le hQT,
    ← PRZZCappedWindowBand.native_mass F G W c L N dual T Q V b eD eH t A B hT hQ.le hQT]
  unfold mass PRZZCappedNativeTail.flatMass
  simp only [← sum_add_distrib]
  apply sum_le_sum; intro s hss
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro u hu
  apply sum_le_sum; intro v hv
  split_ifs with had
  · simp only [← sum_add_distrib]
    apply sum_le_sum; intro gap hg
    by_cases hc : gap ≠ 0 ∧ |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
        |((-gap:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d
    · simp only [if_pos hc]
      rw [row_transport L d s u v gap _ _ W _ T V eH t _ _ hW hsW ht
        (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs]
      simp only [mul_sub,mul_add]
      apply (norm_sub_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · rw [source_tail]
          simp only [if_pos hc.2.1,PRZZCappedTailMass.coeff,mul_assoc,le_refl]
        · by_cases hraw : PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1
          · simp only [bodyCut,if_pos hraw,windowCut,← mul_sub]
            rw [PRZZCappedSubunitMass.central_row_difference]
            have hcond : gap ≠ 0 ∧ |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
                |((-gap:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d ∧
                PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1 :=
              ⟨hc.1,hc.2.1,hc.2.2,hraw⟩
            rw [if_pos hc.2.1,if_pos hcond]
            simp only [mul_assoc,le_refl]
          · simp [bodyCut,hraw]
      · simp only [windowCut,sourceCutoff,← mul_sub]
        rw [PRZZCappedWindowBand.central_row_difference]
        simp only [if_pos hc.2.1,mul_assoc,le_refl]
    · simp only [if_neg hc]
      split_ifs <;> positivity
  · simp

theorem wide_zero (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hwide : 2*T < Q) :
    mass F G W c L N dual T Q V b eD eH t A B = 0 := by
  unfold mass
  apply sum_eq_zero; intro s hss
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  by_cases had : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N
  · rw [if_pos had]
    have hz : scaledCutoff F Q ((d:ℝ)*u) = 0 := by
      by_contra hz
      have hh := (PRZZWindowTailTime.scaled_support F Q hQ hsF hz).1
      have hdu : (d:ℝ)*u ≤ T := (by exact_mod_cast had.2.1 : (d:ℝ)*u ≤ N).trans hNT
      linarith
    apply sum_eq_zero; intro gap hg
    split_ifs <;> simp [row,PRZZUnfrozenPoisson.arithmetic,hz]
  · simp only [if_neg had]

theorem uniform (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 < V → t ∈ Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      mass F G W c L N dual T Q V b eD eH t A B ≤ C*T^(-power) := by
  obtain ⟨Ct,hCt,htail⟩ := PRZZCappedWindowTime.uniform F G W hF hG hcF hcG hsF hW hsW
    Hcap hHcap a b S r eD eH power ha hb hS hr heD he
  obtain ⟨Cs,hCs,hsub⟩ := PRZZCappedSubunitMass.uniform F G W hF hG hcF hcG hsF hsG hW hsW
    Hcap hHcap a b S r eD eH power ha hb hS hr heD he
  obtain ⟨Cb,hCb,hband⟩ := PRZZCappedWindowBand.uniform F G W hF hG hcF hcG hsF hsG hW hsW
    Hcap hHcap a b S r eD eH power ha hb hS hr heD he
  refine ⟨Ct+Cs+Cb,by positivity,?_⟩
  filter_upwards [htail,hsub,hband,eventually_ge_atTop (2:ℝ)] with T htail hsub hband hT
  intro c L N dual Q V t A B hcoef hN hNT hQ hV ht hA hB hsep
  by_cases hQT : Q ≤ 2*T
  · have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
      rw [← add_div]
      exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
        (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
    have hh := mass_bound F G W c L N dual T Q V b eD eH t A B hW hsW
      (by linarith) hQ hQT (by linarith [ht.1]) hs
    rw [PRZZCappedNativeTail.native_eq_all F G W c L N dual T Q V b eD eH t A B
      (by linarith) hNT hQ hsF] at hh
    exact hh.trans ((add_le_add (add_le_add
      (htail c L N dual Q V t A B hcoef hN hNT hQ ht hA hB hsep)
      (hsub c L N dual Q V t A B hcoef hN hNT hQ hV ht hA hB hsep))
      (hband c L N dual Q V t A B hcoef hN hNT hQ hV ht hA hB hsep)).trans_eq (by ring))
  · rw [wide_zero F G W c L N dual T Q V b eD eH t A B hNT hQ hsF (lt_of_not_ge hQT)]
    positivity

#print axioms row_transport
#print axioms mass_nonneg
#print axioms mass_bound
#print axioms wide_zero
#print axioms uniform
end XiPrime8845.PRZZCappedBodyMass
