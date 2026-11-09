import PRZZWindowBandMass
import PRZZCappedTailMass

/-! Common-cap coefficients in the actual window-cut source-to-window transfer band.
The window cutoff is not replaced by the larger common cutoff. Constants
precede the coefficient sequence, native exhaustion and height. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZCappedWindowBand
open PRZZResolvedTailMass PRZZWindowGrids PRZZMellinSeparation PRZZWindowTailMass PRZZWindowTailTime
open PRZZBandOuterMass PRZZWindowBandMass
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem pair_absorbed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH A0 : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (dual : Bool) (N d j l : ℕ) (M Q V Q1 t : ℝ) (A B : ℂ)
        (J : ℕ) (w : ℤ × ℕ) (s : Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ M → M ≤ T^b → 0 < Q1 →
      t ∈ Icc T (2*T) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      s ⊆ PRZZPrefactorMass.pairs N d j l →
      Function.support (scaledCutoff F Q) ⊆ Icc (Q1/2) (3*Q1) →
      |(w.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      (∀ p ∈ s, scaledCutoff G V ((d:ℝ)*p.2) ≠ 0 →
        ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (p.2:ℝ) eH⌉₊ ≤ J) →
      (∑ p ∈ s, ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w) *
        band W M T eH t A B J (p,w)‖) ≤ K*T^(-A0)/d := by
  obtain ⟨Cm,hCm,hmass⟩ := PRZZCappedTailMass.pair_mass F G hF hG hcF hcG Hcap hHcap S hS
  obtain ⟨Ct,hCt,htail⟩ := PRZZCompatibleTail.central_band W hW hsW
    a b S r eD eH (A0+1) ha hb hS hr heD he
  obtain ⟨Cl,hCl,hlog⟩ := PRZZOptimalOuter.power_log_absorbed
    (0:ℕ) (-(A0+1)) (-A0) (by linarith)
  refine ⟨Cm*Ct*Cl+1,by positivity,?_⟩
  filter_upwards [hmass,eventually_ge_atTop (36:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hm hT hL
  intro c dual N d j l M Q V Q1 t A B J w s hcoef hN hd hNT hM hMT hQ ht hA hB hsep hsub hs1 hg hcover
  have hdR : (0:ℝ) < d := by exact_mod_cast (Nat.zero_lt_one.trans_le hd)
  have hh : (∑ p ∈ s, ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w) *
      exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖) ≤ Cm*(Real.log N)^(0:ℕ)/d := by
    simpa using hm dual c N d j l Q V t A B w s hcoef hN hd hNT ht hA hB hsub
  have hp : ∀ p ∈ s, ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w) *
      band W M T eH t A B J (p,w)‖ ≤
      ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w) *
        exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖ *
          (Ct*T^(-(A0+1))) := by
    intro p hp
    have hbox := mem_product.mp (mem_filter.mp (hsub hp)).1
    have hu := mem_Icc.mp ((PRZZDyadic.mem_cell N j p.1).mp hbox.1).1
    have hv := mem_Icc.mp ((PRZZDyadic.mem_cell N l p.2).mp hbox.2).1
    by_cases hz : scaledCutoff F Q ((d:ℝ)*p.1) = 0
    · simp [PRZZCappedTailMass.coeff,PRZZUnfrozenPoisson.arithmetic,hz]
    by_cases hzG : scaledCutoff G V ((d:ℝ)*p.2) = 0
    · simp [PRZZCappedTailMass.coeff,PRZZUnfrozenPoisson.arithmetic,hzG]
    have hcut := hcover p hp hzG
    have hrow := htail T M t (PRZZCentralTail.residue (p,w)/p.2) d Q1 J (p,w) A B
      hT hL (by linarith) hMT (Nat.zero_lt_one.trans_le hu.1) (Nat.zero_lt_one.trans_le hv.1)
      ((by exact_mod_cast hv.2 : (p.2:ℝ) ≤ N).trans hNT) ht hA hB hsep hdR hQ (hs1 hz).1 hg hcut
    simpa only [band,norm_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left hrow (norm_nonneg (branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w)))
  have hsum := sum_le_sum hp
  rw [← sum_mul] at hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_right hh (by positivity))
  have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogs : (Real.log N)^(0:ℕ) ≤
      (Real.log T)^(0:ℕ) := by gcongr
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogs hCm.le) hdR.le)
      (by positivity))
  have hl := mul_le_mul_of_nonneg_left (hlog T (by linarith))
    (show 0 ≤ Cm*Ct/(d:ℝ) by positivity)
  have hz : 0 ≤ T^(-A0)/(d:ℝ) := by positivity
  have hl' : Cm*(Real.log T)^(0:ℕ)/(d:ℝ)*
      (Ct*T^(-(A0+1))) ≤ (Cm*Ct*Cl)*T^(-A0)/(d:ℝ) := by
    calc
      _ = (Cm*Ct/(d:ℝ))*(T^(-(A0+1))*(Real.log T)^(0:ℕ)) := by ring
      _ ≤ (Cm*Ct/(d:ℝ))*(Cl*T^(-A0)) := hl
      _ = _ := by ring
  apply hbound'.trans (hl'.trans _)
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right
    (show Cm*Ct*Cl ≤ Cm*Ct*Cl+1 by linarith) hz

theorem window_pair_absorbed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (dual : Bool) (N d j l k : ℕ) (Q V t : ℝ) (A B : ℂ)
        (w : ℤ × ℕ) (s : Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → (2:ℝ)^k ≤ T^b → 0 < Q → 0 < V →
      t ∈ Icc T (2*T) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      s ⊆ PRZZPrefactorMass.pairs N d j l →
      Function.support (scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) →
      |(w.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d →
      (∑ p ∈ s, ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,w) *
        band W ((2:ℝ)^k) T eH t A B
          (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) (p,w)‖) ≤ K*T^(-power)/d := by
  obtain ⟨K,hK,h⟩ := pair_absorbed F G W hF hG hcF hcG hW hsW
    Hcap hHcap a b S r eD eH power ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c dual N d j l k Q V t A B w s hcoef hN hd hNT hM hQ hV ht hA hB hsep hsub hs1 hg
  apply h c dual N d j l ((2:ℝ)^k) Q V Q t A B
    (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) w s hcoef hN hd hNT
    (one_le_pow₀ (by norm_num)) hM hQ ht hA hB hsep hsub hs1 hg
  intro p hp hGnz
  exact PRZZArithmeticWindowCutoff.source_le_window G d k p.1 p.2 w.1 T V eH
    (by omega) (by linarith) hV hsG hGnz

def term (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N d j l k : ℕ)
    (dual : Bool) (T Q V eD eH t : ℝ) (A B : ℂ) (delta : ℤ) : ℝ :=
  if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
    ∑ p ∈ nativePairs L N d j l k delta,
      ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(delta,1)) *
        band W ((2:ℝ)^k) T eH t A B
          (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) (p,(delta,1))‖
  else 0

def mass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ delta ∈ gaps T b eD, term F G W c L N d j l k dual T Q V eD eH t A B delta

theorem absorbed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 < V → Q ≤ 2*T → t ∈ Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Function.support (PRZZMellinSeparation.scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) →
      mass F G W c L N dual T Q V b eD eH t A B ≤ C*T^(-power) := by
  let loss := 2*b+eD+3
  obtain ⟨K,hK,h⟩ := window_pair_absorbed F G W hF hG hcF hcG hsG hW hsW
    Hcap hHcap a b S r eD eH (power+loss) ha hb hS hr heD he
  refine ⟨56*K,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c L N dual Q V t A B hcoef hN hNT hQ hV hQT ht hA hB hsep hsF
  have hT0 : 0 < T := by linarith
  have hterm (k : ℕ) (hk : k ∈ spatial L T b) (d : ℕ) (hd : d ∈ Finset.Icc 1 N)
      (j l : ℕ) (delta : ℤ) :
      term F G W c L N d j l k dual T Q V eD eH t A B delta ≤ K*T^(-(power+loss)) := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
    unfold term
    split_ifs with hg
    · have hp : nativePairs L N d j l k delta ⊆ PRZZPrefactorMass.pairs N d j l :=
        filter_subset _ _
      have hh := h c dual N d j l k Q V t A B (delta,1)
        (nativePairs L N d j l k delta) hcoef hN hd1 hNT
        (mem_filter.mp hk).2 hQ hV ht hA hB hsep hp hsF hg
      exact hh.trans (div_le_self (by positivity) hdR)
    · positivity
  have hs : mass F G W c L N dual T Q V b eD eH t A B ≤
      ((spatial L T b).card:ℝ)*((Finset.Icc 1 N).card:ℝ)*
        ((range (Nat.log 2 N+1)).card:ℝ)^2*((gaps T b eD).card:ℝ)*
          (K*T^(-(power+loss))) := by
    unfold mass
    calc
      _ ≤ ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
          ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
            ∑ delta ∈ gaps T b eD, K*T^(-(power+loss)) := by
        apply sum_le_sum; intro k hk
        apply sum_le_sum; intro d hd
        apply sum_le_sum; intro j hj
        apply sum_le_sum; intro l hl
        apply sum_le_sum; intro delta hg
        exact hterm k hk d hd j l delta
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hc := mul_le_mul_of_nonneg_right (outer_card L N T b eD hN hNT hb heD)
    (show 0 ≤ K*T^(-(power+loss)) by positivity)
  apply hs.trans (hc.trans_eq _)
  dsimp only [loss]
  rw [show 56*T^(2*b+eD+3)*(K*T^(-(power+(2*b+eD+3)))) =
    56*K*(T^(2*b+eD+3)*T^(-(power+(2*b+eD+3)))) by ring]
  rw [← Real.rpow_add hT0]
  congr 2
  ring

theorem wide_zero (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (hwide : 2*T < Q) :
    mass F G W c L N dual T Q V b eD eH t A B = 0 := by
  unfold mass
  apply sum_eq_zero; intro k hk
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro j hj
  apply sum_eq_zero; intro l hl
  apply sum_eq_zero; intro delta hg
  unfold term
  split_ifs
  · apply sum_eq_zero; intro p hp
    have hpair := mem_filter.mp (mem_filter.mp hp).1
    have hdu : (d:ℝ)*p.1 ≤ T := (by exact_mod_cast hpair.2.2.1 : (d:ℝ)*p.1 ≤ N).trans hNT
    have hz : scaledCutoff F Q ((d:ℝ)*p.1) = 0 := by
      by_contra hz
      have hh := (scaled_support F Q hQ hs hz).1
      linarith
    simp [PRZZCappedTailMass.coeff,PRZZUnfrozenPoisson.arithmetic,hz]
  · rfl

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
  obtain ⟨C,hC,h⟩ := absorbed F G W hF hG hcF hcG hsG hW hsW Hcap hHcap a b S r eD eH power
    ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c L N dual Q V t A B hcoef hN hNT hQ hV ht hA hB hsep
  have hT0 : 0 < T := lt_of_lt_of_le
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  by_cases hQT : Q ≤ 2*T
  · exact h c L N dual Q V t A B hcoef hN hNT hQ hV hQT ht hA hB hsep (scaled_support F Q hQ hsF)
  · rw [wide_zero F G W c L N dual T Q V b eD eH t A B hNT hQ hsF (lt_of_not_ge hQT)]
    positivity

theorem native_mass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    (∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
            if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*u/4 ∧
              |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
              ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B ((u,v),(-delta,1)) *
                band W ((2:ℝ)^k) T eH t A B (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) ((u,v),(-delta,1))‖ else 0
        else 0) = mass F G W c L N dual T Q V b eD eH t A B := by
  unfold mass
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro d hd
  rw [PRZZWindowNativeTail.pair_partition (E := ℝ) N d (fun p =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2),
      if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^k*p.1/4 ∧
        |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
        ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(-delta,1)) *
          band W ((2:ℝ)^k) T eH t A B (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) (p,(-delta,1))‖ else 0)]
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro l hl
  have he (p : ℕ × ℕ) := PRZZWindowNativeTail.gap_reindex
    (PRZZNativeFamily.gaps L N (d*p.1) (d*p.2))
    (fun delta => ‖branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(delta,1)) *
      band W ((2:ℝ)^k) T eH t A B (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^k) V eH) (p,(delta,1))‖)
    T ((2:ℝ)^k) Q b eD d p.1 hT (by positivity) (mem_filter.mp hk).2 hQ hQT
    (Finset.mem_Icc.mp hd).1
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

/-- The actual central row difference has exactly the band kernel and
the same arithmetic coefficient. The local/common sign is explicit. -/

theorem central_row_difference (F G W : ℝ → ℂ) (c : ℕ → ℂ)
    (L d s u v : ℕ) (delta : ℤ) (T Q V eH t : ℝ) (A B : ℂ) :
    PRZZNativeComponents.row .central L (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH) W (scaledCutoff F Q) (scaledCutoff G V)
      ((2:ℝ)^s) ((u,v),(delta,1)) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      c d t-
    PRZZNativeComponents.row .central L
      ⌈PRZZSourceCutoffs.poissonCutoff 1 T ((2:ℝ)^s) (v:ℝ) eH⌉₊
      W (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(delta,1))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      c d t =
      if |(delta:ℝ)| ≤ (2:ℝ)^s*u/4 then
        PRZZCappedTailMass.coeff F G c d Q V T A B ((u,v),(delta,1))*
          band W ((2:ℝ)^s) T eH t A B (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH) ((u,v),(delta,1)) else 0 := by
  simp only [PRZZNativeComponents.row,PRZZCappedTailMass.coeff,band,add_div]
  split_ifs <;> ring

#print axioms pair_absorbed
#print axioms window_pair_absorbed
#print axioms absorbed
#print axioms wide_zero
#print axioms uniform
#print axioms native_mass
#print axioms central_row_difference
end XiPrime8845.PRZZCappedWindowBand
