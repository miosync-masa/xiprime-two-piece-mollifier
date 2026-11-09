import PRZZClassZeroTail

/-! Complete primal omitted-gap grid with a common coefficient cap.
All native spatial and arithmetic partitions, and their time integrals,
are retained. The coefficient sequence is selected after the constant. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZClassZeroPrimalGap
open PRZZMellinSeparation PRZZWRowLimit PRZZZeroOuterHeight PRZZZeroNativeTail
open PRZZZeroNativeCompletion
set_option maxHeartbeats 8000000

theorem native_row_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T M Q1 Q2 : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → 1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < M → 0 < Q1 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖tail N a
        (scaledCutoff (profile (fun y => (P y:ℂ))) Q1)
        (scaledCutoff (profile (fun y => (P y:ℂ))) Q2)
        (profile (fun y => (P y:ℂ))) Phi T M Q1 eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := PRZZClassZeroTail.primal_power Phi hPhi hcPhi hsPhi Hcap hHcap eps r S rate heps hr hS
  obtain ⟨hf,hc,hsp⟩ := profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hright y hy])
  have hp := profile_cap P hm hlo hhi hl
  refine ⟨C,hC,?_⟩
  intro N a T M Q1 Q2 A B hcoef hN hT hNT hwide hsep hn hM hQ1 ha hb'
  exact hb N a _ _ _ T M Q1 A B hcoef hf.continuous hsp (fun y hy => hp y)
    (profile_support P Q1 hQ1 hl hright) (fun x => hp _) (fun x => hp _)
    hN hT hNT hwide hsep hn hM hQ1 ha hb'

theorem model_gap_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (a : ℕ → ℂ) (T : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) →
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) L N
      a T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := native_row_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    Hcap hHcap eps r S (rate+6) heps hr hS
  refine ⟨18*C,by positivity,?_⟩
  intro L N a T A B hcoef hN hT hNT hwide hsep hn ha hb'
  have hT0 : 0 < T := by linarith
  let s := (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))
  have hsc : (s.card:ℝ) ≤ 2*T^(4:ℝ) := by
    apply (show (s.card:ℝ) ≤ ((PRZZWindowGrids.spatial L T 4).card:ℝ) from by
      exact_mod_cast Finset.card_le_card (by
        intro j hj
        exact mem_filter.mpr ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.le⟩)).trans
    exact PRZZWindowGrids.spatial_card L T 4 hT.le (by norm_num)
  have hkc0 := PRZZWindowGrids.dyadic_card N T hN hNT
  simp only [card_range] at hkc0
  have hkc : ((Nat.log 2 N+2:ℕ):ℝ) ≤ 3*T := by
    push_cast at hkc0 ⊢
    linarith
  have he : ‖gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) L N
      a T eps
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      ((Nat.log 2 N+2:ℕ):ℝ)^2*(s.card:ℝ)*(C*T^(-(rate+6))) := by
    unfold gapPart
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
          ∑ _j ∈ s, C*T^(-(rate+6)) := by
        apply sum_le_sum
        intro p hp
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro j hj
        exact hb N a T ((2:ℝ)^j) ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B
          hcoef hN hT hNT hwide hsep hn (by positivity) (by positivity) ha hb'
      _ = _ := by simp only [sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_mul]; ring
  calc
    _ ≤ (3*T)^2*(2*T^(4:ℝ))*(C*T^(-(rate+6))) := he.trans (by gcongr)
    _ = (18*C)*(T^(6:ℝ)*T^(-(rate+6))) := by rw [Real.rpow_ofNat,Real.rpow_ofNat]; ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2; ring

theorem model_gap_eventually (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N : ℕ) (a : ℕ → ℂ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) L N
        a T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := model_gap_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    Hcap hHcap eps r S rate heps hr hS
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    (tendsto_rpow_atTop (show 0 < eps/2 by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (2:ℝ)] with T hsmall hwide hT
  intro L N a A B hcoef hN hNT hA hB hsep
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hshift (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hL.le
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  exact hb L N a T A B hcoef hN (by linarith) hNT hwide hsep hn (hshift A hA) (hshift B hB)

#print axioms native_row_power
#print axioms model_gap_power
#print axioms model_gap_eventually
end XiPrime8845.PRZZClassZeroPrimalGap
