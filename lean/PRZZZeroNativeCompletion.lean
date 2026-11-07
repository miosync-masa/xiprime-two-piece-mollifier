import PRZZZeroCompleteCell
import PRZZZeroDualExhaustion

/-! Exact gap completion of the original native collector, including
both AFE branches.  Its residual is now a concrete arithmetic/spatial
partition discrepancy of unrestricted gap series, not an unidentified
cutoff norm.  Arithmetic partition unity still requires adequate K. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroNativeCompletion
open Finset PRZZCentralMainAssembly PRZZZeroCompleteCell PRZZMellinSeparation
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def gapPart (P Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
      PRZZZeroOuterHeight.tail N a
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2))
        (PRZZWRowLimit.profile P) Phi T ((2:ℝ)^s) ((2:ℝ)^p.1) eps alpha beta

def completePart (P Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps (fun d _D M G H =>
    complete N d T M a (PRZZWRowLimit.profile P) G H Phi alpha beta)

theorem part_completion (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (K L N : ℕ) (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    zeroPart (fun y => (P y:ℂ)) (fun y => (P y:ℂ)) Phi K L N a T eps alpha beta+
      gapPart (fun y => (P y:ℂ)) Phi K L N a T eps alpha beta =
      completePart (fun y => (P y:ℂ)) Phi K L N a T eps alpha beta := by
  obtain ⟨hf,hc,hsp⟩ := PRZZWRowLimit.profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hright y hy])
  have hcap := PRZZZeroNativeTail.profile_cap P hm hlo hhi hl
  unfold zeroPart gapPart completePart collect PRZZZeroOuterHeight.tail
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro s hs'
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  exact native_completion N d T ((2:ℝ)^s) ((2:ℝ)^p.1) eps a _ _ _ Phi alpha beta
    hf.continuous hPhi hcPhi hsp hsPhi (fun y hy => hcap y)
    (Finset.mem_Icc.mp hd).1 (by positivity) hT hs hn

/-- For arbitrary K this also retains the arithmetic partition defect.
The original full model uses the covering choice log_2 N+2. -/
def spatialMismatch (P Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  branchPair (fun Phi alpha beta => completePart P Phi K
    (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta-
      PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T)

/-- BOTH genuine AFE branches, including the real Gamma multiplier.
Only the concrete partition discrepancy and the explicit true gap tails
remain; no Fourier/gap cutoffs are silently equated. -/
theorem mismatch_eq (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (K N : ℕ) (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    zeroMismatch (fun y => (P y:ℂ)) (fun y => (P y:ℂ)) Phi K N a T eps alpha beta =
      spatialMismatch (fun y => (P y:ℂ)) Phi K N a T eps alpha beta-
        branchPair (fun Phi alpha beta => gapPart (fun y => (P y:ℂ)) Phi K
          (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta := by
  obtain ⟨hf,hc,hp⟩ := PRZZZeroDualExhaustion.cutoff_regular Phi hPhi hcPhi hsPhi alpha beta ha hb T
  have h1 := part_completion P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    K (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta hT hs hn
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  have h2 := part_completion P hP hm hlo hhi hl hright
    (PRZZKeptLiteral.dualProfile Phi T alpha beta) hf hc hp
    K (PRZZLiteralExhaustion.spatialLength T) N a T eps (-beta) (-alpha) hT hs' hn'
  unfold zeroMismatch spatialMismatch branchPair
  dsimp only
  rw [← h1,← h2]
  ring

theorem gap_grid_eq (P Phi : ℝ → ℂ) (L N : ℕ) (js : List ℕ)
    (T eps : ℝ) (alpha beta : ℂ) :
    gapPart P Phi (Nat.log 2 N+1) L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      T eps alpha beta = PRZZZeroNativeTail.grid P Phi L N js T eps alpha beta := rfl

/-! The original moment model uses log_2 N+2 arithmetic scales. -/
theorem model_gap_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (T : ℝ) (A B : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) L N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := PRZZZeroNativeTail.native_row_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps r S (rate+6) heps hr hS
  refine ⟨18*C,by positivity,?_⟩
  intro L N T A B hN hT hNT hwide hsep hn ha hb'
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
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
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
        exact hb N T ((2:ℝ)^j) ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B
          hN hT hNT hwide hsep hn (by positivity) (by positivity) ha hb'
      _ = _ := by simp only [sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_mul]; ring
  calc
    _ ≤ (3*T)^2*(2*T^(4:ℝ))*(C*T^(-(rate+6))) := he.trans (by gcongr)
    _ = (18*C)*(T^(6:ℝ)*T^(-(rate+6))) := by rw [Real.rpow_ofNat,Real.rpow_ofNat]; ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2 <;> ring

theorem model_gap_eventually (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) L N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := model_gap_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps r S rate heps hr hS
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    (tendsto_rpow_atTop (show 0 < eps/2 by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (2:ℝ)] with T hsmall hwide hT
  intro L N A B hN hNT hA hB hsep
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hshift (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hL.le
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  exact hb L N T A B hN (by linarith) hNT hwide hsep hn (hshift A hA) (hshift B hB)

#print axioms model_gap_eventually
#print axioms model_gap_power
#print axioms part_completion
#print axioms mismatch_eq
#print axioms gap_grid_eq
end XiPrime8845.PRZZZeroNativeCompletion
