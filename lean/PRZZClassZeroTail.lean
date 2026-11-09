import PRZZZeroDualNativeTail

/-! Arbitrary common-cap coefficients in genuine primal/dual omitted-gap tails.
The original strict masks and the true Gamma-weighted profile are retained.
Constants precede height, exhaustion and the coefficient sequence. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZClassZeroTail
open PRZZZeroOuterHeight PRZZMellinSeparation PRZZZeroNativeCompletion
set_option maxHeartbeats 8000000

theorem primal_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (G H F : ℝ → ℂ) (T M Q : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) →
      Function.support G ⊆ Icc (0:ℝ) (2*Q) →
      (∀ x, ‖G x‖ ≤ 1) → (∀ x, ‖H x‖ ≤ 1) →
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < M → 0 < Q →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖tail N a G H F Phi T M Q eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  let k : ℕ := 3
  obtain ⟨D,hD,hb⟩ := PRZZZeroOuterHeight.tail_mass_bound Phi hPhi hcPhi hsPhi eps r (rate+(k:ℝ)) heps hr
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k*(Hcap^2+1),by positivity,?_⟩
  intro N a G H F T M Q A B hcoef hFc hF hcap hGs hG hH hN hT hNT hwide hsep hn hM hQ ha hbeta
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hm := PRZZZeroOuterHeight.mass_cap N a G H _ _ Hcap S T hHcap hS hT hNT hcoef hG hH ha hbeta
  have hh := hb N a G H F T M Q A B
    hFc hF hcap hGs hT hNT hwide hsep hn hM hQ
  have hpow : (1+Real.log N)^k ≤ (2*T)^k := by
    gcongr
    linarith
  have ht : T^k*T^(-(rate+(k:ℝ))) = T^(-rate) := by
    rw [← Real.rpow_natCast T k,← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ (Hcap^2*Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) :=
      hh.trans (by gcongr)
    _ ≤ (Hcap^2*Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k*Hcap^2)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ ≤ _ := by rw [ht]; gcongr; nlinarith

theorem native_row_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ∀ (N : ℕ) (a : ℕ → ℂ) (M Q1 Q2 : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → 1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) →
      0 < M → 0 < Q1 →
      ‖tail N a
        (scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q1)
        (scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q2)
        (PRZZWRowLimit.profile (fun y => (P y:ℂ)))
        (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T M Q1 eps
          (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  let k : ℕ := 3
  obtain ⟨D,hD,hb⟩ := PRZZZeroDualNativeTail.tail_mass_bound Phi hPhi hcPhi hsPhi eps S r (rate+(k:ℝ)) heps hS hr
  obtain ⟨hf,hc,hsp⟩ := PRZZWRowLimit.profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hright y hy])
  have hcap := PRZZZeroNativeTail.profile_cap P hm hlo hhi hl
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k*(Hcap^2+1),by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn N a M Q1 Q2 hcoef hN hT hNT hwide hM hQ1
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hz (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hlogT]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hlogT.le
  have ha : |(-(B/(Real.log T:ℂ))).re| ≤ S/Real.log T := by
    simpa only [Complex.neg_re,abs_neg] using hz B hB
  have hb' : |(-(A/(Real.log T:ℂ))).re| ≤ S/Real.log T := by
    simpa only [Complex.neg_re,abs_neg] using hz A hA
  let G := scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q1
  let H := scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q2
  have hm := PRZZZeroOuterHeight.mass_cap N a G H _ _ Hcap S T hHcap hS hT hNT hcoef
    (fun x => hcap _) (fun x => hcap _) ha hb'
  have hh := hb A B hA hB hsep hn N a
    G H (PRZZWRowLimit.profile (fun y => (P y:ℂ))) M Q1 hf.continuous hsp (fun y hy => hcap y)
    (PRZZZeroNativeTail.profile_support P Q1 hQ1 hl hright) hT hNT hwide hM hQ1
  dsimp only at hh
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hpow : (1+Real.log N)^k ≤ (2*T)^k := by gcongr; linarith
  have ht : T^k*T^(-(rate+(k:ℝ))) = T^(-rate) := by
    rw [← Real.rpow_natCast T k,← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ (Hcap^2*Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) := hh.trans (by gcongr)
    _ ≤ (Hcap^2*Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k*Hcap^2)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ ≤ _ := by rw [ht]; gcongr; nlinarith

theorem model_gap_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L N : ℕ) (a : ℕ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) →
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) →
      ‖gapPart (fun y => (P y:ℂ)) (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) (Nat.log 2 N+2) L N
      a T eps
        (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := native_row_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    Hcap hHcap eps S r (rate+6) heps hS hr
  refine ⟨18*C,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn L N a hcoef hN hT hNT hwide
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
  have he : ‖gapPart (fun y => (P y:ℂ)) (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) (Nat.log 2 N+2) L N
      a T eps
      (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤
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
        exact hb A B hA hB hsep hn N a ((2:ℝ)^j) ((2:ℝ)^p.1) ((2:ℝ)^p.2)
          hcoef hN hT hNT hwide (by positivity) (by positivity)
      _ = _ := by simp only [sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_mul]; ring
  calc
    _ ≤ (3*T)^2*(2*T^(4:ℝ))*(C*T^(-(rate+6))) := he.trans (by gcongr)
    _ = (18*C)*(T^(6:ℝ)*T^(-(rate+6))) := by rw [Real.rpow_ofNat,Real.rpow_ofNat]; ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2; ring

#print axioms primal_power
#print axioms native_row_power
#print axioms model_gap_power
end XiPrime8845.PRZZClassZeroTail
