import PRZZZeroDualOuter

/-! Actual primitive coefficient and arithmetic-grid sums of genuine
Gamma-weighted omitted gaps, with original strict masks unchanged. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroDualNativeTail
open PRZZDiagonalAssembly PRZZZeroOuterHeight PRZZMellinSeparation
open PRZZZeroNativeCompletion
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem tail_mass_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (N : ℕ) (a : ℕ → ℂ) (G H F : ℝ → ℂ) (M Q : ℝ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) →
      Function.support G ⊆ Icc (0:ℝ) (2*Q) →
      1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → 0 < M → 0 < Q →
      let alpha := -(B/(Real.log T:ℂ))
      let beta := -(A/(Real.log T:ℂ))
      ‖tail N a G H F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T M Q eps alpha beta‖ ≤
        mass N a G H alpha beta*C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := PRZZZeroDualGaps.native_power_bound Phi hPhi hcPhi hsPhi eps S r rate heps hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn N a G H F M Q hFc hF hcap hG hT hNT hwide hM hQ
  let alpha := -(B/(Real.log T:ℂ))
  let beta := -(A/(Real.log T:ℂ))
  dsimp only
  unfold tail mass
  rw [Finset.sum_mul,Finset.sum_mul]
  simp only [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  by_cases had : admissible N d u v
  · rw [if_pos had,if_pos had]
    by_cases hz : coefficient a G H alpha beta d u v = 0
    · change ‖coefficient a G H alpha beta d u v*_‖ ≤ _
      simp only [hz,zero_mul,norm_zero]
      positivity
    have hG0 : G ((d:ℝ)*u) ≠ 0 := by
      intro hzG
      exact hz (by simp [coefficient,hzG])
    have huQ : (d:ℝ)*u ≤ 2*Q := (hG hG0).2
    have huT : (u:ℝ) ≤ T := (by exact_mod_cast (Finset.mem_Icc.mp hu).2 : (u:ℝ) ≤ N).trans hNT
    have hvT : (v:ℝ) ≤ T := (by exact_mod_cast (Finset.mem_Icc.mp hv).2 : (v:ℝ) ≤ N).trans hNT
    have hp : 1 ≤ (u:ℝ)*v := by exact_mod_cast Nat.mul_le_mul (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1
    have hpT : (u:ℝ)*v ≤ T^2 := by nlinarith [mul_le_mul huT hvT (by positivity) (by linarith : 0 ≤ T)]
    have h := (hb A B hA hB hsep hn F M Q d u v hFc hF hcap hT hwide hM hQ
      (by exact_mod_cast (Finset.mem_Icc.mp hd).1) (by exact_mod_cast (Finset.mem_Icc.mp hu).1)
      (by exact_mod_cast (Finset.mem_Icc.mp hv).1) hp hpT huQ).2
    rw [show -(A+B)/(Real.log T:ℂ) = -(B/(Real.log T:ℂ))+-(A/(Real.log T:ℂ)) by ring] at h
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)
  · simp only [if_neg had,norm_zero,zero_mul]
    positivity


theorem native_row_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ∀ (N : ℕ) (M Q1 Q2 : ℝ), 1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) →
      0 < M → 0 < Q1 →
      ‖tail N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q1)
        (scaledCutoff (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Q2)
        (PRZZWRowLimit.profile (fun y => (P y:ℂ)))
        (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T M Q1 eps
          (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  let k := 2*PRZZGCoefficient.degree js+3
  obtain ⟨D,hD,hb⟩ := tail_mass_bound Phi hPhi hcPhi hsPhi eps S r (rate+(k:ℝ)) heps hS hr
  obtain ⟨hf,hc,hsp⟩ := PRZZWRowLimit.profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hright y hy])
  have hcap := PRZZZeroNativeTail.profile_cap P hm hlo hhi hl
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn N M Q1 Q2 hN hT hNT hwide hM hQ1
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
  have hm := actual_mass js N G H _ _ S T hN hS hT hNT
    (fun x => hcap _) (fun x => hcap _) ha hb'
  have hh := hb A B hA hB hsep hn N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
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
    _ ≤ (Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) := hh.trans (by gcongr)
    _ ≤ (Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ = _ := by rw [ht]

theorem model_gap_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L N : ℕ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) →
      ‖gapPart (fun y => (P y:ℂ)) (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) (Nat.log 2 N+2) L N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := native_row_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps S r (rate+6) heps hS hr
  refine ⟨18*C,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn L N hN hT hNT hwide
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
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
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
        exact hb A B hA hB hsep hn N ((2:ℝ)^j) ((2:ℝ)^p.1) ((2:ℝ)^p.2)
          hN hT hNT hwide (by positivity) (by positivity)
      _ = _ := by simp only [sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_mul]; ring
  calc
    _ ≤ (3*T)^2*(2*T^(4:ℝ))*(C*T^(-(rate+6))) := he.trans (by gcongr)
    _ = (18*C)*(T^(6:ℝ)*T^(-(rate+6))) := by rw [Real.rpow_ofNat,Real.rpow_ofNat]; ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2 <;> ring

#print axioms model_gap_power
#print axioms native_row_power
#print axioms tail_mass_bound
end XiPrime8845.PRZZZeroDualNativeTail

