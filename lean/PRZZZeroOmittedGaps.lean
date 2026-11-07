import PRZZZeroSpatialHeight

/-! The actual signed source-cutoff complement, summed over ALL omitted
integer gaps after the actual time and space integrations.  Strict retained
cutoffs have the weak complement used here, including equality endpoints. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroOmittedGaps
open PRZZCentralFubini
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def value (F Phi : ℝ → ℂ) (M T u v delta : ℝ) (sigma : ℂ) : ℂ :=
  ∫ x in Ioi (0:ℝ), ∫ t : ℝ,
    kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t

def omitted (F Phi : ℝ → ℂ) (M T Q d u v eps : ℝ) (sigma : ℂ) (n : ℕ) : ℂ :=
  if PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ ((n+1:ℕ):ℝ) then
    value F Phi M T u v ((n+1:ℕ):ℝ) sigma+
      value F Phi M T u v (-((n+1:ℕ):ℝ)) sigma else 0

/-- This is an equality of the actual retained/complementary row values,
not merely an inequality between budgets.  The boundary belongs to omitted. -/
theorem split (F Phi : ℝ → ℂ) (M T Q d u v eps : ℝ) (sigma : ℂ) (n : ℕ) :
    (if ((n+1:ℕ):ℝ) < PRZZSourceCutoffs.deltaCutoff T M Q eps/d then
      value F Phi M T u v ((n+1:ℕ):ℝ) sigma+
        value F Phi M T u v (-((n+1:ℕ):ℝ)) sigma else 0)+
      omitted F Phi M T Q d u v eps sigma n =
    value F Phi M T u v ((n+1:ℕ):ℝ) sigma+
      value F Phi M T u v (-((n+1:ℕ):ℝ)) sigma := by
  unfold omitted
  split_ifs <;> simp_all <;> linarith

theorem absolute_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (F : ℝ → ℂ) (T M Q d u v eps L : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → L ≠ 0 → r ≤ ‖A+B‖ →
      ‖(A+B)/(L:ℂ)‖ ≤ 1/8 → 1 ≤ T →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      let sigma := (A+B)/(L:ℂ)
      Summable (fun j : ℕ => ‖omitted F Phi M T Q d u v eps sigma j‖) ∧
        (∑' j : ℕ, ‖omitted F Phi M T Q d u v eps sigma j‖) ≤
          C n*(1+L^2/r^2)*T^5*(3*T^(-eps))^n := by
  obtain ⟨C,hC,hb⟩ := PRZZZeroSpatialHeight.row_integral Phi hPhi hcPhi hsPhi r hr
  let p := fun j : ℕ => 1/(((j+1:ℕ):ℝ)^2)
  have hp : Summable p := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let Z := ∑' j : ℕ, p j
  have hZ : 0 ≤ Z := tsum_nonneg (fun j => by dsimp [p]; positivity)
  refine ⟨fun n => 2*C n*Z,fun n => mul_nonneg (mul_nonneg (by norm_num) (hC n)) hZ,?_⟩
  intro n F T M Q d u v eps L A B hFc hF hcap hL hsep hn hT hM hQ hd hu hv hp1 hpT huQ
  let sigma := (A+B)/(L:ℂ)
  have hCn := hC n
  let K := 2*C n*(1+L^2/r^2)*T^5*(3*T^(-eps))^n
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he (j : ℕ) : ‖omitted F Phi M T Q d u v eps sigma j‖ ≤ K*p j := by
    unfold omitted
    split_ifs with hg
    · have hg' : PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |((j+1:ℕ):ℝ)| := by
        simpa only [abs_of_pos (show (0:ℝ) < (j+1:ℕ) by positivity)] using hg
      have h1 := hb n F T M Q d u v ((j+1:ℕ):ℝ) eps L A B
        hFc hF hcap hL hsep hn hT hM hQ hd hu hv hp1 hpT huQ hg'
      have h2 := hb n F T M Q d u v (-((j+1:ℕ):ℝ)) eps L A B
        hFc hF hcap hL hsep hn hT hM hQ hd hu hv hp1 hpT huQ (by simpa only [abs_neg] using hg')
      apply (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq _)
      simp only [abs_neg,abs_of_pos (show (0:ℝ) < (j+1:ℕ) by positivity)]
      dsimp [K,p]
      ring
    · rw [norm_zero]
      exact mul_nonneg hK (by dsimp [p]; positivity)
  have hm := (hp.mul_left K).of_nonneg_of_le (fun j => norm_nonneg _) he
  refine ⟨hm,?_⟩
  apply (hm.tsum_le_tsum he (hp.mul_left K)).trans_eq
  rw [tsum_mul_left]
  dsimp [K,Z]
  ring

/-- All omitted gaps, not a finite gap truncation.  Constants and the
IBP order are selected BEFORE height and every original local scale. -/
theorem power_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps r rate : ℝ) (heps : 0 < eps) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℂ) (T M Q d u v : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 1 < T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      let sigma := (A+B)/(Real.log T:ℂ)
      Summable (omitted F Phi M T Q d u v eps sigma) ∧
        ‖∑' j : ℕ, omitted F Phi M T Q d u v eps sigma j‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := absolute_bound Phi hPhi hcPhi hsPhi r hr
  obtain ⟨n,D,hD,hh⟩ := PRZZZeroUniformHeight.source_order_uniform eps 5 rate r heps hr
  have hCn := hC n
  refine ⟨C n*D+1,by positivity,?_⟩
  intro F T M Q d u v A B hFc hF hcap hT hsep hn hM hQ hd hu hv hp1 hpT huQ
  obtain ⟨hs,hb'⟩ := hb n F T M Q d u v eps (Real.log T) A B
    hFc hF hcap (Real.log_pos hT).ne' hsep hn hT.le hM hQ hd hu hv hp1 hpT huQ
  have hsum := hs.of_norm
  refine ⟨hsum,?_⟩
  apply (norm_tsum_le_tsum_norm hs).trans (hb'.trans _)
  have h := mul_le_mul_of_nonneg_left (hh T hT.le) (hC n)
  rw [Real.rpow_ofNat] at h
  have ht : 0 ≤ T^(-rate) := Real.rpow_nonneg (by linarith) _
  convert (h.trans (show C n*(D*T^(-rate)) ≤ (C n*D+1)*T^(-rate) by nlinarith)) using 1 <;> ring

/-- The actual profile reaches twice its nominal scale.  Half the
epsilon slack accommodates this factor without changing the native cutoff. -/
theorem cutoff_widen (T M Q eps : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hQ : 0 ≤ Q) (hwide : 2 ≤ T^(eps/2)) :
    PRZZSourceCutoffs.deltaCutoff T M (2*Q) (eps/2) ≤
      PRZZSourceCutoffs.deltaCutoff T M Q eps := by
  have he (e : ℝ) : PRZZSourceCutoffs.deltaCutoff T M Q e = M*Q/T*T^e := by
    unfold PRZZSourceCutoffs.deltaCutoff
    rw [Real.rpow_sub hT,Real.rpow_one]
    field_simp
  have hw : PRZZSourceCutoffs.deltaCutoff T M (2*Q) (eps/2) =
      2*(M*Q/T)*T^(eps/2) := by
    unfold PRZZSourceCutoffs.deltaCutoff
    rw [Real.rpow_sub hT,Real.rpow_one]
    field_simp
    <;> ring
  have heps : T^eps = T^(eps/2)*T^(eps/2) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  rw [hw,he eps,heps]
  have h := mul_le_mul_of_nonneg_right hwide (show 0 ≤ (M*Q/T)*T^(eps/2) by positivity)
  nlinarith only [h]

theorem omitted_norm_mono (F Phi : ℝ → ℂ) (M T Q Q' d u v eps eps' : ℝ)
    (sigma : ℂ) (hcut : PRZZSourceCutoffs.deltaCutoff T M Q' eps'/d ≤
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d) (j : ℕ) :
    ‖omitted F Phi M T Q d u v eps sigma j‖ ≤
      ‖omitted F Phi M T Q' d u v eps' sigma j‖ := by
  unfold omitted
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' (hcut.trans h))
  · simp only [norm_zero]
    exact norm_nonneg _
  · simp

/-- Native cutoff complement, with the actual doubled arithmetic support.
The source cutoff in `omitted` is NOT replaced by a wider cutoff. -/
theorem native_power_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps r rate : ℝ) (heps : 0 < eps) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℂ) (T M Q d u v : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 1 < T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ 2*Q →
      let sigma := (A+B)/(Real.log T:ℂ)
      Summable (omitted F Phi M T Q d u v eps sigma) ∧
        ‖∑' j : ℕ, omitted F Phi M T Q d u v eps sigma j‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := absolute_bound Phi hPhi hcPhi hsPhi r hr
  obtain ⟨n,D,hD,hh⟩ := PRZZZeroUniformHeight.source_order_uniform (eps/2) 5 rate r (by linarith) hr
  have hCn := hC n
  refine ⟨C n*D+1,by positivity,?_⟩
  intro F T M Q d u v A B hFc hF hcap hT hwide hsep hn hM hQ hd hu hv hp1 hpT huQ
  obtain ⟨hs,hb'⟩ := hb n F T M (2*Q) d u v (eps/2) (Real.log T) A B
    hFc hF hcap (Real.log_pos hT).ne' hsep hn hT.le hM (by positivity) hd hu hv hp1 hpT huQ
  have hcut := div_le_div_of_nonneg_right (cutoff_widen T M Q eps (by linarith) hM.le hQ.le hwide) hd.le
  have hm := fun j => omitted_norm_mono F Phi M T Q (2*Q) d u v eps (eps/2)
    ((A+B)/(Real.log T:ℂ)) hcut j
  have hnative := hs.of_nonneg_of_le (fun j => norm_nonneg _) hm
  refine ⟨hnative.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hnative).trans
    ((hnative.tsum_le_tsum hm hs).trans (hb'.trans _))
  have h := mul_le_mul_of_nonneg_left (hh T hT.le) (hC n)
  rw [Real.rpow_ofNat] at h
  have ht : 0 ≤ T^(-rate) := Real.rpow_nonneg (by linarith) _
  convert (h.trans (show C n*(D*T^(-rate)) ≤ (C n*D+1)*T^(-rate) by nlinarith)) using 1 <;> ring

#print axioms native_power_bound
#print axioms omitted_norm_mono
#print axioms cutoff_widen
#print axioms split
#print axioms absolute_bound
#print axioms power_bound
end XiPrime8845.PRZZZeroOmittedGaps
