import PRZZZeroDualBoundary

/-! Genuine Gamma-weighted omitted native gap estimates. The reflected
source shift and original Gamma shifts remain distinct. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroDualGaps
open PRZZZeroGap PRZZCentralFubini PRZZZeroOmittedGaps
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem row_integral (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ∀ (n : ℕ) (F : ℝ → ℂ) (M Q d u v delta eps : ℝ),
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 1 ≤ T →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta| →
      ‖value F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
        M T u v delta (-(A+B)/(Real.log T:ℂ))‖ ≤
          C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-eps))^n/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := PRZZZeroDualBoundary.phase_envelope Phi hPhi hcPhi hsPhi S r hS hr
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨fun n => C n*J,fun n => mul_nonneg (hC n) hJ,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn n F M Q d u v delta eps hF hcap hT hM hQ hd hu hv hp hpT huQ hgap
  have hT0 : 0 < T := by linarith
  have hcut : 0 < PRZZSourceCutoffs.deltaCutoff T M Q eps/d := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hd0 : delta ≠ 0 := abs_pos.mp (hcut.trans_le hgap)
  let sigma := -(A+B)/(Real.log T:ℂ)
  let Psi := PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  have hCn := hC n
  let K := C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-eps))^n/|delta|^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  unfold value
  simp_rw [kernel_time]
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_of_nonneg
    (f := fun x : ℝ => ‖F ((M/v)⁻¹*x)*core Psi T (u*v) sigma delta x‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (envelope_integrable.const_mul K) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    by_cases hz : F ((M/v)⁻¹*x) = 0
    · simp only [hz,zero_mul,norm_zero]
      exact mul_nonneg hK (envelope_nonneg x)
    have hxM : x ≤ 3*(M/v) := (div_le_iff₀ (div_pos hM hv)).mp (by
      simpa only [div_eq_mul_inv,mul_comm] using (hF hz).2)
    have hphase := PRZZZeroSourceHeight.source_phase_scale T M Q d u v delta x eps
      hT0 hM hQ hd hu hv hx huQ hxM hgap
    have hc := hb A B hA hB hsep hn n (u*v) delta x (3*T^(-eps)) hT hp hpT hd0 hx
      (by positivity) hphase
    dsimp only at hc
    have hnorm := mul_le_mul_of_nonneg_right (hcap ((M/v)⁻¹*x) (by positivity))
      (norm_nonneg (core Psi T (u*v) sigma delta x))
    rw [norm_mul]
    exact (hnorm.trans_eq (one_mul _)).trans (hc.trans_eq (by dsimp [K]; ring)))
  apply hh.trans_eq
  rw [integral_const_mul]
  dsimp [K,J]
  ring

theorem absolute_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (n : ℕ) (F : ℝ → ℂ) (M Q d u v eps : ℝ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 1 ≤ T →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      let sigma := -(A+B)/(Real.log T:ℂ)
      Summable (fun j : ℕ => ‖omitted F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q d u v eps sigma j‖) ∧
        (∑' j : ℕ, ‖omitted F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q d u v eps sigma j‖) ≤
          C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-eps))^n := by
  obtain ⟨C,hC,hb⟩ := row_integral Phi hPhi hcPhi hsPhi S r hS hr
  let p := fun j : ℕ => 1/(((j+1:ℕ):ℝ)^2)
  have hp : Summable p := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let Z := ∑' j : ℕ, p j
  have hZ : 0 ≤ Z := tsum_nonneg (fun j => by dsimp [p]; positivity)
  refine ⟨fun n => 2*C n*Z,fun n => mul_nonneg (mul_nonneg (by norm_num) (hC n)) hZ,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn n F M Q d u v eps hFc hF hcap hT hM hQ hd hu hv hp1 hpT huQ
  let sigma := -(A+B)/(Real.log T:ℂ)
  have hCn := hC n
  let K := 2*C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-eps))^n
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he (j : ℕ) : ‖omitted F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q d u v eps sigma j‖ ≤ K*p j := by
    unfold omitted
    split_ifs with hg
    · have hg' : PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |((j+1:ℕ):ℝ)| := by
        simpa only [abs_of_pos (show (0:ℝ) < (j+1:ℕ) by positivity)] using hg
      have h1 := hb A B hA hB hsep hn n F M Q d u v ((j+1:ℕ):ℝ) eps
        hF hcap hT hM hQ hd hu hv hp1 hpT huQ hg'
      have h2 := hb A B hA hB hsep hn n F M Q d u v (-((j+1:ℕ):ℝ)) eps
        hF hcap hT hM hQ hd hu hv hp1 hpT huQ (by simpa only [abs_neg] using hg')
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

theorem native_power_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps S r rate : ℝ) (heps : 0 < eps) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (F : ℝ → ℂ) (M Q d u v : ℝ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 1 < T → 2 ≤ T^(eps/2) →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ 2*Q →
      let sigma := -(A+B)/(Real.log T:ℂ)
      Summable (omitted F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q d u v eps sigma) ∧
        ‖∑' j : ℕ, omitted F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q d u v eps sigma j‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := absolute_bound Phi hPhi hcPhi hsPhi S r hS hr
  obtain ⟨n,D,hD,hh⟩ := PRZZZeroUniformHeight.source_order_uniform (eps/2) 5 rate r (by linarith) hr
  have hCn := hC n
  refine ⟨C n*D+1,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn F M Q d u v hFc hF hcap hT hwide hM hQ hd hu hv hp1 hpT huQ
  obtain ⟨hs,hb'⟩ := hb A B hA hB hsep hn n F M (2*Q) d u v (eps/2)
    hFc hF hcap hT.le hM (by positivity) hd hu hv hp1 hpT huQ
  have hcut := div_le_div_of_nonneg_right (cutoff_widen T M Q eps (by linarith) hM.le hQ.le hwide) hd.le
  have hm := fun j => omitted_norm_mono F (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) M T Q (2*Q) d u v eps (eps/2)
    (-(A+B)/(Real.log T:ℂ)) hcut j
  have hnative := hs.of_nonneg_of_le (fun j => norm_nonneg _) hm
  refine ⟨hnative.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hnative).trans
    ((hnative.tsum_le_tsum hm hs).trans (hb'.trans _))
  have h := mul_le_mul_of_nonneg_left (hh T hT.le) (hC n)
  rw [Real.rpow_ofNat] at h
  have ht : 0 ≤ T^(-rate) := Real.rpow_nonneg (by linarith) _
  convert (h.trans (show C n*(D*T^(-rate)) ≤ (C n*D+1)*T^(-rate) by nlinarith)) using 1 <;> ring

#print axioms absolute_bound
#print axioms native_power_bound
#print axioms row_integral
end XiPrime8845.PRZZZeroDualGaps
