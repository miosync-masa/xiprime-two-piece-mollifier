import PRZZClassZeroBoundary
import PRZZClassZeroPrimalGap
import PRZZMixedPoisson

/-! Actual zeroMismatch with uniform bounded coefficients. Spatial boundary
and omitted gaps in both true AFE branches are evaluated before polarization.
This does not estimate the separate nonzero Fourier/freezing remainders. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZClassZeroCorrection
open PRZZZeroBoundarySum
set_option maxHeartbeats 8000000

theorem primal_error_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S theta rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (a : ℕ → ℂ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖total P Phi (PRZZLiteralExhaustion.spatialLength T) N
          a T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))+
        PRZZZeroNativeCompletion.gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2)
          (PRZZLiteralExhaustion.spatialLength T) N a
            T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  have hPc : Continuous P := by
    simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hP.continuous
  obtain ⟨C,hC,hb⟩ := PRZZClassZeroBoundary.primal_power P hPc hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    Hcap hHcap r S theta rate hr hS htheta hrate
  obtain ⟨D,hD,hg⟩ := PRZZClassZeroPrimalGap.model_gap_eventually P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi Hcap hHcap eps r S rate heps hr hS
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hg,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    Filter.eventually_ge_atTop (4:ℝ)] with T hg hsmall hT
  intro N a A B hcoef hN hNtheta hNT hA hB hsep
  have hlog : 0 < Real.log T := by linarith [hsmall.1]
  have hz (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hlog]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hlog.le
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  have h1 := hb _ N a T A B hcoef le_rfl hT hN hNtheta hNT hsep hn (hz A hA) (hz B hB)
  have h2 := hg (PRZZLiteralExhaustion.spatialLength T) N a A B hcoef hN hNT hA hB hsep
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

theorem actual_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps r S theta rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (a : ℕ → ℂ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.zeroMismatch (fun y => (P y:ℂ)) (fun y => (P y:ℂ))
        Phi (Nat.log 2 N+2) N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨Cp,hCp,hp⟩ := primal_error_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi Hcap hHcap eps r S theta rate heps hr hS htheta hrate
  obtain ⟨Cb,hCb,hb⟩ := PRZZClassZeroBoundary.dual_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi Hcap hHcap r S theta rate hr hS htheta hrate
  obtain ⟨Cg,hCg,hg⟩ := PRZZClassZeroTail.model_gap_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi Hcap hHcap eps S r rate heps hS hr
  refine ⟨Cp+Cb+Cg,by positivity,?_⟩
  filter_upwards [hp,hb,hg,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    (tendsto_rpow_atTop (show 0 < eps/2 by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (4:ℝ)] with T hp hb hg hsmall hwide hT
  intro N a A B hcoef hN hNtheta hNT hA hB hsep
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4 := (hsmall.2 A hA).trans (by norm_num)
  have hbb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4 := (hsmall.2 B hB).trans (by norm_num)
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  have hn' : ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by simpa only [neg_div,norm_neg] using hn
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hlog.ne')
  have h1 := hp N a A B hcoef hN hNtheta hNT hA hB hsep
  have h2 := hb A B hA hB hsep hn' (PRZZLiteralExhaustion.spatialLength T) N a hcoef
    le_rfl hT hN hNtheta hNT
  have h3 := hg A B hA hB hsep hn' (PRZZLiteralExhaustion.spatialLength T) N a hcoef
    hN (by linarith) hNT hwide
  rw [PRZZZeroBoundaryIdentity.mismatch_boundary_gaps P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi N a T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hT0 ha hbb hs (by simpa only [← add_div] using hn),norm_neg]
  unfold PRZZCentralMainAssembly.branchPair
  dsimp only
  exact ((norm_add_le _ _).trans (add_le_add h1
    ((norm_add_le _ _).trans (add_le_add h2 h3)))).trans_eq (by ring)

theorem combine_cap (N : ℕ) (c d : ℕ → ℂ) (H : ℝ) (_hH : 0 ≤ H)
    (hc : ∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H)
    (hd : ∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ∀ n ∈ Finset.Icc 1 N, ‖PRZZCoefficientPolarization.combine c d z n‖ ≤ 2*H := by
  intro n hn
  unfold PRZZCoefficientPolarization.combine
  apply (norm_add_le _ _).trans
  rw [norm_mul,hz,one_mul]
  linarith [hc n hn,hd n hn]

theorem lift_bound (Q : (ℕ → ℂ) → ℂ) (c d : ℕ → ℂ) (R : ℝ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ‖Q (PRZZCoefficientPolarization.combine c d z)‖ ≤ R) :
    ‖PRZZMixedPoisson.lift Q c d‖ ≤ R := by
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h I (by simp)
  have h4 := h (-I) (by simp)
  have h3' : ‖I*Q (PRZZCoefficientPolarization.combine c d I)‖ ≤ R := by
    simpa only [norm_mul,norm_I,one_mul] using h3
  have h4' : ‖I*Q (PRZZCoefficientPolarization.combine c d (-I))‖ ≤ R := by
    simpa only [norm_mul,norm_I,one_mul] using h4
  unfold PRZZMixedPoisson.lift
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  have hn := norm_sub_le
    (Q (PRZZCoefficientPolarization.combine c d 1)-Q (PRZZCoefficientPolarization.combine c d (-1))+
      I*Q (PRZZCoefficientPolarization.combine c d I))
    (I*Q (PRZZCoefficientPolarization.combine c d (-I)))
  have hn2 := norm_add_le
    (Q (PRZZCoefficientPolarization.combine c d 1)-Q (PRZZCoefficientPolarization.combine c d (-1)))
    (I*Q (PRZZCoefficientPolarization.combine c d I))
  have hn3 := norm_sub_le (Q (PRZZCoefficientPolarization.combine c d 1))
    (Q (PRZZCoefficientPolarization.combine c d (-1)))
  apply (div_le_div_of_nonneg_right (show ‖Q (PRZZCoefficientPolarization.combine c d 1)-
    Q (PRZZCoefficientPolarization.combine c d (-1))+I*Q (PRZZCoefficientPolarization.combine c d I)-
      I*Q (PRZZCoefficientPolarization.combine c d (-I))‖ ≤ 4*R by linarith) (by norm_num)).trans_eq
  ring

/-- Both independent coefficient slots may vary with height after H is fixed.
This is the actual original zeroMismatch polarized after both Gamma branches
and all spatial/gap corrections have been evaluated. -/
theorem mixed_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (H eps r S theta rate : ℝ) (hH : 0 ≤ H)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (c d : ℕ → ℂ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.zeroMismatch
        (fun y => (P y:ℂ)) (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,h⟩ := actual_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    (2*H) (by positivity) eps r S theta rate heps hr hS htheta hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro N c d A B hc hd hN hNtheta hNT hA hB hsep
  apply lift_bound
  intro z hz
  exact h N _ A B (combine_cap N c d H hH hc hd z hz) hN hNtheta hNT hA hB hsep

/-- The full radius-two witness coordinate box, with the actual T-dependent
seven-vector basis. In particular all 49 ordered basis pairs are covered. -/
theorem family_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (theta : ℝ) (z w : Fin 7 → ℂ) (N : ℕ) (A B : ℂ),
      0 < theta → (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let c := PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) z
      let d := PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) w
      ‖PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.zeroMismatch
        (fun y => (P y:ℂ)) (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2) N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,h⟩ := mixed_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    84 eps r S (4/7) rate (by norm_num) heps hr hS (by norm_num) hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro theta z w N A B htheta hz hw hN hscale hA hB hsep
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by norm_num : (4/7:ℝ) ≤ 1))
  exact h N _ _ A B
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT z hz n)
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT w hw n)
    hN hscale hNT hA hB hsep

/-- The remaining three terms are the original positive, negative and tail
collectors, with the same strict masks and the same genuine dual profile. -/
def nonzeroResidual (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
    PRZZCentralMainAssembly.positivePart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta+
  PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
    PRZZCentralMainAssembly.negativePart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta+
  PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
    PRZZCentralMainAssembly.tailPart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta

theorem arithmetic_split (P F Phi : ℝ → ℂ) (K J N : ℕ) (c d : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.arithmeticResidual
      P F Phi K J N a T eps alpha beta) c d =
    PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.zeroMismatch
      P F Phi K N a T eps alpha beta) c d+
    PRZZMixedPoisson.lift (fun a => nonzeroResidual P F Phi K J N a T eps alpha beta) c d := by
  unfold PRZZMixedPoisson.lift PRZZCentralMainAssembly.arithmeticResidual nonzeroResidual
  ring

/-- Insert the evaluated zero correction into the original arithmetic
residual; only its actual nonzero collectors remain on the right. -/
theorem arithmetic_bound (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (H eps r S theta rate : ℝ) (hH : 0 ≤ H)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (J N : ℕ) (c d : ℕ → ℂ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let F := fun y => (P y:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.arithmeticResidual
        F F Phi (Nat.log 2 N+2) J N a T eps alpha beta) c d‖ ≤
      ‖PRZZMixedPoisson.lift (fun a => nonzeroResidual F F Phi (Nat.log 2 N+2) J N a T eps alpha beta) c d‖+
        C*T^(-rate) := by
  obtain ⟨C,hC,h⟩ := mixed_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    H eps r S theta rate hH heps hr hS htheta hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro J N c d A B hc hd hN hNtheta hNT hA hB hsep
  dsimp only
  rw [arithmetic_split]
  exact ((norm_add_le _ _).trans (add_le_add
    (h N c d A B hc hd hN hNtheta hNT hA hB hsep) le_rfl)).trans_eq (by ring)

#print axioms arithmetic_split
#print axioms arithmetic_bound
#print axioms family_power
#print axioms combine_cap
#print axioms lift_bound
#print axioms mixed_power
#print axioms primal_error_power
#print axioms actual_power
end XiPrime8845.PRZZClassZeroCorrection
