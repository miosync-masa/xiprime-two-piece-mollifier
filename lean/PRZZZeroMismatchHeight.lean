import PRZZZeroDualNativeTail

/-! Height-uniform control of the ORIGINAL zeroMismatch. Both true AFE
branches, native strict spatial/gap masks and complete arithmetic cover
are used. This is not yet an optimized bound for the nonzero A* cells. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroMismatchHeight
set_option maxHeartbeats 8000000

theorem actual_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S theta rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.zeroMismatch (fun y => (P y:ℂ)) (fun y => (P y:ℂ))
        Phi (Nat.log 2 N+2) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨Cp,hCp,hp⟩ := PRZZZeroBoundaryIdentity.primal_error_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eps r S theta rate heps hr hS htheta hrate
  obtain ⟨Cb,hCb,hb⟩ := PRZZZeroDualOuter.actual_total_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js r S theta rate hr hS htheta hrate
  obtain ⟨Cg,hCg,hg⟩ := PRZZZeroDualNativeTail.model_gap_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eps S r rate heps hS hr
  refine ⟨Cp+Cb+Cg,by positivity,?_⟩
  filter_upwards [hp,hb,hg,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    (tendsto_rpow_atTop (show 0 < eps/2 by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (4:ℝ)] with T hp hb hg hsmall hwide hT
  intro N A B hN hNtheta hNT hA hB hsep
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
  have h1 := hp N A B hN hNtheta hNT hA hB hsep
  have h2 := hb A B hA hB hsep hn' (PRZZLiteralExhaustion.spatialLength T) N
    le_rfl hT hN hNtheta hNT
  have h3 := hg A B hA hB hsep hn' (PRZZLiteralExhaustion.spatialLength T) N
    hN (by linarith) hNT hwide
  rw [PRZZZeroBoundaryIdentity.mismatch_boundary_gaps P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hT0 ha hbb hs (by simpa only [← add_div] using hn),norm_neg]
  unfold PRZZCentralMainAssembly.branchPair
  dsimp only
  exact ((norm_add_le _ _).trans (add_le_add h1
    ((norm_add_le _ _).trans (add_le_add h2 h3)))).trans_eq (by ring)

/-- Direct original PRZZ length window; N <= T is now supplied rather
than repeated as a premise. The shift separation is still explicit. -/
theorem przz_window_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.zeroMismatch (fun y => (P y:ℂ)) (fun y => (P y:ℂ))
        Phi (Nat.log 2 N+2) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := actual_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps r S (4/7) rate heps hr hS (by norm_num) hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with T hb hT
  intro N A B hN hNT hA hB hsep
  have hNT' : (N:ℝ) ≤ T := hNT.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  exact hb N A B hN hNT hNT' hA hB hsep

#print axioms przz_window_power
#print axioms actual_power
end XiPrime8845.PRZZZeroMismatchHeight
