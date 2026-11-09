import PRZZZeroDualOuter

/-! Uniform zero-frequency spatial boundaries for arbitrary bounded coefficients.
The genuine dual Gamma profile is supplied by the original dual IBP theorem.
The common coefficient cap precedes height and the entire coefficient sequence. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZClassZeroBoundary
open PRZZZeroBoundarySum
set_option maxHeartbeats 8000000

theorem primal_power (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (H : ℝ) (hH : 0 ≤ H) (r S theta rate : ℝ) (hr : 0 < r) (hS : 0 ≤ S)
    (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (a : ℕ → ℂ) (T : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ H) →
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → 1 ≤ N →
      (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖total P Phi L N a T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  let k : ℕ := 3
  obtain ⟨D,hD,hb⟩ := PRZZZeroBoundarySum.total_mass_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    r theta (rate+(k:ℝ)) hr htheta (by positivity)
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k*(H^2+1),by positivity,?_⟩
  intro L N a T A B hcoef hL hT hN hNtheta hNT hsep hn ha hb'
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hm := PRZZZeroOuterHeight.mass_cap N a (fun _ => 1) (fun _ => 1)
    _ _ H S T hH hS (by linarith) hNT hcoef (by intro x; norm_num) (by intro x; norm_num) ha hb'
  have hh := hb L N a T A B
    hL hT hsep hn hNtheta hNT
  have hpow : (1+Real.log N)^k ≤ (2*T)^k := by gcongr; linarith
  have ht : T^k*T^(-(rate+(k:ℝ))) = T^(-rate) := by
    rw [← Real.rpow_natCast T k,← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ (H^2*Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) := hh.trans (by gcongr)
    _ ≤ (H^2*Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k*H^2)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ ≤ _ := by rw [ht]; gcongr; nlinarith

theorem dual_power (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (H : ℝ) (hH : 0 ≤ H) (r S theta rate : ℝ) (hr : 0 < r) (hS : 0 ≤ S)
    (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L N : ℕ) (a : ℕ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ H) →
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → 1 ≤ N →
      (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖total P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L N a T
        (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  let k : ℕ := 3
  obtain ⟨D,hD,hb⟩ := PRZZZeroDualOuter.total_mass_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    S r theta (rate+(k:ℝ)) hS hr htheta (by positivity)
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k*(H^2+1),by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn L N a hcoef hL hT hN hNtheta hNT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hz (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hlogT]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hlogT.le
  have ha : |(-(B/(Real.log T:ℂ))).re| ≤ S/Real.log T := by
    simpa only [Complex.neg_re,abs_neg] using hz B hB
  have hb' : |(-(A/(Real.log T:ℂ))).re| ≤ S/Real.log T := by
    simpa only [Complex.neg_re,abs_neg] using hz A hA
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hm := PRZZZeroOuterHeight.mass_cap N a (fun _ => 1) (fun _ => 1)
    _ _ H S T hH hS (by linarith) hNT hcoef (by intro x; norm_num) (by intro x; norm_num) ha hb'
  have hh := hb A B hA hB hsep hn L N a
    hL hT hNtheta hNT
  have hpow : (1+Real.log N)^k ≤ (2*T)^k := by gcongr; linarith
  have ht : T^k*T^(-(rate+(k:ℝ))) = T^(-rate) := by
    rw [← Real.rpow_natCast T k,← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ (H^2*Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) := hh.trans (by gcongr)
    _ ≤ (H^2*Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k*H^2)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ ≤ _ := by rw [ht]; gcongr; nlinarith

#print axioms primal_power
#print axioms dual_power
end XiPrime8845.PRZZClassZeroBoundary
