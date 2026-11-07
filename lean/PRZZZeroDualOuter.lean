import PRZZZeroDualGaps
import PRZZZeroBoundaryIdentity

/-! Full primitive coefficient mass for the genuine dual spatial boundary.
The source shift is reflected; the Gamma multiplier keeps the original shifts. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroDualOuter
open PRZZDiagonalAssembly PRZZZeroBoundarySum
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem pair_bound (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (S r theta rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L : ℕ) (u v : ℝ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → 0 < u → u ≤ T^theta → 0 < v → v ≤ T →
      1 ≤ u*v → u*v ≤ T^2 →
      Summable (pair P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L T u v (-(A+B)/(Real.log T:ℂ))) ∧
      ‖∑' n : ℕ, pair P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L T u v (-(A+B)/(Real.log T:ℂ)) n‖ ≤ C*T^(-rate) := by
  obtain ⟨D,hD,h⟩ := PRZZZeroDualBoundary.native_boundary_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi S r theta rate hS hr htheta hrate
  let f := fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)
  have hf : Summable f := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let Z := ∑' n : ℕ, f n
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by dsimp [f]; positivity)
  refine ⟨2*D*(Z+1),by positivity,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep hn L u v hL hT hu huT hv hvT hp hpT
  have hb (n : ℕ) : ‖pair P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L T u v (-(A+B)/(Real.log T:ℂ)) n‖ ≤
      (2*D*T^(-rate))*f n := by
    have h1 := h A B hA hB hsep hn L u v ((n+1:ℕ):ℝ) hL hT hu huT hv hvT hp hpT (by norm_cast; omega)
    have h2 := h A B hA hB hsep hn L u v (-((n+1:ℕ):ℝ)) hL hT hu huT hv hvT hp hpT
      (by rw [abs_neg,abs_of_nonneg (by positivity)]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    simp only [abs_neg,abs_of_nonneg (show (0:ℝ) ≤ (n+1:ℕ) by positivity)] at h1 h2
    exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by dsimp [row,f]; ring)
  have hs := (hf.mul_left (2*D*T^(-rate))).of_norm_bounded hb
  refine ⟨hs,?_⟩
  have hh := (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum hb
    (hf.mul_left (2*D*T^(-rate))))
  rw [tsum_mul_left] at hh
  change _ ≤ 2*D*T^(-rate)*Z at hh
  have ht : 0 ≤ 2*D*T^(-rate) := by positivity
  nlinarith

theorem total_mass_bound (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (S r theta rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L N : ℕ) (a : ℕ → ℂ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖total P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L N a T (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤
        PRZZZeroOuterHeight.mass N a (fun _ => 1) (fun _ => 1)
          (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))*C*T^(-rate) := by
  obtain ⟨C,hC,h⟩ := pair_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    S r theta rate hS hr htheta hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep hn L N a hL hT hNtheta hNT
  unfold total PRZZZeroOuterHeight.mass
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
  · simp only [if_pos had,norm_mul,← add_div]
    have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    have huN : (u:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hu).2
    have hvN : (v:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hv).2
    have hu1 : (1:ℝ) ≤ u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv1 : (1:ℝ) ≤ v := by exact_mod_cast (mem_Icc.mp hv).1
    have hb := (h A B hA hB hsep hn L u v hL hT hu0 (huN.trans hNtheta) hv0
      (hvN.trans hNT) (by nlinarith) (by nlinarith [mul_le_mul (huN.trans hNT) (hvN.trans hNT) hv0.le (by linarith : (0:ℝ) ≤ T)])).2
    rw [show -(B/(Real.log T:ℂ))+-(A/(Real.log T:ℂ)) = -(A+B)/(Real.log T:ℂ) by ring]
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
  · simp [had]


theorem actual_total_power (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (r S theta rate : ℝ) (hr : 0 < r) (hS : 0 ≤ S)
    (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (L N : ℕ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → 1 ≤ N →
      (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖total P (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T
        (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))‖ ≤ C*T^(-rate) := by
  let k := 2*PRZZGCoefficient.degree js+3
  obtain ⟨D,hD,hb⟩ := total_mass_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    S r theta (rate+(k:ℝ)) hS hr htheta (by positivity)
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn L N hL hT hN hNtheta hNT
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
  have hm := PRZZZeroOuterHeight.actual_mass js N (fun _ => 1) (fun _ => 1)
    _ _ S T hN hS (by linarith) hNT (by intro x; norm_num) (by intro x; norm_num) ha hb'
  have hh := hb A B hA hB hsep hn L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    hL hT hNtheta hNT
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

#print axioms actual_total_power
#print axioms pair_bound
#print axioms total_mass_bound
end XiPrime8845.PRZZZeroDualOuter

