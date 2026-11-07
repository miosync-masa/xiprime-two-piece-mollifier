import PRZZZeroSpatialPrefix

/-! Sum the actual strict-M spatial boundary integrals over all signed
gaps and the original primitive arithmetic coefficients. No count of
arithmetic profiles or of gap indices is charged. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Finset
namespace XiPrime8845.PRZZZeroBoundarySum
open PRZZDiagonalAssembly
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def row (P : ℝ → ℝ) (Phi : ℝ → ℂ) (L : ℕ) (T u v : ℝ)
    (sigma : ℂ) (delta : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0:ℝ),
    (1-(∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
      PRZZWRowLimit.profile (fun y => (P y:ℂ)) (((2:ℝ)^s/v)⁻¹*x)))*
        PRZZZeroGap.core Phi T (u*v) sigma delta x

def pair (P : ℝ → ℝ) (Phi : ℝ → ℂ) (L : ℕ) (T u v : ℝ)
    (sigma : ℂ) (n : ℕ) : ℂ :=
  row P Phi L T u v sigma ((n+1:ℕ):ℝ)+row P Phi L T u v sigma (-((n+1:ℕ):ℝ))

def total (P : ℝ → ℝ) (Phi : ℝ → ℂ) (L N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if admissible N d u v then
      coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v*
        ∑' n : ℕ, pair P Phi L T u v (alpha+beta) n else 0

theorem pair_bound (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (r theta rate : ℝ) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (T u v : ℝ) (A B : ℂ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < u → u ≤ T^theta → 0 < v → v ≤ T →
      1 ≤ u*v → u*v ≤ T^2 →
      Summable (pair P Phi L T u v ((A+B)/(Real.log T:ℂ))) ∧
      ‖∑' n : ℕ, pair P Phi L T u v ((A+B)/(Real.log T:ℂ)) n‖ ≤ C*T^(-rate) := by
  obtain ⟨D,hD,h⟩ := PRZZZeroSpatialPrefix.native_boundary_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi r theta rate hr htheta hrate
  let f := fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)
  have hf : Summable f := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let Z := ∑' n : ℕ, f n
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by dsimp [f]; positivity)
  refine ⟨2*D*(Z+1),by positivity,?_⟩
  intro L T u v A B hL hT hsep hn hu huT hv hvT hp hpT
  have hb (n : ℕ) : ‖pair P Phi L T u v ((A+B)/(Real.log T:ℂ)) n‖ ≤
      (2*D*T^(-rate))*f n := by
    have h1 := h L T u v ((n+1:ℕ):ℝ) A B hL hT hsep hn hu huT hv hvT hp hpT (by norm_cast; omega)
    have h2 := h L T u v (-((n+1:ℕ):ℝ)) A B hL hT hsep hn hu huT hv hvT hp hpT
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

/-- The exact arithmetic mass, not N cubed, controls the full primitive
grid. The constants are selected before N,L,T and the logarithmic shifts. -/
theorem total_mass_bound (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (r theta rate : ℝ) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (a : ℕ → ℂ) (T : ℝ) (A B : ℂ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T →
      ‖total P Phi L N a T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        PRZZZeroOuterHeight.mass N a (fun _ => 1) (fun _ => 1)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))*C*T^(-rate) := by
  obtain ⟨C,hC,h⟩ := pair_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    r theta rate hr htheta hrate
  refine ⟨C,hC,?_⟩
  intro L N a T A B hL hT hsep hn hNtheta hNT
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
    have hb := (h L T u v A B hL hT hsep hn hu0 (huN.trans hNtheta) hv0
      (hvN.trans hNT) (by nlinarith) (by nlinarith [mul_le_mul (huN.trans hNT) (hvN.trans hNT) hv0.le (by linarith : (0:ℝ) ≤ T)])).2
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
  · simp [had]

/-- Substitute the actual mollifier coefficients and pay for all their
logarithms by selecting the boundary IBP order before height. -/
theorem actual_total_power (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (r S theta rate : ℝ) (hr : 0 < r) (hS : 0 ≤ S)
    (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (T : ℝ) (A B : ℂ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → 1 ≤ N →
      (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖total P Phi L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  let k := 2*PRZZGCoefficient.degree js+3
  obtain ⟨D,hD,hb⟩ := total_mass_bound P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    r theta (rate+(k:ℝ)) hr htheta (by positivity)
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k,by positivity,?_⟩
  intro L N T A B hL hT hN hNtheta hNT hsep hn ha hb'
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hm := PRZZZeroOuterHeight.actual_mass js N (fun _ => 1) (fun _ => 1)
    _ _ S T hN hS (by linarith) hNT (by intro x; norm_num) (by intro x; norm_num) ha hb'
  have hh := hb L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T A B
    hL hT hsep hn hNtheta hNT
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
end XiPrime8845.PRZZZeroBoundarySum
