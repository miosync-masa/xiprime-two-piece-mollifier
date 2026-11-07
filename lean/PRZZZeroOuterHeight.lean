import PRZZZeroOmittedGaps
import PRZZDiagonalMass

/-! Actual primitive arithmetic coefficients multiplying the omitted
zero-frequency gaps.  Their mass is bounded by three harmonic sums;
there is no supplied coefficient-mass or tail-bound premise. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroOuterHeight
open PRZZDiagonalAssembly PRZZZeroOmittedGaps
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def mass (N : ℕ) (a : ℕ → ℂ) (G H : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then ‖coefficient a G H alpha beta d u v‖ else 0

theorem mass_cap (N : ℕ) (a : ℕ → ℂ) (G H : ℝ → ℂ)
    (alpha beta : ℂ) (B S T : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hT : 1 < T) (hNT : (N:ℝ) ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ B)
    (hG : ∀ x, ‖G x‖ ≤ 1) (hH : ∀ x, ‖H x‖ ≤ 1)
    (halpha : |alpha.re| ≤ S/Real.log T) (hbeta : |beta.re| ≤ S/Real.log T) :
    mass N a G H alpha beta ≤ B^2*Real.exp (2*S)*(1+Real.log N)^3 := by
  have hm : mass N a G H alpha beta ≤
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (B^2*Real.exp (2*S))*(1/(d:ℝ))*(1/(u:ℝ))*(1/(v:ℝ)) := by
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro u hu
    apply sum_le_sum
    intro v hv
    by_cases had : admissible N d u v
    · rw [if_pos had]
      have hh := PRZZDiagonalMass.coefficient_envelope N d u v a G H alpha beta B 1 1 S T
        hB (by norm_num) (by norm_num) hS hT hNT
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1
        ha hG hH halpha hbeta had.2.1 had.2.2
      exact hh.trans_eq (by ring)
    · rw [if_neg had]
      positivity
  have he : (∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      (B^2*Real.exp (2*S))*(1/(d:ℝ))*(1/(u:ℝ))*(1/(v:ℝ))) =
      (B^2*Real.exp (2*S))*(SupportTail.harmonic N)^3 := by
    simp only [SupportTail.harmonic,pow_succ,pow_zero,mul_one,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hh : SupportTail.harmonic N ≤ 1+Real.log N := by
    simpa [SupportTail.harmonic,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log N
  have hh0 : 0 ≤ SupportTail.harmonic N := sum_nonneg (fun _ _ => by positivity)
  apply hm.trans
  rw [he]
  gcongr

theorem actual_mass (js : List ℕ) (N : ℕ) (G H : ℝ → ℂ)
    (alpha beta : ℂ) (S T : ℝ) (hN : 1 ≤ N) (hS : 0 ≤ S)
    (hT : 1 < T) (hNT : (N:ℝ) ≤ T)
    (hG : ∀ x, ‖G x‖ ≤ 1) (hH : ∀ x, ‖H x‖ ≤ 1)
    (halpha : |alpha.re| ≤ S/Real.log T) (hbeta : |beta.re| ≤ S/Real.log T) :
    mass N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) G H alpha beta ≤
      Real.exp (2*S)*(1+Real.log N)^(2*PRZZGCoefficient.degree js+3) := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hb : 0 ≤ (Real.log N)^PRZZGCoefficient.degree js := by positivity
  have ha : ∀ n ∈ Finset.Icc 1 N, ‖(PRZZGCoefficient.coefficient js n:ℂ)‖ ≤
      (Real.log N)^PRZZGCoefficient.degree js := by
    intro n hn
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      PRZZGCoefficient.coefficient_bound js N hN n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  apply (mass_cap N _ G H alpha beta _ S T hb hS hT hNT ha hG hH halpha hbeta).trans
  calc
    _ ≤ ((1+Real.log N)^PRZZGCoefficient.degree js)^2*Real.exp (2*S)*(1+Real.log N)^3 := by
      gcongr
      linarith
    _ = _ := by
      rw [show 2*PRZZGCoefficient.degree js+3 = PRZZGCoefficient.degree js*2+3 by omega,
        pow_add,pow_mul]
      ring

def tail (N : ℕ) (a : ℕ → ℂ) (G H F Phi : ℝ → ℂ)
    (T M Q eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then coefficient a G H alpha beta d u v*
      (∑' j : ℕ, omitted F Phi M T Q d u v eps (alpha+beta) j) else 0

/-- Every nonzero arithmetic row supplies its own source-support witness.
No condition is requested on zero-coefficient configurations. -/
theorem tail_mass_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (eps r rate : ℝ) (heps : 0 < eps) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (G H F : ℝ → ℂ)
      (T M Q : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) →
      Function.support G ⊆ Icc (0:ℝ) (2*Q) →
      1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < M → 0 < Q →
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖tail N a G H F Phi T M Q eps alpha beta‖ ≤
        mass N a G H alpha beta*C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := native_power_bound Phi hPhi hcPhi hsPhi eps r rate heps hr
  refine ⟨C,hC,?_⟩
  intro N a G H F T M Q A B hFc hF hcap hG hT hNT hwide hsep hn hM hQ
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
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
    have h := (hb F T M Q d u v A B hFc hF hcap hT hwide hsep hn hM hQ
      (by exact_mod_cast (Finset.mem_Icc.mp hd).1) (by exact_mod_cast (Finset.mem_Icc.mp hu).1)
      (by exact_mod_cast (Finset.mem_Icc.mp hv).1) hp hpT huQ).2
    rw [add_div] at h
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)
  · simp only [if_neg had,norm_zero,zero_mul]
    positivity

/-- Concrete mollifier coefficients are substituted before the IBP order
is chosen.  All harmonic and coefficient logarithms are actually paid for. -/
theorem actual_outer_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (G H F : ℝ → ℂ) (T M Q : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) →
      Function.support G ⊆ Icc (0:ℝ) (2*Q) →
      (∀ x, ‖G x‖ ≤ 1) → (∀ x, ‖H x‖ ≤ 1) →
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < M → 0 < Q →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖tail N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) G H F Phi T M Q eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  let k := 2*PRZZGCoefficient.degree js+3
  obtain ⟨D,hD,hb⟩ := tail_mass_bound Phi hPhi hcPhi hsPhi eps r (rate+(k:ℝ)) heps hr
  refine ⟨Real.exp (2*S)*D*(2:ℝ)^k,by positivity,?_⟩
  intro N G H F T M Q A B hFc hF hcap hGs hG hH hN hT hNT hwide hsep hn hM hQ ha hbeta
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log N ≤ T := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith [Real.log_le_sub_one_of_pos hN0]
  have hm := actual_mass js N G H _ _ S T hN hS hT hNT hG hH ha hbeta
  have hh := hb N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) G H F T M Q A B
    hFc hF hcap hGs hT hNT hwide hsep hn hM hQ
  have hpow : (1+Real.log N)^k ≤ (2*T)^k := by
    gcongr
    linarith
  have ht : T^k*T^(-(rate+(k:ℝ))) = T^(-rate) := by
    rw [← Real.rpow_natCast T k,← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ (Real.exp (2*S)*(1+Real.log N)^k)*D*T^(-(rate+(k:ℝ))) :=
      hh.trans (by gcongr)
    _ ≤ (Real.exp (2*S)*(2*T)^k)*D*T^(-(rate+(k:ℝ))) := by gcongr
    _ = (Real.exp (2*S)*D*(2:ℝ)^k)*(T^k*T^(-(rate+(k:ℝ)))) := by rw [mul_pow]; ring
    _ = _ := by rw [ht]

#print axioms actual_outer_power
#print axioms mass_cap
#print axioms actual_mass
#print axioms tail_mass_bound
end XiPrime8845.PRZZZeroOuterHeight
