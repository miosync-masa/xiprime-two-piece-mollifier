import PRZZWitnessBasis
import PRZZDiagonalMass

/-! Actual diagonal contour-error mass for the whole witness basis box.
Constants precede theta, height, cutoff values and complex profile vectors.
This evaluates that mass only, not the full Weil/DI moment error. -/
noncomputable section
open Complex MeasureTheory Finset Set Filter Topology
namespace XiPrime8845.PRZZWitnessMass
open PRZZWitnessBasis PRZZCoefficientPolarization PRZZDiagonalAssembly
set_option maxHeartbeats 4000000

def arithmeticLabels (i : Fin 7) : List ℕ := if i.val < 4 then [] else [0,0]
def profileDegree : Fin 7 → ℕ := ![1,2,3,4,1,2,3]

/-- All T dependence is in this explicit scalar profile. The arithmetic
labels supplied to the existing Weil/DI row theorem remain fixed. -/
def profileWeight (theta T : ℝ) (i : Fin 7) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ (n:ℝ) ≤ PRZZ.length theta T then
    let L := Real.log (PRZZ.length theta T)
    let u := Real.log (PRZZ.length theta T/n)/L
    (3*u^(profileDegree i)/(if i.val < 4 then 1 else L^2):ℝ)
  else 0

theorem basis_arithmetic_factorization (theta T : ℝ) (i : Fin 7) (n : ℕ) :
    basis theta T i n = (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ)*
      profileWeight theta T i n := by
  fin_cases i <;> by_cases hs : 1 ≤ n ∧ (n:ℝ) ≤ PRZZ.length theta T <;>
    simp [basis,profiles,conreyMonomial,fengMonomial,arithmeticLabels,profileDegree,
      profileWeight,PRZZ.coefficient,PRZZGCoefficient.coefficient,PRZZ.fengArithmetic,hs] <;>
    push_cast <;> ring

theorem uniform_mass (U1 U2 S : ℝ) (hU1 : 0 ≤ U1) (hU2 : 0 ≤ U2) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta T : ℝ) (N : ℕ) (z : Fin 7 → ℂ)
      (F1 F2 : ℝ → ℂ) (alpha beta : ℂ),
      0 < theta → 2 ≤ T → 1 ≤ N → (N:ℝ) ≤ T →
      (∀ i, ‖z i‖ ≤ 2) → (∀ x, ‖F1 x‖ ≤ U1) → (∀ x, ‖F2 x‖ ≤ U2) →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (family (basis theta T) z) F1 F2 alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^2 := by
  obtain ⟨D,hD,h⟩ := PRZZDiagonalMass.mass_envelope
  let B := U1*U2*84^2*Real.exp (2*S)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D*(B+1),by positivity,?_⟩
  intro theta T N z F1 F2 alpha beta htheta hT hN hNT hz hF1 hF2 ha hb
  have hc := h N T B (family (basis theta T) z) F1 F2 alpha beta hN (by linarith) hB
    (by
      intro d hd u hu v hv had
      exact PRZZDiagonalMass.coefficient_envelope N d u v _ F1 F2 alpha beta
        84 U1 U2 S T (by norm_num) hU1 hU2 hS (by linarith) hNT
        (mem_Icc.mp hd).1 (mem_Icc.mp hu).1 (mem_Icc.mp hv).1
        (fun n hn => family_coefficient_bound theta T htheta hT z hz n)
        hF1 hF2 ha hb had.2.1 had.2.2)
  apply hc.trans
  gcongr
  linarith

/-- The actual fixed witness, not an unspecified bounded coefficient. -/
theorem witness_mass (U1 U2 S : ℝ) (hU1 : 0 ≤ U1) (hU2 : 0 ≤ U2) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta T : ℝ) (N : ℕ)
      (F1 F2 : ℝ → ℂ) (alpha beta : ℂ),
      0 < theta → 2 ≤ T → 1 ≤ N → (N:ℝ) ≤ T →
      (∀ x, ‖F1 x‖ ≤ U1) → (∀ x, ‖F2 x‖ ≤ U2) →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (PRZZ.coefficient PRZZ.witness theta T) F1 F2 alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^2 := by
  obtain ⟨C,hC,h⟩ := uniform_mass U1 U2 S hU1 hU2 hS
  refine ⟨C,hC,?_⟩
  intro theta T N F1 F2 alpha beta htheta hT hN hNT hF1 hF2 ha hb
  rw [witness_expansion]
  exact h theta T N coordinates F1 F2 alpha beta htheta hT hN hNT
    (fun i => (coordinates_unit i).trans (by norm_num)) hF1 hF2 ha hb

#print axioms uniform_mass
#print axioms witness_mass
#print axioms basis_arithmetic_factorization

/-- The actual natural cutoff, not an unrounded surrogate, has o(T)
target budget at tau=2.5e-7. Constants and any further losses are separate. -/
theorem normalized_cutoff_target :
    Tendsto (fun T : ℝ => T^(1/4000000:ℝ)*PRZZOptimalPowers.target
      (PRZZ.cutoff (4/7-1/1000000) T) T/T) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ witness_normalized_envelope
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    unfold PRZZOptimalPowers.target
    positivity
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hlen : 0 ≤ PRZZ.length (4/7-1/1000000) T := Real.rpow_nonneg hT.le _
    have hcut : (PRZZ.cutoff (4/7-1/1000000) T:ℝ) ≤
        PRZZ.length (4/7-1/1000000) T := Nat.floor_le hlen
    unfold PRZZOptimalPowers.target
    rw [mul_comm (PRZZ.length (4/7-1/1000000) T ^ (7/8:ℝ))]
    gcongr

#print axioms normalized_cutoff_target
end XiPrime8845.PRZZWitnessMass
