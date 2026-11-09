import PRZZFamilyMomentOptimal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Derive the exact public witness estimate from explicit Weil and DI
inputs. The auxiliary plateau is constructed, not assumed; the public
all-real-time integral is identified with the proved compact-window moment. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZWitnessBridge
open PRZZCoefficientPolarization
set_option maxHeartbeats 16000000

def seed (x : ℝ) : ℝ := 1-Real.smoothTransition (2*x-1)

theorem seed_smooth : ContDiff ℝ ∞ (fun x => (seed x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)))

theorem seed_antitone : Antitone seed := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (by linarith : 2*x-1 ≤ 2*y-1)) 1

theorem seed_bounds (x : ℝ) : 0 ≤ seed x ∧ seed x ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2*x-1)
  have h1 := Real.smoothTransition.le_one (2*x-1)
  constructor <;> dsimp [seed] <;> linarith

theorem seed_left (x : ℝ) (hx : x ≤ (1/2:ℝ)) : seed x = 1 := by
  simp [seed,Real.smoothTransition.zero_of_nonpos (by linarith : 2*x-1 ≤ 0)]

theorem seed_right (x : ℝ) (hx : 1 ≤ x) : seed x = 0 := by
  simp [seed,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*x-1)]

theorem integral_window (f : ℝ → ℂ) (Phi : ℝ → ℝ)
    (hs : Function.support Phi ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ, f t*(Phi (t/T):ℂ)) = ∫ t in Icc T (2*T), f t*(Phi (t/T):ℂ) := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    by_cases ht : t ∈ Icc T (2*T)
    · simp [ht]
    · have hp : Phi (t/T) = 0 := by
        by_contra hp
        have hh := hs hp
        have h1 := (le_div_iff₀ hT).mp hh.1
        have h2 := (div_le_iff₀ hT).mp hh.2
        exact ht ⟨by linarith,by linarith⟩
      simp [ht,hp])

theorem twisted_eq (theta T : ℝ) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (A B : ℂ) (hT : 0 < T) :
    PRZZ.twistedMoment PRZZ.witness PRZZ.witness theta T Phi A B =
    PRZZMixedPoisson.moment (PRZZ.cutoff theta T)
      (PRZZ.coefficient PRZZ.witness theta T) (PRZZ.coefficient PRZZ.witness theta T)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (fun t => (Phi (t/T):ℂ)) := by
  unfold PRZZ.twistedMoment
  rw [integral_window _ Phi hPhi.2 T hT]
  unfold PRZZMixedPoisson.moment pairing density PRZZAFEDual.leftArg PRZZAFEDual.rightArg
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by ring)

set_option backward.isDefEq.respectTransparency false in
/-- Exact old public input contract, now a theorem relative to Weil/DI.
It covers every theta in (0,4/7), not only the numerical specialization. -/
theorem witness_estimate (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (theta : ℝ) (hTheta0 : 0 < theta) (hTheta1 : theta < 4/7)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (shiftBound poleGap eps : ℝ) (hShift : 0 < shiftBound)
    (hGap : 0 < poleGap) (hEps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖PRZZ.twistedMoment PRZZ.witness PRZZ.witness theta T Phi A B-
        PRZZ.densityGcdMainTerm PRZZ.witness PRZZ.witness theta T Phi A B‖ ≤
        C*T^eps*((PRZZ.length theta T)^(7/4:ℝ)+
          (PRZZ.length theta T)^(7/8:ℝ)*T^(1/2:ℝ)) := by
  obtain ⟨C,hC,h⟩ := PRZZFamilyMomentOptimal.witness_bound hWeil hDI 4 (by norm_num)
    seed Phi seed_smooth seed_antitone (fun x => (seed_bounds x).1) (fun x => (seed_bounds x).2)
    seed_left seed_right hPhi eps shiftBound poleGap hEps hShift.le hGap
  have hgap : 0 < 1-theta := by linarith
  have hh : ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖PRZZ.twistedMoment PRZZ.witness PRZZ.witness theta T Phi A B-
        PRZZ.densityGcdMainTerm PRZZ.witness PRZZ.witness theta T Phi A B‖ ≤
        C*T^eps*((PRZZ.length theta T)^(7/4:ℝ)+
          (PRZZ.length theta T)^(7/8:ℝ)*T^(1/2:ℝ)) := by
    filter_upwards [h,(tendsto_rpow_atTop hTheta0).eventually (eventually_ge_atTop (2:ℝ)),
      (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hTheta0)).eventually (eventually_ge_atTop (1:ℝ)),
      (tendsto_rpow_atTop hgap).eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (2:ℝ)]
      with T h hY hlogY hgapT hT
    refine ⟨hT,?_⟩
    intro A B hA hB hsep
    have hT0 : 0 < T := by linarith
    have hfloor : (PRZZ.cutoff theta T:ℝ) ≤ T^theta := Nat.floor_le (by positivity)
    have hN : 1 ≤ PRZZ.cutoff theta T := by
      unfold PRZZ.cutoff
      apply Nat.le_floor
      convert! (by norm_num : (1:ℝ) ≤ 2).trans hY using 1 <;> norm_num
    have hsum : (PRZZ.cutoff theta T:ℝ)+1 ≤ T := by
      have hp := mul_le_mul_of_nonneg_left hgapT (Real.rpow_nonneg hT0.le theta)
      rw [← Real.rpow_add hT0,show theta+(1-theta)=1 by ring,Real.rpow_one] at hp
      linarith
    have hscale : (PRZZ.cutoff theta T:ℝ) ≤ T^(4/7:ℝ) := hfloor.trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hTheta1.le)
    have hb := h theta (PRZZ.cutoff theta T) A B hTheta0 hN hsum hscale hlogY hfloor hA hB hsep
    rw [twisted_eq theta T Phi hPhi A B hT0,densityGcdMainTerm_eq]
    change ‖PRZZFamilyMomentOptimal.error Phi (PRZZ.cutoff theta T) T A B _ _‖ ≤ _
    apply hb.trans
    unfold PRZZOptimalPowers.target
    have hfloor' : (PRZZ.cutoff theta T:ℝ) ≤ PRZZ.length theta T := hfloor
    have hY0 : 0 ≤ PRZZ.length theta T := by unfold PRZZ.length; positivity
    have hpow1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ PRZZ.cutoff theta T) hfloor'
      (by norm_num : (0:ℝ) ≤ 7/4)
    have hpow2 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ PRZZ.cutoff theta T) hfloor'
      (by norm_num : (0:ℝ) ≤ 7/8)
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (show 0 ≤ C*T^eps by positivity),
      mul_le_mul_of_nonneg_left hpow2 (show 0 ≤ C*T^eps*T^(1/2:ℝ) by positivity)]
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hh
  refine ⟨C,max 2 T0,hC,le_max_left _ _,?_⟩
  intro T hT
  exact (hT0 T ((le_max_right _ _).trans hT)).2

#print axioms seed_smooth
#print axioms seed_antitone
#print axioms seed_bounds
#print axioms seed_left
#print axioms seed_right
#print axioms integral_window
#print axioms twisted_eq
#print axioms witness_estimate
end XiPrime8845.PRZZWitnessBridge
