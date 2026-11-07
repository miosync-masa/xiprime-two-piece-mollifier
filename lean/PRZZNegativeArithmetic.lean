import PRZZActualAStar
import PRZZSignedCentral

/-! Exact negative-h arithmetic reflection. Delta, both real phase
coordinates, and ONLY the spatial profile are reflected. No conjugation
of arithmetic coefficients or shifts is made. This closes the negative
arithmetic estimate; transfer through the signed literal's coordinate
change and Mellin/Fubini integrals is a separate interface. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory
namespace XiPrime8845.PRZZNegativeArithmetic
open PRZZAStar PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation PRZZKloostermanInputs
open PRZZActualAggregate
set_option maxHeartbeats 7000000

def reflect (F : ℝ → ℂ) (x : ℝ) : ℂ := F (-x)
def flip (q : ℤ × ℕ) : ℤ × ℕ := (-q.1,q.2)

theorem flip_mem (d : ℕ) (D H : ℝ) (q : ℤ × ℕ) :
    flip q ∈ frequencies d D H ↔ q ∈ frequencies d D H := by
  simp only [frequencies,product_eq_sprod,mem_product,flip,PRZZAStar.delta_cutoff_iff,
    Int.cast_neg,abs_neg]

theorem flip_sum (d : ℕ) (D H : ℝ) (f : ℤ × ℕ → ℂ) :
    (∑ q ∈ frequencies d D H, f (flip q)) = ∑ q ∈ frequencies d D H, f q := by
  apply sum_bij (fun q _ => flip q)
  · intro q hq; exact (flip_mem d D H q).mpr hq
  · intro q hq r hr he
    have h1 := congrArg (fun z : ℤ × ℕ => z.1) he
    have h2 := congrArg (fun z : ℤ × ℕ => z.2) he
    exact Prod.ext (neg_injective h1) h2
  · intro q hq
    refine ⟨flip q,(flip_mem d D H q).mpr hq,?_⟩
    simp [flip]
  · intro q hq; rfl

theorem signed_expanded (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedSum N d D H a F1 F2 FM alpha beta x y t =
      ∑ i ∈ pairs N d, ∑ q ∈ frequencies d D H,
        pairCoeff d a F1 F2 FM alpha beta x t i*PRZZNuCoefficient.oscillation x y q*
          PRZZKloostermanInputs.e (-(freq q:ℝ)*inverseResidue i.2 i.1/i.2) := by
  exact (PRZZNuCoefficient.separate (frequencies d D H) (pairs N d) x y
    (pairCoeff d a F1 F2 FM alpha beta x t)
    (fun i k => PRZZKloostermanInputs.e (-(k:ℝ)*inverseResidue i.2 i.1/i.2))).symm

def negativeSum (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  ∑ i ∈ pairs N d, ∑ q ∈ frequencies d D H,
    pairCoeff d a F1 F2 FM alpha beta x t i*
      (PRZZKloostermanInputs.e ((q.2:ℝ)*x)*PRZZKloostermanInputs.e ((q.1:ℝ)*y/(2*Real.pi)))*
      PRZZKloostermanInputs.e ((q.2:ℝ)*(q.1:ℝ)*inverseResidue i.2 i.1/i.2)

theorem negative_reflection (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    negativeSum N d D H a F1 F2 FM alpha beta x y t =
      signedSum N d D H a F1 F2 (reflect FM) alpha beta (-x) (-y) t := by
  rw [signed_expanded]
  unfold negativeSum
  symm
  apply sum_congr rfl
  intro i hi
  rw [← flip_sum d D H]
  apply sum_congr rfl
  intro q hq
  have hc : pairCoeff d a F1 F2 (reflect FM) alpha beta (-x) t i =
      pairCoeff d a F1 F2 FM alpha beta x t i := by
    simp [pairCoeff,reflect]
  have ho : PRZZNuCoefficient.oscillation (-x) (-y) (flip q) =
      PRZZKloostermanInputs.e ((q.2:ℝ)*x)*PRZZKloostermanInputs.e ((q.1:ℝ)*y/(2*Real.pi)) := by
    simp [PRZZNuCoefficient.oscillation,flip]
  have hp : -((freq (flip q):ℝ))*inverseResidue i.2 i.1/i.2 =
      (q.2:ℝ)*(q.1:ℝ)*inverseResidue i.2 i.1/i.2 := by
    simp [freq,flip]
  rw [hc,ho,hp]

/-- The negative source phases, with the same arithmetic coefficient,
including its conjugate in the second slot. -/
def amplitudeMinus (d : ℕ) (a : ℕ → ℂ) (F1 F2 FM W : ℝ → ℂ)
    (alpha beta : ℂ) (x y : ℝ) (z : Index) : ℂ :=
  PRZZFilteredResidual.signedPrefactor a F1 F2 d beta alpha z (-(z.2.2:ℤ))*
    PRZZKloostermanInputs.e ((z.2.2:ℝ)*x)*FM (x*z.1.2)/(x:ℂ)^(alpha+beta)*
    PRZZKloostermanInputs.e ((z.2.1:ℝ)*y/(2*Real.pi))*W (2*Real.pi*x/y)

theorem amplitude_negative (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    (∑ z ∈ indices N d D H, amplitudeMinus d a F1 F2 FM W alpha beta x y z*
      twist z.1.1 t*twist z.1.2 t) =
      W (2*Real.pi*x/y)/((d:ℂ)*(x:ℂ)^(alpha+beta))*
        negativeSum N d D H a F1 F2 FM alpha beta x y t := by
  change (∑ z ∈ (pairs N d).product (frequencies d D H), _) = _
  simp only [product_eq_sprod,sum_product]
  unfold negativeSum
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  simp only [amplitudeMinus,PRZZFilteredResidual.signedPrefactor,PRZZUnfrozenPoisson.arithmetic,
    pairCoeff,Int.cast_neg,Int.cast_natCast,neg_mul,neg_neg,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Weil and DI now bound the ACTUAL negative arithmetic phase, not an
assumed negative-source envelope. Constants precede all real coordinates. -/
theorem negative_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖negativeSum N d D H (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM alpha beta x y t‖ ≤
        totalBudget C w caps js eps eta b T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K*(1+|t|) := by
  have hrM : Continuous (reflect FM) := hM.comp continuous_neg
  have hrcM : HasCompactSupport (reflect FM) := hcM.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨caps,w,C,hC,hw,h⟩ := PRZZActualAggregate.signedSum_bound hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 (reflect FM) hf hc hF hcF hrM hrcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d T Q D H x y t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb'
  rw [negative_reflection]
  exact h N d T Q D H (-x) (-y) t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb'

#print axioms flip_mem
#print axioms flip_sum
#print axioms signed_expanded
#print axioms negative_reflection
#print axioms amplitude_negative
#print axioms negative_weil_di
end XiPrime8845.PRZZNegativeArithmetic
