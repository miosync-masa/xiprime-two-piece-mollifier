import PRZZNativeComponents
import PRZZAllPoissonAFE

/-! Exact exhaustive-component form of the ORIGINAL AFE error. All five
actual Poisson components, both branches, zeroPair and gammaDefect are
retained. Integrals of collective fields are used: no unproved Fubini or
separate integrability of an infinite Fourier component is a premise. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZExhaustiveAFEError
open PRZZNativeComponents PRZZCoupledAFE
set_option maxHeartbeats 6000000

def field (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  component .central L J N F (fun _ => 1) (fun _ => 1) a alpha beta t+
    component .tail L J N F (fun _ => 1) (fun _ => 1) a alpha beta t-
    component .boundary L J N F (fun _ => 1) (fun _ => 1) a alpha beta t+
    component .freeze L J N F (fun _ => 1) (fun _ => 1) a alpha beta t+
    component .outside L J N F (fun _ => 1) (fun _ => 1) a alpha beta t

theorem field_eq (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    field L J N F a alpha beta t =
      PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t :=
  (family_decomposition L J N F (fun _ => 1) (fun _ => 1) a alpha beta t).symm

def componentModel (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  diagonalMain N a alpha beta T phi+
    (((∫ t in Icc T (2*T), phi t*field L J N F a alpha beta t)+
      ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
        field L J N F a (-beta) (-alpha) t)-
      PRZZZeroCoupled.zeroPair N a alpha beta T phi)+
    ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N a alpha beta t

theorem model_eq (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) :
    componentModel L J N F a alpha beta T phi =
      PRZZAllPoissonAFE.model L J N F a alpha beta T phi := by
  unfold componentModel PRZZAllPoissonAFE.model
  simp_rw [field_eq]

def moment (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  ∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi a a N t *
    (riemannZeta (PRZZAFEDual.leftArg alpha t)*riemannZeta (PRZZAFEDual.rightArg beta t))

/-- The full original moment-minus-AFE-model error, with no asserted
analytic smallness of one of its unresolved Fourier components. -/
theorem original_error_eq (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) :
    moment N a alpha beta T phi-PRZZAllPoissonAFE.model L J N F a alpha beta T phi =
      (moment N a alpha beta T phi-diagonalMain N a alpha beta T phi)-
        (((∫ t in Icc T (2*T), phi t*field L J N F a alpha beta t)+
          ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
            field L J N F a (-beta) (-alpha) t)-
          PRZZZeroCoupled.zeroPair N a alpha beta T phi)-
        ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  rw [← model_eq]
  unfold componentModel
  ring

/-- The exact component identity carries the existing sharp AFE error
limit to arbitrary L-dependent central-frequency cutoffs. This remains
an AFE reduction, not an optimized bound on every component in field. -/
theorem scaled_full_error_limit (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (js : List ℕ) (S r delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) → ∀ J : ℕ → ℕ, ∃ E : ℂ,
      Tendsto (fun L : ℕ =>
        moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi-
        componentModel L (J L) N F (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZAllPoissonAFE.scaled_afe_limit F hF hlo hhi js S r delta hS hr hd
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep N hN hNT phi P hphi hP hp J
  obtain ⟨E,hlim,hbound⟩ := h A B hA hB hsep N hN hNT phi P hphi hP hp J
  refine ⟨E,?_,hbound⟩
  simpa only [moment,model_eq] using hlim

#print axioms field_eq
#print axioms model_eq
#print axioms original_error_eq
#print axioms scaled_full_error_limit
end XiPrime8845.PRZZExhaustiveAFEError
