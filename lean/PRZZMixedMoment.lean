import PRZZMixedPoisson

/-! Return the complete mixed Poisson field to the actual moment minus
its Gamma diagonal arithmetic kernel. The AFE error limit is evaluated;
the collective field is retained, not assumed to satisfy a sharp bound.
All height-dependent witness basis combinations share one coefficient cap. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ContDiff
namespace XiPrime8845.PRZZMixedMoment
open PRZZCoefficientPolarization PRZZMixedPoisson
set_option maxHeartbeats 5000000

theorem diagonal_eq (N : ℕ) (c d : ℕ → ℂ) (a b : ℂ) (T : ℝ) (phi : ℝ → ℂ) :
    lift (fun e => PRZZCoupledAFE.diagonalMain N e a b T phi) c d =
      arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N a b T phi) c d := by
  have h := arithmetic_polarization N (PRZZDiagonalKernel.diagonalKernel N a b T phi) c d
  unfold PRZZMixedPoisson.lift
  simp_rw [PRZZDiagonalKernel.diagonalMain_eq]
  linear_combination -h/4

/-- Exact finite-cutoff equation, with both branches, all five collective
components, zeroPair and gammaDefect. No separate Fourier Fubini premise. -/
theorem moment_components_eq (L J N : ℕ) (F : ℝ → ℂ) (c d : ℕ → ℂ)
    (a b : ℂ) (T : ℝ) (phi : ℝ → ℂ) :
    moment N c d a b T phi-
        arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N a b T phi) c d =
      lift (fun e => components L J N F e a b T phi) c d+
        (moment N c d a b T phi-model L J N F c d a b T phi) := by
  rw [← diagonal_eq]
  exact PRZZMixedPoisson.original_error_eq L J N F c d a b T phi

/-- The entire collective field converges; separate integrability or
convergence of its individual infinite Fourier pieces is not assumed. -/
theorem complete_limit (N : ℕ) (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (c d : ℕ → ℂ) (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (hn : ‖a+b‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) (J : ℕ → ℕ) :
    Tendsto (fun L => lift (fun e => components L (J L) N F e a b T phi) c d) atTop
      (𝓝 (moment N c d a b T phi-
        arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N a b T phi) c d-
        ∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t*
          PRZZIntegratedDefect.defect a b t)) := by
  have he := error_limit N F hf hlo hhi c d a b ha hb hs hn T hT phi hp J
  have hh := he.const_sub (moment N c d a b T phi-
    arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N a b T phi) c d)
  convert hh using 1
  funext L
  rw [moment_components_eq]
  ring

/-- The original mixed moment equation after cutoff removal. Its only
unevaluated summand is the explicit collective Poisson field, not the AFE
replacement error. Constants precede both slots and J may vary with L. -/
theorem decomposition_limit (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (S r delta H : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ (c d : ℕ → ℂ) (N : ℕ),
      1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) → ∀ J : ℕ → ℕ, ∃ E : ℂ,
      Tendsto (fun L =>
        moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi-
        arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) c d-
        lift (fun e => components L (J L) N F e
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) c d) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_error_limit F hf hlo hhi S r delta H hS hr hd hH
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hp hP hphi J
  obtain ⟨E,he,hbound⟩ := h A B hA hB hsep c d N hN hNT hc hd' phi P hp hP hphi J
  refine ⟨E,?_,hbound⟩
  convert he using 1
  funext L
  rw [moment_components_eq]
  ring

/-- All independent witness combinations, hence all 49 ordered basis
pairs, are inserted without freezing the basis at a reference height. -/
theorem family_decomposition_limit (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (S r delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (z w : Fin 7 → ℂ),
      0 < theta → (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) → ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) → ∀ J : ℕ → ℕ, ∃ E : ℂ,
      let c := family (PRZZWitnessBasis.basis theta T) z
      let d := family (PRZZWitnessBasis.basis theta T) w
      Tendsto (fun L =>
        moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi-
        arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) c d-
        lift (fun e => components L (J L) N F e
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) c d) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := decomposition_limit F hf hlo hhi S r delta 84 hS hr hd (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro theta z w htheta hz hw A B hA hB hsep N hN hNT phi P hp hP hphi J
  exact h A B hA hB hsep _ _ N hN hNT
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT z hz n)
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT w hw n)
    phi P hp hP hphi J

#print axioms diagonal_eq
#print axioms moment_components_eq
#print axioms complete_limit
#print axioms decomposition_limit
#print axioms family_decomposition_limit
end XiPrime8845.PRZZMixedMoment
