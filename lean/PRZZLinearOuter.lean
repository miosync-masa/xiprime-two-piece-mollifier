import PRZZMellinMoment
import PRZZOuterMass
import PRZZSharpAggregation

/-! Literal A* norm transfer with linear Mellin-frequency growth.
The actual localized kernel supplies Fubini; the fixed cutoff supplies
its weighted Mellin mass. Arithmetic block estimates remain explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZLinearOuter
open PRZZAStar PRZZAStarNu PRZZActualMellin PRZZAStarWindow PRZZMellinSeparation
open PRZZAStarRectangles PRZZNuCoefficient PRZZAStarIntegralBound
open PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem literal_linear_bound (N d : ℕ) (D H T A B M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (_hM : 0 ≤ M)
    (hbound : ∀ p ∈ window N T A B, ∀ t : ℝ,
      ‖signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ M*(1+|t|)) :
    ‖literal N d D H T a F1 F2 FM W Phi α β‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖common N d T A B W α β p‖)*M*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let J := fun p t => ∑ z ∈ indices N d D H,
    localized N d T A B a F1 F2 FM W Phi α β z p t
  have hi : Integrable (Function.uncurry J) := by
    apply integrable_finsetSum
    intro z hz
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact localized_integrable N d T A B a F1 F2 FM W Phi α β z hFM hW hPhi hsP
      hN hT hA hB (by have := (mem_Icc.mp hn.1).1; omega)
      (by have := (mem_Icc.mp hn.2).1; omega)
  have hm : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hc := common_integrable N d T A B W α β hW hN hd hT hA hB
  have hj := (hc.norm.mul_const M).mul_prod hm
  have hb : ∀ q : (ℝ × ℝ) × ℝ, ‖Function.uncurry J q‖ ≤
      (‖common N d T A B W α β q.1‖*M)*((1+|q.2|)*‖mellin Phi (q.2*I)‖) := by
    intro q
    change ‖∑ z ∈ indices N d D H, localized N d T A B a F1 F2 FM W Phi α β z q.1 q.2‖ ≤ _
    rw [localized_nu]
    change ‖common N d T A B W α β q.1 * mellin Phi (q.2*I) *
      twist (q.1.1*q.1.2/T) q.2 * signedSum N d D H a F1 F2 FM α β q.1.1 q.1.2 q.2‖ ≤ _
    by_cases hp : q.1 ∈ window N T A B
    · have hx : 0 < q.1.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
      have hy : 0 < q.1.2 := (div_pos hT (by positivity)).trans_le hp.2.1
      simp only [norm_mul,twist_norm _ _ (div_pos (mul_pos hx hy) hT),mul_one]
      exact (mul_le_mul_of_nonneg_left (hbound q.1 hp q.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
    · simp [common,hp]
  rw [PRZZAStarTransform.literal_mellin N d D H T A B a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hT hA hB]
  change ‖(1/(2*Real.pi):ℂ)*(∫ t, ∫ p, J p t)‖ ≤ _
  have hprod := integral_prod (Function.uncurry J) hi
  simp only [Function.uncurry] at hprod
  rw [← integral_integral_swap hi,← hprod,norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left (integral_mono hi.norm hj hb) (by positivity)).trans_eq
  change (1/(2*Real.pi))*(∫ q : (ℝ × ℝ) × ℝ,
    ‖common N d T A B W α β q.1‖*M*((1+|q.2|)*‖mellin Phi (q.2*I)‖) ∂volume.prod volume) = _
  rw [integral_prod _ hj]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,integral_mul_const]
  ring

theorem literal_linear_uniform (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ D H M : ℝ, 0 ≤ M →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (α β : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(α+β).re| ≤ S/Real.log T →
      (∀ p ∈ window N T A B, ∀ t : ℝ,
        ‖PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ M*(1+|t|)) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi α β‖ ≤ C*(T/d)*M := by
  obtain ⟨C,hC,hmass⟩ := PRZZOuterMass.common_mass_uniform W hW A B S hA hB hS
  let L := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hL : 0 ≤ L := integral_nonneg (fun _ => by positivity)
  refine ⟨(1/(2*Real.pi))*C*L,by positivity,?_⟩
  intro N d hN hd T hT hlog hNT D H M hM a F1 F2 FM α β hFM hsM hz hb
  have hh := literal_linear_bound N d D H T A B M a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hd hT hA hB hM hb
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmass N d hN hd T hT hlog hNT α β hz)
        (by positivity : 0 ≤ 1/(2*Real.pi))) hM) hL
  exact hh'.trans_eq (by dsimp [L]; ring)

/-- Composes the proved G average with weighted Mellin integration.
The actual all-branch decomposition and balanced bounds are still explicit
inputs: this theorem does not assert their suppliers. -/
theorem literal_linear_h_blocks (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S)
    (js : List ℕ) (k : ℕ) (η β0 : ℝ) (hη : 0 < η) (hβ : 0 < β0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T →
      ∀ D H sigma X A0 V B0 : ℝ, sigma ≤ 0 → 0 < X → 0 ≤ A0 → 0 ≤ V → 0 ≤ B0 →
      ∀ (s : Finset ℕ) (E : ℕ → ℝ),
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (α β : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(α+β).re| ≤ S/Real.log T →
      ∀ z : (ℝ × ℝ) → ℝ → ℕ → ℂ,
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t,
        PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t =
          ∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z p t h) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        ‖z p t h‖ ≤ (B0*(1+|t|))*seven h (E h) A0 (X/h) V) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi α β‖ ≤
        C*(T/d)*B0*envelope X A0 V*(d:ℝ)^η*(N:ℝ)^β0 := by
  obtain ⟨Co,hCo,ho⟩ := literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := PRZZSharpAggregation.source_h_sum js k η β0 hη hβ
  refine ⟨Co*Cg,mul_nonneg hCo hCg.le,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V B0 hσ hX hA0 hV hB0 s E hs hE
    a F1 F2 FM α β hFM hsM hz z hsplit hblocks
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (B0*(envelope X A0 V*(Cg*(d:ℝ)^η*(N:ℝ)^β0))) (by positivity)
    a F1 F2 FM α β hFM hsM hz (by
      intro p hp t
      rw [hsplit p hp t]
      exact (hg sigma d N hσ hd hN s X A0 V (B0*(1+|t|)) E hX hA0 hV
        (by positivity) hs hE (z p t) (hblocks p hp t)).trans_eq (by ring))
  exact hb.trans_eq (by ring)

#print axioms literal_linear_h_blocks
#print axioms literal_linear_bound
#print axioms literal_linear_uniform
end XiPrime8845.PRZZLinearOuter
