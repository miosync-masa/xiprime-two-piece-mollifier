import PRZZSharpDI
import PRZZDIExpansion
import PRZZOuterMass

/-! Sharp signed DI to the seven terms, then the proved source G average.
Balanced sizes and a decomposition of the original signed sum remain
explicit obligations. No such decomposition is postulated as an axiom. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZSharpAggregation
open PRZZSharpDI PRZZKloostermanInputs PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem sharp_signed_seven (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ A E F V : ℝ,
      1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nuPlus nuMinus alpha : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) → (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nuPlus a‖ ≤ P) → (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nuMinus a‖ ≤ P) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) →
      ‖sharpNegativeBlock N V F A E h r beta nuPlus alpha+
        sharpBlock N V F A E h r beta nuMinus alpha‖ ≤
      2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*(R*S*(P*Q)*K*((V*F*A*E)^ε*seven h E A (E*F) V))) := by
  obtain ⟨K,hK,hb⟩ := sharp_two_sided_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro N A E F V hA hE hF hV h hh R S P Q hR hS hP hQ r beta np nm alpha hr hf hp hm he
  apply (hb N V F A E hV hF hA hE h hh R S P Q hR hS hP hQ r beta np nm alpha hr hf hp hm he).trans
  have hl : 0 ≤ 1+2*Real.log ((⌊F⌋₊:ℝ)+1) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ (⌊F⌋₊:ℝ)+1 by exact le_add_of_nonneg_left (Nat.cast_nonneg _))
    linarith
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (PRZZDIExpansion.diBound_seven ε E A F V h hh
        (by linarith) (by linarith) (by linarith) (by linarith)) (by positivity)) hl) (by norm_num)

/-- A finite collection of branches costs the sum of absolute scalar
weights, not its cardinality and not an assumed cancellation. -/
theorem branch_sum_bound {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (B : ι → ℝ)
    (hb : ∀ i ∈ s, ‖z i‖ ≤ B i) :
    ‖∑ i ∈ s, c i*z i‖ ≤ ∑ i ∈ s, ‖c i‖*B i := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _)

/-- The G(h) moment is supplied by the proved arithmetic average.
B is the common remaining coefficient/DI/log-separation budget. -/
theorem source_h_sum (js : List ℕ) (k : ℕ) (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℝ) (d n : ℕ),
      sigma ≤ 0 → 1 ≤ d → 1 ≤ n → ∀ (s : Finset ℕ) (X A V B : ℝ) (E : ℕ → ℝ),
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ B →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      ∀ z : ℕ → ℂ, (∀ h ∈ s, ‖z h‖ ≤ B*seven h (E h) A (X/h) V) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        B*(envelope X A V*(C*(d:ℝ)^η*(n:ℝ)^β)) := by
  obtain ⟨C,hC,h⟩ := PRZZGAbsorption.sourceG_seven_power js k η β hη hβ
  refine ⟨C,hC,?_⟩
  intro sigma d n hσ hd hn s X A V B E hX hA hV hB hs hE z hz
  apply (branch_sum_bound s (fun h => (sourceG js k sigma d h:ℂ)) z _ hz).trans
  simp only [Complex.norm_real,Real.norm_eq_abs]
  calc
    _ = B*(∑ h ∈ s, |sourceG js k sigma d h| * seven h (E h) A (X/h) V) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h sigma d n hσ hd hn s X A V E hX hA hV hs hE) hB

/-- Height-uniform outer integration after an exact h decomposition.
The decomposition and balanced block bounds are hypotheses, not suppliers.
W is fixed; no uniformity for an unspecified height-dependent W is claimed. -/
theorem literal_of_h_blocks (W Phi : ℝ → ℂ) (hW : Continuous W)
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
        ‖z p t h‖ ≤ B0*seven h (E h) A0 (X/h) V) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi α β‖ ≤
        C*(T/d)*B0*envelope X A0 V*(d:ℝ)^η*(N:ℝ)^β0 := by
  obtain ⟨Co,hCo,ho⟩ := PRZZOuterMass.literal_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := source_h_sum js k η β0 hη hβ
  refine ⟨Co*Cg,mul_nonneg hCo hCg.le,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V B0 hσ hX hA0 hV hB0 s E hs hE
    a F1 F2 FM α β hFM hsM hz z hsplit hblocks
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (B0*(envelope X A0 V*(Cg*(d:ℝ)^η*(N:ℝ)^β0))) (by positivity)
    a F1 F2 FM α β hFM hsM hz (by
      intro p hp t
      rw [hsplit p hp t]
      exact hg sigma d N hσ hd hN s X A0 V B0 E hX hA0 hV hB0 hs hE (z p t) (hblocks p hp t))
  exact hb.trans_eq (by ring)

#print axioms sharp_signed_seven
#print axioms branch_sum_bound
#print axioms source_h_sum
#print axioms literal_of_h_blocks
end XiPrime8845.PRZZSharpAggregation
