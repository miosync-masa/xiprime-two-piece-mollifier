import PRZZSourceTypeII
import PRZZDISeven

/-! Explicit radical expansion of the DI bound. Source coefficient envelopes
and the original integral A-star reduction remain separate obligations. -/
noncomputable section
namespace XiPrime8845.PRZZDIExpansion
open PRZZKloostermanInputs PRZZDISeven
set_option maxHeartbeats 4000000

def six (h E A F V : ℝ) : ℝ :=
  (h*V*F)^(1/4:ℝ)*(A^(1/2:ℝ)+E^(1/2:ℝ))*
    (V^(1/4:ℝ)+h^(1/4:ℝ)*E^(1/2:ℝ))+
  (h*A*E^2*F^2)^(1/4:ℝ)*(A^(1/4:ℝ)+E^(1/4:ℝ))

theorem radical_bound (h E A F V : ℝ) (hh : 1 ≤ h)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hF : 0 ≤ F) (hV : 0 ≤ V) :
    (A+E)^(1/4:ℝ)*(V*F*(A+h*E)*(V+h*E^2)+h*A*E^2*F^2)^(1/4:ℝ) ≤
      six h E A F V := by
  have hh0 : 0 ≤ h := by linarith
  have ha : 0 ≤ A+E := by positivity
  have hb : (A+E)*(A+h*E) ≤ h*(A+E)^2 := by
    have hx : A+h*E ≤ h*(A+E) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx ha]
  have hroot : ((A+E)^2)^(1/4:ℝ) = (A+E)^(1/2:ℝ) := by
    rw [← Real.rpow_natCast_mul ha]
    norm_num
  have heroot : (E^2)^(1/4:ℝ) = E^(1/2:ℝ) := by
    rw [← Real.rpow_natCast_mul hE]
    norm_num
  rw [← Real.mul_rpow ha (by positivity)]
  calc
    _ = (V*F*((A+E)*(A+h*E))*(V+h*E^2)+(A+E)*(h*A*E^2*F^2))^(1/4:ℝ) := by congr 1; ring
    _ ≤ (V*F*(h*(A+E)^2)*(V+h*E^2)+(A+E)*(h*A*E^2*F^2))^(1/4:ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      gcongr
    _ ≤ (V*F*(h*(A+E)^2)*(V+h*E^2))^(1/4:ℝ)+
        ((A+E)*(h*A*E^2*F^2))^(1/4:ℝ) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num) (by norm_num)
    _ = (h*V*F)^(1/4:ℝ)*(A+E)^(1/2:ℝ)*(V+h*E^2)^(1/4:ℝ)+
        (h*A*E^2*F^2)^(1/4:ℝ)*(A+E)^(1/4:ℝ) := by
      rw [show V*F*(h*(A+E)^2)*(V+h*E^2) = (h*V*F)*(A+E)^2*(V+h*E^2) by ring]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),hroot,
        Real.mul_rpow ha (by positivity)]
      ring
    _ ≤ six h E A F V := by
      unfold six
      have h1 := Real.rpow_add_le_add_rpow hA hE (p := (1/2:ℝ)) (by norm_num) (by norm_num)
      have h2 := Real.rpow_add_le_add_rpow hV (show 0 ≤ h*E^2 by positivity)
        (p := (1/4:ℝ)) (by norm_num) (by norm_num)
      rw [Real.mul_rpow hh0 (sq_nonneg E),heroot] at h2
      have h3 := Real.rpow_add_le_add_rpow hA hE (p := (1/4:ℝ)) (by norm_num) (by norm_num)
      gcongr

private theorem fourth_rep (x : ℝ) (hx : 0 < x) : ∃ y : ℝ, 0 < y ∧ x = y^4 := by
  refine ⟨x^(1/4:ℝ),Real.rpow_pos_of_pos hx _,?_⟩
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num

/-- The first DI term and the six radical terms are exactly the seven
monomials, with U=E*F. No asymptotic constants are hidden in this identity. -/
theorem seven_identity (h E A F V : ℝ) (hh : 0 < h) (hE : 0 < E)
    (hA : 0 < A) (hF : 0 < F) (hV : 0 < V) :
    (V*F*A*E)^(1/2:ℝ)*(Real.sqrt (V*F)+six h E A F V) = seven h E A (E*F) V := by
  obtain ⟨h,hh,rfl⟩ := fourth_rep h hh
  obtain ⟨E,hE,rfl⟩ := fourth_rep E hE
  obtain ⟨A,hA,rfl⟩ := fourth_rep A hA
  obtain ⟨F,hF,rfl⟩ := fourth_rep F hF
  obtain ⟨V,hV,rfl⟩ := fourth_rep V hV
  rw [seven_expand]
  unfold six
  simp (disch := positivity) only [Real.sqrt_eq_rpow, Real.mul_rpow,
    ← Real.rpow_natCast_mul]
  norm_num [Real.rpow_neg,Real.rpow_natCast,Real.rpow_neg_one]
  field_simp
  <;> ring

#print axioms radical_bound
#print axioms seven_identity

theorem diBound_seven (ε E A F V : ℝ) (h : ℕ) (hh : 1 ≤ h)
    (hE : 0 < E) (hA : 0 < A) (hF : 0 < F) (hV : 0 < V) :
    diBound ε V F A E h ≤ (V*F*A*E)^ε*seven h E A (E*F) V := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0:ℝ) < h := by linarith
  have hp : 0 < V*F*A*E := by positivity
  unfold diBound
  change (V*F*A*E)^(1/2+ε:ℝ)*(Real.sqrt (V*F)+
    (A+E)^(1/4:ℝ)*(V*F*(A+(h:ℝ)*E)*(V+(h:ℝ)*E^2)+(h:ℝ)*A*E^2*F^2)^(1/4:ℝ)) ≤ _
  rw [Real.rpow_add hp]
  calc
    _ = (V*F*A*E)^ε*((V*F*A*E)^(1/2:ℝ)*(Real.sqrt (V*F)+
        (A+E)^(1/4:ℝ)*(V*F*(A+(h:ℝ)*E)*(V+(h:ℝ)*E^2)+(h:ℝ)*A*E^2*F^2)^(1/4:ℝ))) := by ring
    _ ≤ (V*F*A*E)^ε*((V*F*A*E)^(1/2:ℝ)*(Real.sqrt (V*F)+six h E A F V)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      exact add_le_add le_rfl (radical_bound h E A F V hh' hE.le hA.le hF.le hV.le)
    _ = _ := by rw [seven_identity h E A F V hh0 hE hA hF hV]

#print axioms diBound_seven

/-- The actual separated source sum satisfies the seven-term estimate,
conditional only on DI and the displayed coefficient envelopes. -/
theorem sourceSum_seven (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A E F V : ℝ, 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ h d : ℕ, 1 ≤ h → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) → (∀ f ∈ Finset.Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ a ∈ Finset.Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) → (∀ e ∈ Finset.Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) →
      ‖PRZZSourceTypeII.sourceSum A E F V h d r beta nu alpha‖ ≤
        R*S*(P*Q)*K*((V*F*A*E)^ε*seven h E A (E*F) V) := by
  obtain ⟨K,hK,hb⟩ := PRZZSourceTypeII.sourceSum_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro A E F V hA hE hF hV h d hh R S P Q hR hS hP hQ r beta nu alpha hr hb' hn ha
  apply (hb A E F V hA hE hF hV h d hh R S P Q hR hS hP hQ r beta nu alpha hr hb' hn ha).trans
  exact mul_le_mul_of_nonneg_left (diBound_seven ε E A F V h hh
    (by linarith) (by linarith) (by linarith) (by linarith)) (by positivity)

#print axioms sourceSum_seven
end XiPrime8845.PRZZDIExpansion
