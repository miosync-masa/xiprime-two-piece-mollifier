import PRZZSharpCost
import PRZZGroupBounds

/-! DI with a literal sharp product cutoff. The comparison Fourier phases
are absorbed in the two factor coefficients, not in the Kloosterman phase.
The L1 cost and its proved logarithmic bound are both exposed. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace XiPrime8845.PRZZSharpDI
open PRZZSharpCutoff PRZZTypeII PRZZKloostermanInputs
set_option maxHeartbeats 3000000

def sharpBlock (N : ℕ) (C D U V : ℝ) (rho : ℕ)
    (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    ∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      if v*d ≤ N then r c*beta d*(nu u*alpha v)*
        e ((u:ℝ)*inverseResidue c (rho*v*d)/c) else 0

def rightTwist (beta : ℕ → ℂ) (t : PRZZSharpCutoff.Circle) (d : ℕ) : ℂ :=
  beta d*fourier (-(d:ℤ)) t
def leftTwist (N F : ℕ) (alpha : ℕ → ℂ) (t : PRZZSharpCutoff.Circle) (v : ℕ) : ℂ :=
  alpha v*fourier (threshold N F v:ℤ) t

theorem rightTwist_norm (beta : ℕ → ℂ) (t : PRZZSharpCutoff.Circle) (d : ℕ) :
    ‖rightTwist beta t d‖ = ‖beta d‖ := by rw [rightTwist,norm_mul,phase_norm,mul_one]
theorem leftTwist_norm (N F : ℕ) (alpha : ℕ → ℂ) (t : PRZZSharpCutoff.Circle) (v : ℕ) :
    ‖leftTwist N F alpha t v‖ = ‖alpha v‖ := by rw [leftTwist,norm_mul,phase_norm,mul_one]

private theorem cint {f : PRZZSharpCutoff.Circle → ℂ} (hf : Continuous f) : Integrable f haar := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact (μ := haar) isCompact_univ

theorem twisted_continuous (N : ℕ) (C D U V : ℝ) (rho : ℕ)
    (r beta nu alpha : ℕ → ℂ) :
    Continuous (fun t : PRZZSharpCutoff.Circle => block C D U V rho r (rightTwist beta t) nu
      (leftTwist N ⌊D⌋₊ alpha t)) := by
  unfold block rightTwist leftTwist
  fun_prop

theorem sharpBlock_eq (N : ℕ) (C D U V : ℝ) (rho : ℕ)
    (r beta nu alpha : ℕ → ℂ) :
    sharpBlock N C D U V rho r beta nu alpha =
      ∫ t : PRZZSharpCutoff.Circle, kernel ⌊D⌋₊ t*block C D U V rho r (rightTwist beta t) nu
        (leftTwist N ⌊D⌋₊ alpha t) ∂haar := by
  have hk := kernel_continuous ⌊D⌋₊
  unfold sharpBlock block rightTwist leftTwist
  simp only [mul_sum]
  rw [integral_finsetSum _ (fun _ _ => cint (by fun_prop))]
  apply sum_congr rfl
  intro c hc
  rw [integral_finsetSum _ (fun _ _ => cint (by fun_prop))]
  apply sum_congr rfl
  intro d hd
  rw [integral_finsetSum _ (fun _ _ => cint (by fun_prop))]
  apply sum_congr rfl
  intro u hu
  rw [integral_finsetSum _ (fun _ _ => cint (by fun_prop))]
  apply sum_congr rfl
  intro v hv
  have hh := product_comparison N ⌊D⌋₊ v d (mem_Icc.mp (mem_filter.mp hv).1).1
    (mem_Icc.mp (mem_filter.mp hd).1).2
  have he : (fun t : PRZZSharpCutoff.Circle => kernel ⌊D⌋₊ t*
      (r c*(beta d*fourier (-(d:ℤ)) t)*
      ((nu u*(alpha v*fourier (threshold N ⌊D⌋₊ v:ℤ) t))*
      e ((u:ℝ)*inverseResidue c (rho*v*d)/c)))) =
      (fun t => (r c*beta d*(nu u*alpha v)*e ((u:ℝ)*inverseResidue c (rho*v*d)/c))*
        (kernel ⌊D⌋₊ t*fourier (threshold N ⌊D⌋₊ v:ℤ) t*fourier (-(d:ℤ)) t)) := by
    funext t
    ring
  rw [he,integral_const_mul,hh]
  split_ifs <;> simp

theorem sharpBlock_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) → (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ‖sharpBlock N C D U V rho r beta nu alpha‖ ≤
        cost ⌊D⌋₊*(R*S*(P*Q)*K*diBound ε C D U V rho) := by
  obtain ⟨K,hK,h⟩ := block_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn ha
  rw [sharpBlock_eq]
  apply (norm_integral_le_integral_norm _).trans
  rw [cost,← integral_mul_const]
  apply integral_mono
  · exact (cint ((kernel_continuous _).mul (twisted_continuous N C D U V rho r beta nu alpha))).norm
  · exact ((cint (kernel_continuous _)).norm).mul_const _
  · intro t
    dsimp only
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r _ nu _ hr
      (by simpa only [rightTwist_norm] using hb) hn
      (by simpa only [leftTwist_norm] using ha)

#print axioms rightTwist_norm
#print axioms leftTwist_norm
#print axioms sharpBlock_eq
#print axioms sharpBlock_bound

theorem sharpBlock_log_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) → (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ‖sharpBlock N C D U V rho r beta nu alpha‖ ≤
        (1+2*Real.log ((⌊D⌋₊:ℝ)+1))*(R*S*(P*Q)*K*diBound ε C D U V rho) := by
  obtain ⟨K,hK,h⟩ := sharpBlock_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn ha
  apply (h N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn ha).trans
  apply mul_le_mul_of_nonneg_right (PRZZSharpCost.cost_log _)
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hbnd : 0 ≤ diBound ε C D U V rho := by
    unfold diBound
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    apply add_nonneg (Real.sqrt_nonneg _)
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  exact mul_nonneg (by positivity) hbnd

#print axioms sharpBlock_log_bound

/-- Supply both factor envelopes from actual log-weighted HB groups,
including arbitrary restrictions on individual atoms and on the groups. -/
theorem sharp_groups_bound (hDI : DeshouillersIwaniecLemma1)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (js ks : List ℕ) :
    ∃ K Cf Ca : ℝ, 0 < K ∧ 0 < Cf ∧ 0 < Ca ∧
      ∀ N : ℕ, ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R P : ℝ, 0 ≤ R → 0 < P →
      ∀ r nu : ℕ → ℂ, (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      ∀ a b : ℕ → PRZZGroupBounds.Atom, ∀ s t : Set ℕ,
      ∀ w z : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) → (∀ n, ‖z n‖ ≤ 1) →
      ‖sharpBlock N C D U V rho r
        (s.indicator (fun n => (PRZZGroupBounds.group js a n:ℂ)*w n)) nu
        (t.indicator (fun n => (PRZZGroupBounds.group ks b n:ℂ)*z n))‖ ≤
        (1+2*Real.log ((⌊D⌋₊:ℝ)+1))*(R*(Cf*D^η)*(P*(Ca*V^η))*K*diBound ε C D U V rho) := by
  classical
  obtain ⟨K,hK,h⟩ := sharpBlock_log_bound hDI ε hε
  obtain ⟨Cf,hCf,hf⟩ := PRZZGroupBounds.rectangle_envelope js η hη
  obtain ⟨Ca,hCa,ha⟩ := PRZZGroupBounds.rectangle_envelope ks η hη
  refine ⟨K,Cf,Ca,hK,hCf,hCa,?_⟩
  intro N C D U V hC hD hU hV rho hrho R P hR hP r nu hr hn a b s t w z hw hz
  exact h N C D U V hC hD hU hV rho hrho R (Cf*D^η) P (Ca*V^η)
    hR (by positivity) hP (mul_pos hCa (Real.rpow_pos_of_pos (by linarith) _))
    r _ nu _ hr (hf a s w hw D hD) hn (ha b t z hz V hV)

#print axioms sharp_groups_bound

/-- Literal negative phase, with the same sharp product cutoff. -/
def sharpNegativeBlock (N : ℕ) (C D U V : ℝ) (rho : ℕ)
    (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    ∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      if v*d ≤ N then r c*beta d*(nu u*alpha v)*
        e (-((u:ℝ)*inverseResidue c (rho*v*d)/c)) else 0

theorem sharpNegativeBlock_eq (N : ℕ) (C D U V : ℝ) (rho : ℕ)
    (r beta nu alpha : ℕ → ℂ) :
    sharpNegativeBlock N C D U V rho r beta nu alpha =
      starRingEnd ℂ (sharpBlock N C D U V rho (fun n => starRingEnd ℂ (r n))
        (fun n => starRingEnd ℂ (beta n)) (fun n => starRingEnd ℂ (nu n))
        (fun n => starRingEnd ℂ (alpha n))) := by
  simp [sharpNegativeBlock,sharpBlock,apply_ite,conj_e]

theorem sharp_two_sided_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nuPlus nuMinus alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nuPlus u‖ ≤ P) → (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nuMinus u‖ ≤ P) →
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ‖sharpNegativeBlock N C D U V rho r beta nuPlus alpha+
        sharpBlock N C D U V rho r beta nuMinus alpha‖ ≤
        2*((1+2*Real.log ((⌊D⌋₊:ℝ)+1))*(R*S*(P*Q)*K*diBound ε C D U V rho)) := by
  obtain ⟨K,hK,h⟩ := sharpBlock_log_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nuPlus nuMinus alpha hr hb hp hm ha
  have hneg := h N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    (fun n => starRingEnd ℂ (r n)) (fun n => starRingEnd ℂ (beta n))
    (fun n => starRingEnd ℂ (nuPlus n)) (fun n => starRingEnd ℂ (alpha n))
    (by simpa using hr) (by simpa using hb) (by simpa using hp) (by simpa using ha)
  have hpos := h N C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    r beta nuMinus alpha hr hb hm ha
  rw [← Complex.norm_conj,← sharpNegativeBlock_eq] at hneg
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

#print axioms sharpNegativeBlock_eq
#print axioms sharp_two_sided_bound
end XiPrime8845.PRZZSharpDI
