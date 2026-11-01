import PRZZSharpAggregation
import PRZZTypeI

/-! Product-dependent analytic weights are retained by finite Abel
summation. The seven-term estimate is uniform in every sharp cutoff;
its extra cost is the actual discrete variation, not an assumed constant. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZWeightedDI
open PRZZSharpDI PRZZKloostermanInputs PRZZDISeven
set_option maxHeartbeats 3000000

def weighted (N : ℕ) (V F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊V⌋₊, ∑ f ∈ (Icc 1 ⌊F⌋₊).filter (fun f => c.Coprime (h*f)),
    ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ e ∈ (Icc 1 ⌊E⌋₊).filter (fun e => e.Coprime c),
      if e*f ≤ N then w (e*f)*(r c*beta f*(nu a*alpha e)*
        PRZZKloostermanInputs.e ((a:ℝ)*inverseResidue c (h*e*f)/c)) else 0

private theorem jump (m j : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    (if m ≤ j+1 then z else 0)-(if m ≤ j then z else 0) =
      if j=m-1 then z else 0 := by
  split_ifs <;> simp_all <;> omega

private theorem jump_sum (N m : ℕ) (hm : 1 ≤ m) (z : ℂ) (w : ℕ → ℂ) :
    (∑ j ∈ range N, w (j+1)*((if m ≤ j+1 then z else 0)-(if m ≤ j then z else 0))) =
      if m ≤ N then w m*z else 0 := by
  simp_rw [jump m _ hm]
  by_cases h : m ≤ N
  · rw [if_pos h,sum_eq_single (m-1)]
    · simp [show m-1+1=m by omega]
    · intro j hj hjm
      simp [hjm]
    · intro hh
      exact False.elim (hh (mem_range.mpr (by omega)))
  · rw [if_neg h]
    apply sum_eq_zero
    intro j hj
    have hh : j ≠ m-1 := by have := mem_range.mp hj; omega
    simp [hh]

theorem weighted_eq (N : ℕ) (V F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) :
    weighted N V F A E h r beta nu alpha w =
      ∑ j ∈ range N, w (j+1)*(sharpBlock (j+1) V F A E h r beta nu alpha-
        sharpBlock j V F A E h r beta nu alpha) := by
  symm
  unfold sharpBlock weighted
  simp_rw [← sum_sub_distrib,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  apply jump_sum
  have hf := (mem_Icc.mp (mem_filter.mp hf).1).1
  have he := (mem_Icc.mp (mem_filter.mp he).1).1
  nlinarith

theorem sharp_zero (V F A E : ℝ) (h : ℕ) (r beta nu alpha : ℕ → ℂ) :
    sharpBlock 0 V F A E h r beta nu alpha = 0 := by
  unfold sharpBlock
  apply sum_eq_zero; intro c hc
  apply sum_eq_zero; intro f hf
  apply sum_eq_zero; intro a ha
  apply sum_eq_zero; intro e he
  have hf := (mem_Icc.mp (mem_filter.mp hf).1).1
  have he := (mem_Icc.mp (mem_filter.mp he).1).1
  exact if_neg (by nlinarith)

theorem weighted_bound (N : ℕ) (V F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) (B : ℝ)
    (hb : ∀ k ≤ N, ‖sharpBlock k V F A E h r beta nu alpha‖ ≤ B) :
    ‖weighted N V F A E h r beta nu alpha w‖ ≤
      B*PRZZTypeI.variation (fun j => w (j+1)) N := by
  rw [weighted_eq]
  apply PRZZTypeI.abel_bound
  intro k hk
  have he : (∑ j ∈ range k, (sharpBlock (j+1) V F A E h r beta nu alpha-
      sharpBlock j V F A E h r beta nu alpha)) = sharpBlock k V F A E h r beta nu alpha := by
    induction k with
    | zero => simp [sharp_zero]
    | succ k ih => rw [sum_range_succ,ih (by omega)]; ring
  rw [he]
  exact hb k hk

theorem weighted_seven (hDI : DeshouillersIwaniecLemma1) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ V F A E : ℝ,
      1 ≤ V → 1 ≤ F → 1 ≤ A → 1 ≤ E → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha w : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊V⌋₊, ‖r c‖ ≤ R) →
      (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) →
      ‖weighted N V F A E h r beta nu alpha w‖ ≤
        ((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*(R*S*(P*Q)*K*
          ((V*F*A*E)^eps*seven h E A (E*F) V)))*
            PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨K,hK,hb⟩ := sharpBlock_log_bound hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N V F A E hV hF hA hE h hh R S P Q hR hS hP hQ r beta nu alpha w hr hf hn he
  apply weighted_bound
  intro k hk
  apply (hb k V F A E hV hF hA hE h hh R S P Q hR hS hP hQ r beta nu alpha hr hf hn he).trans
  have hl : 0 ≤ 1+2*Real.log ((⌊F⌋₊:ℝ)+1) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ (⌊F⌋₊:ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg _))
    linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (PRZZDIExpansion.diBound_seven eps E A F V h hh (by linarith) (by linarith)
      (by linarith) (by linarith)) (by positivity)) hl

def negative (N : ℕ) (V F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊V⌋₊, ∑ f ∈ (Icc 1 ⌊F⌋₊).filter (fun f => c.Coprime (h*f)),
    ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ e ∈ (Icc 1 ⌊E⌋₊).filter (fun e => e.Coprime c),
      if e*f ≤ N then w (e*f)*(r c*beta f*(nu a*alpha e)*
        PRZZKloostermanInputs.e (-((a:ℝ)*inverseResidue c (h*e*f)/c))) else 0

theorem negative_eq (N : ℕ) (V F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) :
    negative N V F A E h r beta nu alpha w =
      starRingEnd ℂ (weighted N V F A E h
        (fun n => starRingEnd ℂ (r n)) (fun n => starRingEnd ℂ (beta n))
        (fun n => starRingEnd ℂ (nu n)) (fun n => starRingEnd ℂ (alpha n))
        (fun n => starRingEnd ℂ (w n))) := by
  simp [negative,weighted,apply_ite,PRZZTypeII.conj_e]

theorem signed_seven (hDI : DeshouillersIwaniecLemma1) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ V F A E : ℝ,
      1 ≤ V → 1 ≤ F → 1 ≤ A → 1 ≤ E → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta np nm alpha w : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊V⌋₊, ‖r c‖ ≤ R) → (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖np a‖ ≤ P) → (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nm a‖ ≤ P) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) →
      ‖negative N V F A E h r beta np alpha w+weighted N V F A E h r beta nm alpha w‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*(R*S*(P*Q)*K*
          ((V*F*A*E)^eps*seven h E A (E*F) V)))*
            PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨K,hK,hb⟩ := weighted_seven hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N V F A E hV hF hA hE h hh R S P Q hR hS hP hQ r beta np nm alpha w hr hf hp hm he
  have hpos := hb N V F A E hV hF hA hE h hh R S P Q hR hS hP hQ r beta nm alpha w hr hf hm he
  have hneg := hb N V F A E hV hF hA hE h hh R S P Q hR hS hP hQ
    (fun n => starRingEnd ℂ (r n)) (fun n => starRingEnd ℂ (beta n))
    (fun n => starRingEnd ℂ (np n)) (fun n => starRingEnd ℂ (alpha n))
    (fun n => starRingEnd ℂ (w n))
    (by simpa using hr) (by simpa using hf) (by simpa using hp) (by simpa using he)
  have hv : PRZZTypeI.variation (fun j => starRingEnd ℂ (w (j+1))) N =
      PRZZTypeI.variation (fun j => w (j+1)) N := by simp [PRZZTypeI.variation, ← map_sub]
  rw [hv] at hneg
  rw [← Complex.norm_conj,← negative_eq] at hneg
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

#print axioms negative_eq
#print axioms signed_seven
#print axioms weighted_eq
#print axioms sharp_zero
#print axioms weighted_bound
#print axioms weighted_seven
end XiPrime8845.PRZZWeightedDI
