import PRZZTypeII

/-! Literal separated negative-phase Type II sum of PRZZ p.21, retaining
the additional coprimality with the original divisor d. It is imposed on
the two coefficients, not discarded from a cancellation estimate.
Sharp product cutoffs and source coefficient envelopes are not supplied. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSourceTypeII
open PRZZTypeII PRZZKloostermanInputs
set_option maxHeartbeats 2000000

def coprimeCoeff (d : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Coprime d then f n else 0

def sourceSum (A E F V : ℝ) (h d : ℕ) (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime h),
    ∑ e ∈ (Icc 1 ⌊E⌋₊).filter (fun e => e.Coprime (d*v)),
      ∑ f ∈ (Icc 1 ⌊F⌋₊).filter (fun f => f.Coprime (d*v)),
        r v*beta f*(nu a*alpha e)*PRZZKloostermanInputs.e (-((a:ℝ)*inverseResidue v (h*e*f)/v))

theorem coprimeCoeff_norm (d n : ℕ) (f : ℕ → ℂ) :
    ‖coprimeCoeff d f n‖ ≤ ‖f n‖ := by
  unfold coprimeCoeff
  split_ifs <;> simp

private theorem sum_if {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p] (f : ι → ℂ) :
    (∑ i ∈ s, if p then f i else 0) = if p then ∑ i ∈ s, f i else 0 := by
  by_cases hp : p <;> simp [hp]

theorem sourceSum_eq (A E F V : ℝ) (h d : ℕ) (r beta nu alpha : ℕ → ℂ) :
    sourceSum A E F V h d r beta nu alpha =
      negativeBlock V F A E h r (coprimeCoeff d beta) nu (coprimeCoeff d alpha) := by
  unfold sourceSum negativeBlock
  simp only [sum_filter,mul_sum,mul_ite,mul_zero]
  simp_rw [← sum_if]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simp_rw [sum_comm (s := Icc 1 ⌊E⌋₊) (t := Icc 1 ⌊F⌋₊)]
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro e he
  have hvf : v.Coprime f ↔ f.Coprime v := Nat.coprime_comm
  by_cases hvh : v.Coprime h <;> by_cases hfd : f.Coprime d <;>
    by_cases hfv : f.Coprime v <;> by_cases hed : e.Coprime d <;>
    by_cases hev : e.Coprime v <;>
    simp [coprimeCoeff,Nat.coprime_mul_iff_right,hvh,hfd,hfv,hed,hev,
      hvf] <;> ring_nf <;> split_ifs <;> simp_all

/-- DI controls this literal separated sum with the original divisor
restriction still present. No boundedness of the source coefficients is
asserted: the four envelopes are explicit, uniform inputs. -/
theorem sourceSum_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A E F V : ℝ, 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ h d : ℕ, 1 ≤ h → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) → (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) → (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) →
      ‖sourceSum A E F V h d r beta nu alpha‖ ≤ R*S*(P*Q)*K*diBound ε V F A E h := by
  obtain ⟨K,hK,hb⟩ := block_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro A E F V hA hE hF hV h d hh R S P Q hR hS hP hQ r beta nu alpha hr hbeta hnu halpha
  rw [sourceSum_eq,negativeBlock_eq,Complex.norm_conj]
  apply hb V F A E hV hF hA hE h hh R S P Q hR hS hP hQ
  · simpa only [Complex.norm_conj] using hr
  · intro f hf
    simpa only [Complex.norm_conj] using (coprimeCoeff_norm d f beta).trans (hbeta f hf)
  · simpa only [Complex.norm_conj] using hnu
  · intro e he
    simpa only [Complex.norm_conj] using (coprimeCoeff_norm d e alpha).trans (halpha e he)

#print axioms coprimeCoeff_norm
#print axioms sourceSum_eq
#print axioms sourceSum_bound
end XiPrime8845.PRZZSourceTypeII
