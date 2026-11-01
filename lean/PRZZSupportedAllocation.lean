import PRZZSupportedSplit
import PRZZSharpAggregation

/-! Source coefficient allocation on the proved supported h set.
Arbitrary analytic weights stay inside the residual block. Extracting G
precedes HB expansion: no multiplicativity of a single HB branch is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSupportedAllocation
open PRZZSupportedSplit PRZZCoefficientSeparation PRZZGCoefficient
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def residual (N d : ℕ) (js : List ℕ) (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  ∑ r ∈ Icc 1 N, if d.Coprime r ∧ d*(h*r) ≤ N then
    (coefficient js r:ℂ)*F (h*r) else 0

private theorem evaluate_sum (ts : List (List ℕ × List ℕ)) (N d h : ℕ) (F : ℕ → ℂ) :
    (∑ r ∈ Icc 1 N, if d.Coprime r ∧ d*(h*r) ≤ N then
      (evaluate ts (d*h) r:ℂ)*F (h*r) else 0) =
    (ts.map (fun q => (coefficient q.1 (d*h):ℂ)*residual N d q.2 F h)).sum := by
  induction ts with
  | nil => simp [evaluate]
  | cons q ts ih =>
    simp only [evaluate,List.map_cons,List.sum_cons,Complex.ofReal_add,add_mul] at ih ⊢
    rw [show (∑ r ∈ Icc 1 N,
      if d.Coprime r ∧ d*(h*r) ≤ N then
        ((coefficient q.1 (d*h)*coefficient q.2 r:ℝ):ℂ)*F (h*r)+
          (((ts.map (fun t => coefficient t.1 (d*h)*coefficient t.2 r)).sum:ℝ):ℂ)*F (h*r)
      else 0) =
        (∑ r ∈ Icc 1 N, if d.Coprime r ∧ d*(h*r) ≤ N then
          ((coefficient q.1 (d*h)*coefficient q.2 r:ℝ):ℂ)*F (h*r) else 0)+
        (∑ r ∈ Icc 1 N, if d.Coprime r ∧ d*(h*r) ≤ N then
          (((ts.map (fun t => coefficient t.1 (d*h)*coefficient t.2 r)).sum:ℝ):ℂ)*F (h*r) else 0) by
      rw [← sum_add_distrib]; apply sum_congr rfl; intros; split_ifs <;> simp]
    rw [ih]
    congr 1
    simp only [residual,mul_sum]
    apply sum_congr rfl
    intros
    split_ifs <;> simp [Complex.ofReal_mul,mul_assoc]

private theorem sum_list_swap {ι : Type*} (s : Finset ι) (ts : List (List ℕ × List ℕ))
    (F : ι → (List ℕ × List ℕ) → ℂ) :
    (∑ i ∈ s, (ts.map (F i)).sum) = (ts.map (fun q => ∑ i ∈ s, F i q)).sum := by
  induction ts with
  | nil => simp
  | cons q ts ih => simp only [List.map_cons,List.sum_cons,sum_add_distrib,ih]

/-- Exact supported h decomposition of the original coefficient with any
remaining weight F. This includes frequency phases, conjugated second
coefficients and dyadic masks by substitution, not by an envelope. -/
theorem weighted_source (N d : ℕ) (hd : 1 ≤ d) (js : List ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, if d*n ≤ N then (coefficient js (d*n):ℂ)*F n else 0) =
      ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
        (sourceG q.1 0 0 d h:ℂ)*residual N d q.2 F h)).sum := by
  rw [sum_cutoff d N hd]
  have he : (∑ h ∈ hSupport N d, ∑ r ∈ Icc 1 N,
      if d.Coprime r ∧ d*(h*r) ≤ N then (coefficient js (d*(h*r)):ℂ)*F (h*r) else 0) =
      ∑ h ∈ hSupport N d, ((allocations js).map (fun q =>
        (coefficient q.1 (d*h):ℂ)*residual N d q.2 F h)).sum := by
    apply sum_congr rfl
    intro h hh
    rw [← evaluate_sum]
    apply sum_congr rfl
    intro r hr
    split_ifs with hc
    · rw [source_allocation js d h r (mem_hSupport N d h hh).2.2 hc.1]
    · rfl
  rw [he,sum_list_swap]
  simp [sourceG]

/-- The actual supported set discharges the support hypotheses of the
proved h average. Only the balanced residual DI estimate remains an input. -/
theorem residual_average (js : List ℕ) (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      ∀ (ks : List ℕ) (X A V B : ℝ) (E : ℕ → ℝ) (F : ℕ → ℂ),
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ B →
      (∀ h ∈ hSupport N d, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      (∀ h ∈ hSupport N d, ‖residual N d ks F h‖ ≤
        B*PRZZDISeven.seven h (E h) A (X/h) V) →
      ‖∑ h ∈ hSupport N d, (sourceG js 0 0 d h:ℂ)*residual N d ks F h‖ ≤
        B*(PRZZDISeven.envelope X A V*(C*(d:ℝ)^η*(N:ℝ)^β)) := by
  obtain ⟨C,hC,h⟩ := PRZZSharpAggregation.source_h_sum js 0 η β hη hβ
  refine ⟨C,hC,?_⟩
  intro N d hN hd ks X A V B E F hX hA hV hB hE hb
  exact h 0 d N le_rfl hd hN (hSupport N d) X A V B E hX hA hV hB
    (fun h hh => mem_hSupport N d h hh) hE _ hb

#print axioms residual_average
#print axioms weighted_source
end XiPrime8845.PRZZSupportedAllocation
