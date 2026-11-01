import PRZZNuBounds

/-! Both signed frequency branches with their actual nu coefficients.
The negative frequency has the positive exponential phase. Conjugation
acts on every coefficient, not on nu alone. The divisor restrictions
remain present and DI is an explicit hypothesis. -/
noncomputable section
open scoped BigOperators
open Finset Complex
namespace XiPrime8845.PRZZSignedTypeII
open PRZZKloostermanInputs PRZZSourceTypeII PRZZTypeII PRZZNuCoefficient
set_option maxHeartbeats 2000000

def sourcePlus (A E F V : ℝ) (h d : ℕ) (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime h),
    ∑ e ∈ (Icc 1 ⌊E⌋₊).filter (fun e => e.Coprime (d*v)),
      ∑ f ∈ (Icc 1 ⌊F⌋₊).filter (fun f => f.Coprime (d*v)),
        r v*beta f*(nu a*alpha e)*PRZZKloostermanInputs.e ((a:ℝ)*inverseResidue v (h*e*f)/v)

theorem sourcePlus_conj (A E F V : ℝ) (h d : ℕ) (r beta nu alpha : ℕ → ℂ) :
    sourcePlus A E F V h d r beta nu alpha =
      starRingEnd ℂ (sourceSum A E F V h d (fun n => starRingEnd ℂ (r n))
        (fun n => starRingEnd ℂ (beta n)) (fun n => starRingEnd ℂ (nu n))
        (fun n => starRingEnd ℂ (alpha n))) := by
  simp [sourcePlus,sourceSum,conj_e]

theorem sourcePlus_eq (A E F V : ℝ) (h d : ℕ) (r beta nu alpha : ℕ → ℂ) :
    sourcePlus A E F V h d r beta nu alpha =
      block V F A E h r (coprimeCoeff d beta) nu (coprimeCoeff d alpha) := by
  rw [sourcePlus_conj,sourceSum_eq,negativeBlock_eq]
  simp [coprimeCoeff,apply_ite]
  rfl

def signedSource (s : Finset (ℤ × ℕ)) (x y A E F V : ℝ) (h d : ℕ)
    (r beta alpha : ℕ → ℂ) : ℂ :=
  sourceSum A E F V h d r beta (fun k => nu s x y k) alpha +
    sourcePlus A E F V h d r beta (fun k => nu s x y (-(k:ℤ))) alpha

/-- One pair of constants controls both signs, before all real integration
variables, finite cutoffs, and coefficient sequences. -/
theorem signedSource_bound (hDI : DeshouillersIwaniecLemma1)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (s : Finset (ℤ × ℕ)), (∀ q ∈ s, 0 < q.2) →
      ∀ A E F V : ℝ, 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ h d : ℕ, 1 ≤ h → ∀ R S Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < Q →
      ∀ r beta alpha : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) →
      (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) → ∀ x y : ℝ,
      ‖signedSource s x y A E F V h d r beta alpha‖ ≤
        2*(R*S*((C*A^η)*Q)*K*diBound ε V F A E h) := by
  obtain ⟨C,hC,hnu⟩ := PRZZNuBounds.nu_subpower η hη
  obtain ⟨K,hK,hbound⟩ := two_sided_bound hDI ε hε
  refine ⟨C,K,hC,hK,?_⟩
  intro s hs A E F V hA hE hF hV h d hh R S Q hR hS hQ r beta alpha hr hb ha x y
  have hn (k : ℕ) (hk : k ∈ Icc 1 ⌊A⌋₊) :
      ‖nu s x y (k:ℤ)‖ ≤ C*A^η ∧ ‖nu s x y (-(k:ℤ))‖ ≤ C*A^η := by
    have hk0 : (k:ℤ) ≠ 0 := by exact_mod_cast (show 0 < k from (mem_Icc.mp hk).1).ne'
    have hkA : (k:ℝ) ≤ A := (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans (Nat.floor_le (by linarith))
    have hu := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ k) hkA hη.le) hC.le
    constructor
    · have hp := hnu s hs x y k hk0
      simp only [Int.natAbs_natCast] at hp
      exact hp.trans hu
    · have hm := hnu s hs x y (-(k:ℤ)) (neg_ne_zero.mpr hk0)
      simp only [Int.natAbs_neg,Int.natAbs_natCast] at hm
      exact hm.trans hu
  rw [signedSource,sourceSum_eq,sourcePlus_eq]
  apply hbound V F A E hV hF hA hE h hh R S (C*A^η) Q hR hS
    (mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)) hQ
  · exact hr
  · intro f hf; exact (coprimeCoeff_norm d f beta).trans (hb f hf)
  · exact fun k hk => (hn k hk).1
  · exact fun k hk => (hn k hk).2
  · intro e he; exact (coprimeCoeff_norm d e alpha).trans (ha e he)

#print axioms sourcePlus_conj
#print axioms sourcePlus_eq
#print axioms signedSource_bound
end XiPrime8845.PRZZSignedTypeII
