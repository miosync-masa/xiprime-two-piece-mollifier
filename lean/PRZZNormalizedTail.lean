import PRZZJetUniform

/-! The Poisson Jacobian is retained in absolute tails and in arithmetic
time aggregation. The analytic common envelope remains explicitly named. -/
noncomputable section
open scoped BigOperators FourierTransform ContDiff
open MeasureTheory Set
namespace XiPrime8845.PRZZNormalizedTail
set_option maxHeartbeats 2000000

/-- Exact q-power after the Poisson Jacobian: q^(n+1), not q^(n+2). -/
theorem normalized_budget (B q : ℝ) (n H : ℕ) (hq : 0 < q) :
    q⁻¹*(2*B*(q/(2*Real.pi))^(n+2)/((H:ℝ)+1)^n*PRZZWeightTail.squareMass) =
      2*B*q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass := by
  rw [div_pow,show n+2 = (n+1)+1 by omega,pow_succ q]
  field_simp

theorem normalized_tail (f : ℕ → ℝ) (B q : ℝ) (n H : ℕ) (hq : 0 < q)
    (hb : (∑' j, f j) ≤ 2*B*(q/(2*Real.pi))^(n+2)/((H:ℝ)+1)^n*PRZZWeightTail.squareMass) :
    (∑' j, q⁻¹*f j) ≤
      2*B*q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass := by
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hq.le)).trans_eq
    (normalized_budget B q n H hq)

/-- Actual coefficient pairs and all finite masks, with the Poisson
normalization inside each summand. Compact time supplies integrability. -/
theorem arithmetic_time (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l))
    (u : ℕ × ℕ → ℝ → ℂ) (B T q : ℝ) (hB : 0 ≤ B) (hq : 0 < q)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hu : ∀ t ∈ Icc T (2*T), ∀ p ∈ s, ‖u p t‖ ≤ B) :
    ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ p ∈ s,
      (((PRZZGCoefficient.coefficient js p.1:ℂ)*star (PRZZGCoefficient.coefficient js p.2:ℂ))*(u p t/(q:ℂ)))/
        ((p.1:ℂ)*(p.2:ℂ)))‖ ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*(B/q)*
        (∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  apply PRZZSourceTailBudget.arithmetic_time_compact js N j l hN s hs
    (fun p t => u p t/(q:ℂ)) (B/q) T (by positivity) Phi hPhi
  intro t ht p hp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
  exact div_le_div_of_nonneg_right (hu t ht p hp) hq.le

/-- Actual Fourier tails with uniform shift/phase cap and Poisson Jacobian.
All spatial integration is discharged; the scale and shift budgets are explicit. -/
theorem uniform_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (M k omega R q Z P s : ℝ) (z sigma : ℂ),
      0 < M → 0 < k → 0 ≤ R → 0 < q → sigma ≠ 0 →
      0 ≤ Z → ‖z‖ ≤ Z → ‖z‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤ P →
      1/‖sigma‖^2 ≤ s →
      (∀ x ∈ Icc (M/2) (3*M), |omega/x| ≤ R) →
      let f := PRZZFullWeightSmooth.weight F M k omega z sigma
      let B := (3*M-M/2)*(PRZZJetUniform.uniformCap C D E a k M R Z P s (n+2)/(M/2)^(n+2))
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
      Summable tail ∧ (∑' j, q⁻¹*tail j) ≤
        2*B*q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass := by
  obtain ⟨C,D,E,hpos,h⟩ := PRZZEnvelopeMass.tail_bound F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H M k omega R q Z P s z sigma hM hk hR hq hsigma hZ hz hP hsig hp
  have ht := h n H M k omega R q z sigma hM hk hR hq hsigma hp
  refine ⟨ht.1,?_⟩
  apply normalized_tail _ _ q n H hq
  apply ht.2.trans
  have hc := PRZZJetUniform.cap_uniform C D E a k M R _ Z P s z sigma (n+2)
    hpos hk.le hR hZ hz hP hsig
  have hm : 0 ≤ 3*M-M/2 := by linarith
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc
    (show 0 ≤ (M/2)^(n+2) by positivity)) hm
  have hsquare : 0 ≤ PRZZWeightTail.squareMass := tsum_nonneg (fun j => by positivity)
  dsimp only at *
  gcongr

/-- Finite retained frequency sums use the absolute tail, so no separate
bound on the arithmetic summand is assumed. The uniform tail mass is explicit. -/
theorem tail_arithmetic_time (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l))
    (freq : Finset ℕ) (f : ℕ × ℕ → ℝ → ℕ → ℂ) (B T q : ℝ)
    (hB : 0 ≤ B) (hq : 0 < q) (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hf : ∀ t ∈ Icc T (2*T), ∀ p ∈ s, Summable (fun h => ‖f p t h‖))
    (hb : ∀ t ∈ Icc T (2*T), ∀ p ∈ s, (∑' h, ‖f p t h‖) ≤ B) :
    ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ p ∈ s,
      (((PRZZGCoefficient.coefficient js p.1:ℂ)*star (PRZZGCoefficient.coefficient js p.2:ℂ))*
        ((∑ h ∈ freq, f p t h)/(q:ℂ)))/((p.1:ℂ)*(p.2:ℂ)))‖ ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*(B/q)*
        (∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  apply arithmetic_time js N j l hN s hs (fun p t => ∑ h ∈ freq, f p t h)
    B T q hB hq Phi hPhi
  intro t ht p hp
  apply (norm_sum_le _ _).trans
  exact (Summable.sum_le_tsum freq (fun h _ => norm_nonneg _) (hf t ht p hp)).trans (hb t ht p hp)

#print axioms tail_arithmetic_time
#print axioms uniform_tail
#print axioms normalized_budget
#print axioms normalized_tail
#print axioms arithmetic_time
end XiPrime8845.PRZZNormalizedTail
