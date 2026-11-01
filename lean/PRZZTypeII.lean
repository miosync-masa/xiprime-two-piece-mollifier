import PRZZKloostermanInputs

/-! Conditional DI adapter for separated Type II coefficients.
DI (C,D,U,V,rho) corresponds to PRZZ (v-bound,f-bound,a-bound,e-bound,h).
Zero coefficients can encode dyadic subintervals. This module retains the
DI envelope; it does not claim the seven-monomial simplification, Mellin
separation, or the Heath-Brown-to-dyadic combinatorial reduction. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTypeII
open PRZZKloostermanInputs
set_option maxHeartbeats 1000000

theorem diSum_const_mul (C D U V : ℝ) (rho : ℕ) (b : ℕ → ℕ → ℂ) (z : ℂ) :
    diSum C D U V rho (fun u v => z*b u v) = ‖z‖*diSum C D U V rho b := by
  simp only [diSum,mul_assoc,← mul_sum,norm_mul]

theorem di_bound_scaled (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ B : ℝ, 0 < B → ∀ b : ℕ → ℕ → ℂ,
      (∀ u ∈ Icc 1 ⌊U⌋₊, ∀ v ∈ Icc 1 ⌊V⌋₊, ‖b u v‖ ≤ B) →
        diSum C D U V rho b ≤ B*K*diBound ε C D U V rho := by
  obtain ⟨K,hK,h⟩ := hDI ε hε
  refine ⟨K,hK,?_⟩
  intro C D U V hC hD hU hV rho hrho B hB b hb
  let b' := fun u v => b u v/(B:ℂ)
  have hh := h C D U V hC hD hU hV rho hrho b' (by
    intro u hu v hv
    dsimp [b']
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
    exact (div_le_one hB).mpr (hb u hu v hv))
  have he : b = fun u v => (B:ℂ)*b' u v := by
    funext u v
    dsimp [b']
    have hBc : (B:ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp [hBc]
  rw [he,diSum_const_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left hh hB.le).trans_eq (by ring)

/-- Positive-frequency branch. Outer coefficients are NOT moved inside
DI's absolute value before taking the norm/triangle inequality. -/
def block (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    r c*beta d*(∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      (nu u*alpha v)*e ((u:ℝ)*inverseResidue c (rho*v*d)/c))

theorem block_le_diSum (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (R S : ℝ) (hR : 0 ≤ R) (_hS : 0 ≤ S)
    (hr : ∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R)
    (hb : ∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) :
    ‖block C D U V rho r beta nu alpha‖ ≤
      (R*S)*diSum C D U V rho (fun u v => nu u*alpha v) := by
  unfold block diSum
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro c hc
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro d hd
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hr c hc) (hb d (mem_filter.mp hd).1) (norm_nonneg _) hR) (norm_nonneg _)

theorem block_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) → (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ‖block C D U V rho r beta nu alpha‖ ≤
        R*S*(P*Q)*K*diBound ε C D U V rho := by
  obtain ⟨K,hK,h⟩ := di_bound_scaled hDI ε hε
  refine ⟨K,hK,?_⟩
  intro C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn ha
  apply (block_le_diSum C D U V rho r beta nu alpha R S hR hS hr hb).trans
  have hh := h C D U V hC hD hU hV rho hrho (P*Q) (mul_pos hP hQ)
    (fun u v => nu u*alpha v) (by
      intro u hu v hv
      rw [norm_mul]
      exact mul_le_mul (hn u hu) (ha v hv) (norm_nonneg _) hP.le)
  exact (mul_le_mul_of_nonneg_left hh (mul_nonneg hR hS)).trans_eq (by ring)

theorem conj_e (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp
  exact Or.inl (map_ofNat (starRingEnd ℂ) 2)

/-- The minus sign in PRZZ's positive-a branch is retained literally. -/
def negativeBlock (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    r c*beta d*(∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      (nu u*alpha v)*e (-((u:ℝ)*inverseResidue c (rho*v*d)/c)))

theorem negativeBlock_eq (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) :
    negativeBlock C D U V rho r beta nu alpha =
      starRingEnd ℂ (block C D U V rho (fun n => starRingEnd ℂ (r n))
        (fun n => starRingEnd ℂ (beta n)) (fun n => starRingEnd ℂ (nu n))
        (fun n => starRingEnd ℂ (alpha n))) := by
  simp [block,negativeBlock,conj_e]

/-- Both signs of a, with independent coefficients and one uniform constant.
Setting coefficients to zero retains strict frequency and dyadic cutoffs. -/
theorem two_sided_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nuPlus nuMinus alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nuPlus u‖ ≤ P) → (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nuMinus u‖ ≤ P) →
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ‖negativeBlock C D U V rho r beta nuPlus alpha + block C D U V rho r beta nuMinus alpha‖ ≤
        2*(R*S*(P*Q)*K*diBound ε C D U V rho) := by
  obtain ⟨K,hK,h⟩ := block_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nuPlus nuMinus alpha hr hb hp hm ha
  have hneg := h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    (fun n => starRingEnd ℂ (r n)) (fun n => starRingEnd ℂ (beta n))
    (fun n => starRingEnd ℂ (nuPlus n)) (fun n => starRingEnd ℂ (alpha n))
    (by simpa using hr) (by simpa using hb) (by simpa using hp) (by simpa using ha)
  have hpos := h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nuMinus alpha hr hb hm ha
  have hn : ‖negativeBlock C D U V rho r beta nuPlus alpha‖ ≤
      R*S*(P*Q)*K*diBound ε C D U V rho := by
    rw [negativeBlock_eq,Complex.norm_conj]
    exact hneg
  exact (norm_add_le _ _).trans ((add_le_add hn hpos).trans_eq (by ring))

#print axioms diSum_const_mul
#print axioms di_bound_scaled
#print axioms block_le_diSum
#print axioms block_bound
#print axioms negativeBlock_eq
#print axioms two_sided_bound
end XiPrime8845.PRZZTypeII
