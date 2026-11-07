import PRZZZeroDualExhaustion
import PRZZUnitModulusBudget

/-! Arbitrary-power decay of the actual q=1 resolved row tail at its
source frequency cutoff. Actual arithmetic factors remain displayed;
no generic tail bound or support witness is an estimate premise. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZResolvedTail
set_option maxHeartbeats 6000000

theorem arithmetic_row (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M t d Q : ℝ) (dn : ℕ) (z : PRZZAStar.Index)
      (alpha beta : ℂ) (c : ℕ → ℂ) (F1 F2 : ℝ → ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      d = dn → 0 < d → 0 < Q → Function.support F1 ⊆ Icc (Q/2) (3*Q) →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d →
      let alpha' := alpha/(Real.log T:ℂ)
      let beta' := beta/(Real.log T:ℂ)
      let c0 := PRZZUnfrozenPoisson.arithmetic c F1 F2 dn beta' alpha' z/((z.1.1:ℂ)*(z.1.2:ℂ))
      let J : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊
      ‖c0*(∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z
        alpha' beta' ((alpha+beta)/(Real.log T:ℂ)) J j t)‖ ≤
      ‖c0‖*‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A)) := by
  obtain ⟨K,hK,h⟩ := PRZZUnitModulusBudget.actual_tail_absorbed F hF hsF a b S r eD eH A
    ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro T M t d Q dn z alpha beta c F1 F2 hT hlog hM hMT hu hv hvT ht halpha hbeta hsep hdEq hd hQ hF1 hg
  dsimp only
  by_cases hz : F1 ((dn:ℝ)*z.1.1) = 0
  · simp [PRZZUnfrozenPoisson.arithmetic,hz]
  · have hleft := (hF1 hz).1
    rw [← hdEq] at hleft
    have hh := h T M t (PRZZCentralTail.residue z/z.1.2) d Q z alpha beta
      hT hlog hM hMT hu hv hvT ht halpha hbeta hsep hd hQ hleft hg
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

#print axioms arithmetic_row
/-- The row's actual arithmetic coefficient is held fixed in time. A
continuous weight may in particular be the supplied smooth Gamma weight. -/
theorem arithmetic_time (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M d Q : ℝ) (dn : ℕ) (z : PRZZAStar.Index)
      (alpha beta : ℂ) (c : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      d = dn → 0 < d → 0 < Q → Function.support F1 ⊆ Icc (Q/2) (3*Q) →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d → Continuous phi →
      let alpha' := alpha/(Real.log T:ℂ)
      let beta' := beta/(Real.log T:ℂ)
      let c0 := PRZZUnfrozenPoisson.arithmetic c F1 F2 dn beta' alpha' z/((z.1.1:ℂ)*(z.1.2:ℂ))
      let J : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊
      ‖∫ t in Icc T (2*T), phi t*(c0*(∑' j, PRZZFrozenTail.pair F M 1
        (PRZZCentralTail.residue z/z.1.2) z alpha' beta' ((alpha+beta)/(Real.log T:ℂ)) J j t))‖ ≤
      ‖c0‖*‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*
        (K*T^(-A))*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨K,hK,h⟩ := arithmetic_row F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro T M d Q dn z alpha beta c F1 F2 phi hT hlog hM hMT hu hv hvT halpha hbeta hsep hdEq hd hQ hF1 hg hp
  dsimp only
  let D := ‖PRZZUnfrozenPoisson.arithmetic c F1 F2 dn (beta/(Real.log T:ℂ))
    (alpha/(Real.log T:ℂ)) z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
    ‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A))
  have hi : IntegrableOn (fun t : ℝ => D*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hp.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (h T M t d Q dn z alpha beta c F1 F2 hT hlog hM hMT hu hv hvT ht
        halpha hbeta hsep hdEq hd hQ hF1 hg) (norm_nonneg _)).trans_eq (by dsimp [D]; ring)

#print axioms arithmetic_time
end XiPrime8845.PRZZResolvedTail
