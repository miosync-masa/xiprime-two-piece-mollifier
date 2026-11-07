import PRZZDiscardedOuter

/-! Cutoff values, not only their support indicators, in the discarded
sum. A fixed profile bound precedes both dilation scales and height. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZValuedCutoffs
open PRZZDiscardedOuter
set_option maxHeartbeats 4000000

theorem tail_scale (F : ℝ → ℂ) (js : List ℕ) (N : ℕ) (T : ℝ)
    (alpha beta sigma c : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) :
    tailError F js N T alpha beta sigma s (fun u v p => c*w u v p) =
      c*tailError F js N T alpha beta sigma s w := by
  unfold tailError row
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Arbitrary bounded outer multipliers may now contain the actual
cutoff values. The loss is linear in their common bound, not in the
number of arithmetic pairs. -/
theorem multiplier_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (N : ℕ) (A B alpha beta : ℂ) (T U : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re → 0 ≤ U →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ)
        (g : ℕ → ℕ → ℂ),
      Geometry N T eps s w → (∀ u v, ‖g u v‖ ≤ U) →
      ‖tailError F js N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (fun u v p => g u v*w u v p)‖ ≤ (U+1)*E*T^(-power) := by
  obtain ⟨E,hE,hh⟩ := actual_negligible F hF hsF hsupp js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro N A B alpha beta T U hN hNT hT hL hsep ha hb hU s w g hw hg
  have hU1 : 0 < U+1 := by linarith
  have hUc : ((U+1:ℝ):ℂ) ≠ 0 := by exact_mod_cast hU1.ne'
  let wn := fun u v p => (g u v/((U+1:ℝ):ℂ))*w u v p
  have hn : Geometry N T eps s wn := by
    constructor
    · intro u hu v hv p hp
      dsimp [wn]
      rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU1]
      have hg1 : ‖g u v‖/(U+1) ≤ 1 := (div_le_one hU1).mpr (by linarith [hg u v])
      exact (mul_le_mul hg1 (hw.1 u hu v hv p hp) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    · intro u hu v hv p hp hnon
      exact hw.2 u hu v hv p hp (mul_ne_zero_iff.mp hnon).2
  have hbound := hh N A B alpha beta T hN hNT hT hL hsep ha hb s wn hn
  have heq : (fun u v p => g u v*w u v p) =
      (fun u v p => ((U+1:ℝ):ℂ)*wn u v p) := by
    funext u v p
    dsimp [wn]
    field_simp
  rw [heq,tail_scale,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU1]
  exact (mul_le_mul_of_nonneg_left hbound hU1.le).trans_eq (by ring)

/-- Both actual cutoff amplitudes have a scale-independent joint bound.
Continuity and compact support suffice; no derivative estimate is needed
for these outer, time-independent factors. -/
theorem cutoff_pair_uniform (G H : ℝ → ℂ) (hG : Continuous G) (hH : Continuous H)
    (hsG : HasCompactSupport G) (hsH : HasCompactSupport H) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ Q R x y : ℝ,
      ‖PRZZMellinSeparation.scaledCutoff G Q x *
        PRZZMellinSeparation.scaledCutoff H R y‖ ≤ U := by
  obtain ⟨C,hC⟩ := hsG.exists_bound_of_continuous hG
  obtain ⟨D,hD⟩ := hsH.exists_bound_of_continuous hH
  refine ⟨max C 0*max D 0,by positivity,?_⟩
  intro Q R x y
  rw [norm_mul]
  exact mul_le_mul ((hC _).trans (le_max_left _ _)) ((hD _).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

/-- Substitute both valued scaled cutoffs into the actual coefficient
sum. The final constant is chosen before either cutoff scale. -/
theorem valued_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H)
    (hsG : HasCompactSupport G) (hsH : HasCompactSupport H)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (N : ℕ) (A B alpha beta : ℂ) (T Q R d : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      Geometry N T eps s w →
      ‖tailError F js N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (fun u v p => (PRZZMellinSeparation.scaledCutoff G Q (d*u)*
          PRZZMellinSeparation.scaledCutoff H R (d*v))*w u v p)‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,hh⟩ := multiplier_negligible F hF hsF hsupp js eps power r he hr
  obtain ⟨U,hU,hg⟩ := cutoff_pair_uniform G H hG hH hsG hsH
  refine ⟨(U+1)*E,by positivity,?_⟩
  intro N A B alpha beta T Q R d hN hNT hT hL hsep ha hb s w hw
  exact hh N A B alpha beta T U hN hNT hT hL hsep ha hb hU s w _ hw
    (fun u v => hg Q R (d*u) (d*v))

#print axioms tail_scale
#print axioms multiplier_negligible
#print axioms cutoff_pair_uniform
#print axioms valued_negligible
end XiPrime8845.PRZZValuedCutoffs
