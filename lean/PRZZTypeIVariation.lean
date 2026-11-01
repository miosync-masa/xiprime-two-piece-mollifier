import PRZZSmoothWeights

/-! Sample the smooth Type I weight on a retained integer interval.
Sharp endpoints are handled by the Abel endpoint term, not differentiated.
Power/log envelopes remain explicit; the cutoff constants are uniform in
its scale and in kappa. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set
namespace XiPrime8845.PRZZTypeIVariation
open PRZZTypeI PRZZTypeIWeights PRZZSmoothWeights PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem sampled_variation (f : ℝ → ℂ) (a F C D : ℝ) (H : ℕ)
    (hF : 0 < F) (hD : 0 ≤ D) (hH : (H:ℝ) ≤ 2*F)
    (hend : ‖f (a+(H-1:ℕ))‖ ≤ C)
    (hf : ∀ x ∈ Icc a (a+H), HasDerivAt f (deriv f x) x)
    (hd : ∀ x ∈ Icc a (a+H), ‖deriv f x‖ ≤ D/F) :
    variation (fun k => f (a+k)) H ≤ C+2*D := by
  apply variation_le _ H C D F hF hD hH hend
  intro k hk
  have hk' : k+1 ≤ H := by have := mem_range.mp hk; omega
  have hkR : (k:ℝ)+1 ≤ H := by exact_mod_cast hk'
  have hh := sampled_step f (deriv f) a (a+H) (D/F) hf hd (a+k)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (by linarith)
  simpa [Nat.cast_add,Nat.cast_one,add_assoc] using hh

theorem source_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hs : HasCompactSupport F0) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ N kappa a F P L : ℝ,
      ∀ z : ℂ, ∀ j H : ℕ, 0 < F → F ≤ a → 0 ≤ P → 0 ≤ L → (H:ℝ) ≤ 2*F →
      (∀ x ∈ Icc a (a+H), ‖(x:ℂ)^z‖ ≤ P ∧ |Real.log x| ≤ L) →
      variation (fun k => sourceWeight z j kappa (scaledCutoff F0 N) (a+k)) H ≤
        P*L^j*C0+2*(P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1)) := by
  obtain ⟨C0,C1,hC0,hC1,hcut⟩ := cutoff_bounds F0 hf hs
  refine ⟨C0,C1,hC0,hC1,?_⟩
  intro N kappa a F P L z j H hF ha hP hL hH henv
  let w := sourceWeight z j kappa (scaledCutoff F0 N)
  let D := P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hder (x : ℝ) (hx : x ∈ Icc a (a+H)) : HasDerivAt w (deriv w x) x := by
    have hx0 : 0 < x := hF.trans_le (ha.trans hx.1)
    exact (source_hasDerivAt z j kappa x _ _ hx0
      ((scaled_hasDerivAt F0 hf N (kappa*x)).differentiableAt.hasDerivAt)).differentiableAt.hasDerivAt
  apply sampled_variation w a F (P*L^j*C0) D H hF hD hH
  · have hx : a+(H-1:ℕ) ∈ Icc a (a+H) := by
      constructor
      · have := Nat.cast_nonneg (α := ℝ) (H-1); linarith
      · have hh : ((H-1:ℕ):ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
        linarith
    dsimp [w,sourceWeight]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (henv _ hx).1
      (pow_le_pow_left₀ (abs_nonneg _) (henv _ hx).2 j) (by positivity) hP)
      (hcut N (kappa*(a+(H-1:ℕ)))).1 (norm_nonneg _) (by positivity)
  · exact hder
  · intro x hx
    have hx0 : 0 < x := hF.trans_le (ha.trans hx.1)
    have hd := source_hasDerivAt z j kappa x _ _ hx0
      ((scaled_hasDerivAt F0 hf N (kappa*x)).differentiableAt.hasDerivAt)
    have hb := source_derivative_bound z j kappa x _ _ P L C0 C1 hx0 hP hL hC0 hC1
      (henv x hx).1 (henv x hx).2 (hcut N (kappa*x)).1
      (by simpa only [Complex.ofReal_mul] using (hcut N (kappa*x)).2)
    rw [← hd.deriv] at hb
    change ‖(x:ℂ)*deriv w x‖ ≤ D at hb
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0] at hb
    apply (le_div_iff₀ hF).mpr
    nlinarith [norm_nonneg (deriv w x),ha.trans hx.1]

#print axioms sampled_variation
#print axioms source_variation
end XiPrime8845.PRZZTypeIVariation
