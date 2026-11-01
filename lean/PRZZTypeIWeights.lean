import PRZZTypeI

/-! The literal power/log/cutoff weight in PRZZ's Type I sum.
Here z = sigma0 - 1/2 - alpha - w and kappa = d*h*e.
Derivative and discrete-variation costs are explicit; the uniform estimates
for the original cutoff family are not replaced by an unspecified T^epsilon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTypeIWeights
open PRZZTypeI PRZZKloostermanInputs
set_option maxHeartbeats 1000000

def sourceWeight (z : ℂ) (j : ℕ) (kappa : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^z*(Real.log x:ℂ)^j*F (kappa*x)

def sourceDerivative (z : ℂ) (j : ℕ) (kappa : ℝ) (F F' : ℝ → ℂ) (x : ℝ) : ℂ :=
  z*(x:ℂ)^(z-1)*(Real.log x:ℂ)^j*F (kappa*x)+
  (x:ℂ)^z*((j:ℂ)*(Real.log x:ℂ)^(j-1)/(x:ℂ))*F (kappa*x)+
  (x:ℂ)^z*(Real.log x:ℂ)^j*((kappa:ℂ)*F' (kappa*x))

theorem source_hasDerivAt (z : ℂ) (j : ℕ) (kappa x : ℝ) (F F' : ℝ → ℂ)
    (hx : 0 < x) (hF : HasDerivAt F (F' (kappa*x)) (kappa*x)) :
    HasDerivAt (sourceWeight z j kappa F) (sourceDerivative z j kappa F F' x) x := by
  have hp : HasDerivAt (fun y : ℝ => (y:ℂ)^z) (z*(x:ℂ)^(z-1)) x := by
    by_cases hz : z=0
    · simpa [hz] using hasDerivAt_const x (1:ℂ)
    · exact hasDerivAt_ofReal_cpow_const hx.ne' hz
  have hl := (Real.hasDerivAt_log hx.ne').ofReal_comp.pow j
  have hc := hF.scomp x ((hasDerivAt_id x).const_mul kappa)
  convert (hp.mul hl).mul hc using 1 <;> first
    | rfl
    | simp [sourceDerivative,Complex.real_smul,div_eq_mul_inv,add_mul]

/-- The scale-invariant quantity x*w'(x) exposes the (1+|w|) cost. -/
theorem source_derivative_bound (z : ℂ) (j : ℕ) (kappa x : ℝ) (F F' : ℝ → ℂ)
    (P L C0 C1 : ℝ) (hx : 0 < x) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (_hC0 : 0 ≤ C0) (_hC1 : 0 ≤ C1)
    (hp : ‖(x:ℂ)^z‖ ≤ P) (hl : |Real.log x| ≤ L)
    (hf : ‖F (kappa*x)‖ ≤ C0) (hf' : ‖(kappa*x:ℂ)*F' (kappa*x)‖ ≤ C1) :
    ‖(x:ℂ)*sourceDerivative z j kappa F F' x‖ ≤
      P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1) := by
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have he : (x:ℂ)*sourceDerivative z j kappa F F' x =
      (x:ℂ)^z*((z*(Real.log x:ℂ)^j+(j:ℂ)*(Real.log x:ℂ)^(j-1))*F (kappa*x)+
        (Real.log x:ℂ)^j*((kappa*x:ℂ)*F' (kappa*x))) := by
    unfold sourceDerivative
    rw [Complex.cpow_sub _ _ hxc,Complex.cpow_one]
    field_simp
  rw [he,norm_mul]
  have hlog : ‖(Real.log x:ℂ)‖ ≤ L := by simpa using hl
  apply mul_le_mul hp _ (norm_nonneg _) hP
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    apply mul_le_mul _ hf (norm_nonneg _) (by positivity)
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_pow,Complex.norm_natCast]
    gcongr
  · rw [norm_mul,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hlog _) hf' (norm_nonneg _) (pow_nonneg hL _)

theorem variation_le (w : ℕ → ℂ) (H : ℕ) (C D F : ℝ)
    (hF : 0 < F) (hD : 0 ≤ D) (hH : (H:ℝ) ≤ 2*F)
    (hend : ‖w (H-1)‖ ≤ C)
    (hstep : ∀ k ∈ range (H-1), ‖w (k+1)-w k‖ ≤ D/F) :
    variation w H ≤ C+2*D := by
  unfold variation
  have hs : (∑ k ∈ range (H-1), ‖w (k+1)-w k‖) ≤ (H-1:ℕ)*(D/F) := by
    simpa using sum_le_sum hstep
  have hsub : ((H-1:ℕ):ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
  have hh : ((H-1:ℕ):ℝ) ≤ 2*F := hsub.trans hH
  have hm := mul_le_mul_of_nonneg_right hh (div_nonneg hD hF.le)
  have he : 2*F*(D/F)=2*D := by field_simp
  rw [he] at hm
  linarith

/-- Derivatives on the original interval supply the discrete differences. -/
theorem sampled_step (f f' : ℝ → ℂ) (a b D : ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hd : ∀ x ∈ Set.Icc a b, ‖f' x‖ ≤ D)
    (x : ℝ) (hx : a ≤ x) (hx' : x+1 ≤ b) : ‖f (x+1)-f x‖ ≤ D := by
  have hs : Set.Icc x (x+1) ⊆ Set.Icc a b := by intro y hy; constructor <;> linarith [hy.1,hy.2]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => (hf y (hs hy)).hasDerivWithinAt)
    (fun y hy => hd y (hs ⟨hy.1,hy.2.le⟩)) (x+1) (show x+1 ∈ Set.Icc x (x+1) by constructor <;> linarith)
  simpa using hh

#print axioms source_hasDerivAt
#print axioms source_derivative_bound
#print axioms variation_le
#print axioms sampled_step
end XiPrime8845.PRZZTypeIWeights
