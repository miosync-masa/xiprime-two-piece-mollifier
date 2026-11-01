import Mathlib

/-! Mellin separation on Re(s)=0 with the normalization 1/(2*pi).
Inversion is a theorem, not an input equality. Mellin convergence and
vertical L1 integrability remain explicit analytic hypotheses on F; this
module does not supply their uniform constants for PRZZ's cutoff family.
Finite coefficients and all original cutoffs can be retained in the index set. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Finset Complex
namespace XiPrime8845.PRZZMellinSeparation
set_option maxHeartbeats 1000000

def twist (x t : ℝ) : ℂ := (x:ℂ)^(-((t:ℂ)*Complex.I))

theorem twist_norm (x t : ℝ) (hx : 0 < x) : ‖twist x t‖ = 1 := by
  simp [twist,Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem twist_mul (x y t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    twist (x*y) t = twist x t*twist y t := by
  unfold twist
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hx hy]

theorem twist_continuous (x : ℝ) (hx : 0 < x) : Continuous (twist x) := by
  unfold twist
  have hn : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem kernel_integrable (F : ℝ → ℂ) (hF : VerticalIntegrable (mellin F) 0)
    (x : ℝ) (hx : 0 < x) : Integrable (fun t : ℝ => mellin F (t*I)*twist x t) := by
  have hi : Integrable (fun t : ℝ => mellin F (t*I)) := by simpa [VerticalIntegrable] using hF
  exact hi.mul_bdd (twist_continuous x hx).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => (twist_norm x t hx).le))

theorem inversion (F : ℝ → ℂ) (hf : MellinConvergent F 0)
    (hF : VerticalIntegrable (mellin F) 0) (x : ℝ) (hx : 0 < x) (hc : ContinuousAt F x) :
    F x = (1/(2*Real.pi):ℂ)*(∫ t : ℝ, mellin F (t*I)*twist x t) := by
  have h := (mellinInv_mellin_eq 0 F hx hf hF hc).symm
  simpa [mellinInv,twist,smul_eq_mul,mul_comm] using h

/-- Literal F(d*e*f) separation. No endpoint or coefficient is moved. -/
theorem separate (F : ℝ → ℂ) (hf : MellinConvergent F 0)
    (hF : VerticalIntegrable (mellin F) 0) (d x y : ℝ)
    (hd : 0 < d) (hx : 0 < x) (hy : 0 < y) (hc : ContinuousAt F (d*x*y)) :
    F (d*x*y) = (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
      mellin F (t*I)*twist d t*twist x t*twist y t) := by
  rw [inversion F hf hF _ (by positivity) hc]
  simp_rw [twist_mul _ y _ (mul_pos hd hx).le hy.le,twist_mul d x _ hd.le hx.le,mul_assoc]

/-- Finite sum / Mellin integral exchange; the same F is used throughout. -/
theorem sum_separate {ι : Type*} (s : Finset ι) (a : ι → ℂ) (x y : ι → ℝ)
    (d : ℝ) (hd : 0 < d) (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (F : ℝ → ℂ) (hf : MellinConvergent F 0) (hF : VerticalIntegrable (mellin F) 0)
    (hc : ∀ i ∈ s, ContinuousAt F (d*x i*y i)) :
    (∑ i ∈ s, a i*F (d*x i*y i)) = (1/(2*Real.pi):ℂ)*
      (∫ t : ℝ, mellin F (t*I)*twist d t*(∑ i ∈ s, a i*twist (x i) t*twist (y i) t)) := by
  have hi (i : ι) (h : i ∈ s) : Integrable (fun t : ℝ => a i*(mellin F (t*I)*twist (d*x i*y i) t)) :=
    (kernel_integrable F hF _ (mul_pos (mul_pos hd (hx i h)) (hy i h))).const_mul _
  calc
    _ = (1/(2*Real.pi):ℂ)*∑ i ∈ s, ∫ t : ℝ, a i*(mellin F (t*I)*twist (d*x i*y i) t) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i h
      rw [inversion F hf hF _ (mul_pos (mul_pos hd (hx i h)) (hy i h)) (hc i h),integral_const_mul]
      ring
    _ = _ := by
      rw [← integral_finsetSum s hi]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [mul_sum]
      apply sum_congr rfl
      intro i h
      rw [twist_mul _ _ _ (mul_pos hd (hx i h)).le (hy i h).le,
        twist_mul _ _ _ hd.le (hx i h).le]
      ring

/-- The analytic cost of Mellin separation is its L1 norm, explicitly retained. -/
theorem integral_budget (F : ℝ → ℂ) (hF : VerticalIntegrable (mellin F) 0)
    (d B : ℝ) (hd : 0 < d) (S : ℝ → ℂ) (hS : AEStronglyMeasurable S)
    (hB : ∀ t, ‖S t‖ ≤ B) :
    ‖(1/(2*Real.pi):ℂ)*(∫ t : ℝ, mellin F (t*I)*twist d t*S t)‖ ≤
      (1/(2*Real.pi))*B*(∫ t : ℝ, ‖mellin F (t*I)‖) := by
  have hi := (kernel_integrable F hF d hd).mul_bdd hS (Filter.Eventually.of_forall hB)
  have hm : Integrable (fun t : ℝ => ‖mellin F (t*I)‖) := by
    have hh : Integrable (fun t : ℝ => mellin F (t*I)) := by simpa [VerticalIntegrable] using hF
    exact hh.norm
  rw [norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  have hh : (∫ t : ℝ, ‖mellin F (t*I)*twist d t*S t‖) ≤
      ∫ t : ℝ, ‖mellin F (t*I)‖*B := by
    apply integral_mono hi.norm (hm.mul_const B)
    intro t
    dsimp only
    rw [norm_mul,norm_mul,twist_norm d t hd,mul_one]
    exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by rw [integral_mul_const]; ring)

/-- The standard scaled cutoff F_N(x)=phi(x/N); its Mellin L1 cost does
not depend on N on Re(s)=0. The one fixed profile still needs L1 decay. -/
def scaledCutoff (phi : ℝ → ℂ) (N x : ℝ) : ℂ := phi (N⁻¹*x)

theorem scaled_mellin (phi : ℝ → ℂ) (N t : ℝ) (hN : 0 < N) :
    mellin (scaledCutoff phi N) (t*I) = twist N⁻¹ t*mellin phi (t*I) := by
  change mellin (fun x => phi (N⁻¹*x)) (t*I) = _
  simpa only [twist,smul_eq_mul] using
    mellin_comp_mul_left phi (t*I) (inv_pos.mpr hN)

theorem scaled_mellin_norm (phi : ℝ → ℂ) (N t : ℝ) (hN : 0 < N) :
    ‖mellin (scaledCutoff phi N) (t*I)‖ = ‖mellin phi (t*I)‖ := by
  rw [scaled_mellin phi N t hN,norm_mul,twist_norm _ _ (inv_pos.mpr hN),one_mul]

theorem scaled_verticalIntegrable (phi : ℝ → ℂ) (N : ℝ) (hN : 0 < N)
    (hphi : VerticalIntegrable (mellin phi) 0) :
    VerticalIntegrable (mellin (scaledCutoff phi N)) 0 := by
  have h := kernel_integrable phi hphi N⁻¹ (inv_pos.mpr hN)
  unfold VerticalIntegrable
  simp only [Complex.ofReal_zero, zero_add]
  simp_rw [scaled_mellin phi N _ hN]
  simpa only [mul_comm] using h

theorem scaled_mellin_mass (phi : ℝ → ℂ) (N : ℝ) (hN : 0 < N) :
    (∫ t : ℝ, ‖mellin (scaledCutoff phi N) (t*I)‖) = ∫ t : ℝ, ‖mellin phi (t*I)‖ := by
  simp_rw [scaled_mellin_norm phi N _ hN]

#print axioms twist_mul
#print axioms inversion
#print axioms separate
#print axioms sum_separate
#print axioms integral_budget
#print axioms scaled_mellin
#print axioms scaled_verticalIntegrable
#print axioms scaled_mellin_mass
end XiPrime8845.PRZZMellinSeparation
