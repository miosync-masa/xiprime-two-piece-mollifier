import PRZZPowerJets
import PRZZReciprocalJets
import PRZZQuadraticJets

/-! Quantitative all-order Leibniz assembly for the actual spatial weight.
The three sequences of constants are chosen before every scale, shift and
frequency. The finite binomial convolution displays all parameter costs.
This does not yet assert the integrated Poisson tail or a PRZZ error exponent. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace XiPrime8845.PRZZFullWeightJets

def convolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*A i*B (n-i)

def envelope (C D E : ℕ → ℝ) (a k x R : ℝ) (z sigma : ℂ) (n : ℕ) : ℝ :=
  convolution
    (convolution
      (convolution C (fun i => ‖PRZZPowerJets.coeff z i‖*Real.exp (-z.re*Real.log x)))
      (fun i => PRZZReciprocalJets.envelope i R))
    (fun i => (D i+E i/‖sigma‖^2)*(k*x^2)^(-a)) n

theorem product_bound (f g : ℝ → ℂ) (n : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (A B : ℕ → ℝ)
    (hA : ∀ i ≤ n, ‖(x:ℂ)^i*iteratedDeriv i f x‖ ≤ A i)
    (hB : ∀ i ≤ n, ‖(x:ℂ)^i*iteratedDeriv i g x‖ ≤ B i) :
    ‖(x:ℂ)^n*iteratedDeriv n (fun y => f y*g y) x‖ ≤ convolution A B n := by
  rw [PRZZCutoffJets.scaled_leibniz f g n x hf hg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  simp only [norm_mul,Complex.norm_natCast] at hA hB ⊢
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hA i hi') (Nat.cast_nonneg _))
    (hB (n-i) (Nat.sub_le _ _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _)
      ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hA i hi')))

/-- Full frozen-time source weight. No derivative envelope is an input.
The complex power and reciprocal phase losses remain explicit. -/
theorem uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (N k omega x R : ℝ) (z sigma : ℂ),
      0 < k → 0 < x → sigma ≠ 0 → |omega/x| ≤ R →
      ‖(x:ℂ)^n*iteratedDeriv n (PRZZFullWeightSmooth.weight F N k omega z sigma) x‖ ≤
        envelope C D E a k x R z sigma n := by
  choose C hC hcut using PRZZCutoffJets.scaled_uniform F hF hsF
  choose D E hD hE hquad using (fun n => PRZZQuadraticJets.scaled_bound n a ha)
  refine ⟨C,D,E,fun n => ⟨hC n,hD n,hE n⟩,?_⟩
  intro n N k omega x R z sigma hk hx hs hR
  let f := PRZZMellinSeparation.scaledCutoff F N
  let g := PRZZPowerJets.power z
  let p := PRZZReciprocalJets.phase omega
  let w := PRZZPoissonWDerivative.quadratic sigma k
  have hf : ContDiffAt ℝ ∞ f x := (hF.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hg : ContDiffAt ℝ ∞ g x := by
    change ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (-z*(Real.log y:ℂ))) x
    have hl := (Real.contDiffAt_log.mpr hx.ne' : ContDiffAt ℝ ∞ Real.log x)
    have hlc : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y:ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
    fun_prop
  have hp : ContDiffAt ℝ ∞ p x := by
    change ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (Complex.I*(omega/y:ℝ))) x
    have hx0 := hx.ne'
    have hoc : ContDiffAt ℝ ∞ (fun y : ℝ => (omega/y:ℝ) : ℝ → ℂ) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.div contDiffAt_id hx0)
    fun_prop
  have hw : ContDiffAt ℝ ∞ w x := by
    apply (PRZZFullWeightSmooth.source_smooth sigma hs).contDiffAt
      (Ioi_mem_nhds (by positivity : 0 < k*x^2)) |>.comp x
    fun_prop
  have low (i : ℕ) : (i : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤)
  apply product_bound _ _ n x ((hf.mul hg).mul hp |>.of_le (low n)) (hw.of_le (low n))
  · intro i hi
    apply product_bound _ _ i x ((hf.mul hg).of_le (low i)) (hp.of_le (low i))
    · intro j hj
      apply product_bound _ _ j x (hf.of_le (low j)) (hg.of_le (low j))
      · intro u hu; exact hcut u N x
      · intro u hu; exact (PRZZPowerJets.scaled_norm z u x hx).le
    · intro j hj; exact PRZZReciprocalJets.scaled_bound j omega x R hx hR
  · intro i hi; exact hquad i sigma hs k x hk hx

/-- Ordinary derivative form, retaining x^-n for the subsequent spatial
L1/IBP estimate. This is not a bound on an unidentified derivative norm. -/
theorem ordinary_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (N k omega x R : ℝ) (z sigma : ℂ),
      0 < k → 0 < x → sigma ≠ 0 → |omega/x| ≤ R →
      ‖iteratedDeriv n (PRZZFullWeightSmooth.weight F N k omega z sigma) x‖ ≤
        envelope C D E a k x R z sigma n/x^n := by
  obtain ⟨C,D,E,hpos,h⟩ := uniform F hF hsF a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n N k omega x R z sigma hk hx hs hR
  have hh := h n N k omega x R z sigma hk hx hs hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx] at hh
  exact (le_div_iff₀ (pow_pos hx n)).mpr (by simpa [mul_comm] using hh)

#print axioms product_bound
#print axioms uniform
#print axioms ordinary_uniform
end XiPrime8845.PRZZFullWeightJets
