import PRZZFullWeightSmooth

/-! All-order cutoff constants are chosen before the scale (and hence
before height). Both the ordinary N^-n cost and the scaled x^n envelope
are supplied. These are ingredients for, not a substitute for, the full
oscillatory weight's quantitative Leibniz estimate. -/
noncomputable section
open scoped ContDiff
open scoped BigOperators
namespace XiPrime8845.PRZZCutoffJets
open PRZZMellinSeparation

theorem jet_support (F : ℝ → ℂ) (hs : HasCompactSupport F) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n F) := by
  induction n with
  | zero => simpa using hs
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem scaled_jet (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (n : ℕ) (N x : ℝ) :
    iteratedDeriv n (scaledCutoff F N) x =
      (N⁻¹^n:ℝ) • iteratedDeriv n F (N⁻¹*x) := by
  exact congrFun (iteratedDeriv_comp_const_smul (n := n)
    (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) N⁻¹) x

/-- A single constant works for every positive scale, not a compact set
of scales. No supremum depending on N is used. -/
theorem ordinary_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N x : ℝ, 0 < N →
      ‖iteratedDeriv n (scaledCutoff F N) x‖ ≤ C/N^n := by
  obtain ⟨C,hC⟩ := (jet_support F hs n).exists_bound_of_continuous
    (hF.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro N x hN
  rw [scaled_jet F hF n N x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ N⁻¹^n)]
  have h := mul_le_mul_of_nonneg_left ((hC (N⁻¹*x)).trans (le_max_left C 0))
    (show 0 ≤ N⁻¹^n by positivity)
  exact h.trans_eq (by rw [inv_pow]; ring)

/-- The dimensionless envelope for every ordinary derivative order. -/
theorem scaled_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N x : ℝ,
      ‖(x:ℂ)^n * iteratedDeriv n (scaledCutoff F N) x‖ ≤ C := by
  have hc : Continuous (fun x : ℝ => (x:ℂ)^n*iteratedDeriv n F x) :=
    (Complex.continuous_ofReal.pow n).mul
      (hF.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  have hs' : HasCompactSupport (fun x : ℝ => (x:ℂ)^n*iteratedDeriv n F x) :=
    (jet_support F hs n).mul_left
  obtain ⟨C,hC⟩ := hs'.exists_bound_of_continuous hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro N x
  rw [scaled_jet F hF n N x]
  have he : (x:ℂ)^n * ((N⁻¹^n:ℝ) • iteratedDeriv n F (N⁻¹*x)) =
      (N⁻¹*x:ℝ)^n * iteratedDeriv n F (N⁻¹*x) := by
    simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow]
    ring
  rw [he]
  exact (hC _).trans (le_max_left _ _)

/-- Exact scaled Leibniz rule: it preserves the dimensionless envelopes
when factors are assembled, instead of taking a new height-dependent sup. -/
theorem scaled_leibniz (f g : ℝ → ℂ) (n : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    (x:ℂ)^n*iteratedDeriv n (fun y => f y*g y) x =
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*
        ((x:ℂ)^i*iteratedDeriv i f x)*
        ((x:ℂ)^(n-i)*iteratedDeriv (n-i) g x) := by
  rw [iteratedDeriv_fun_mul hf hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have he : (x:ℂ)^n = (x:ℂ)^i*(x:ℂ)^(n-i) := by rw [← pow_add, Nat.add_sub_of_le hi']
  rw [he]
  ring

#print axioms scaled_leibniz
#print axioms jet_support
#print axioms scaled_jet
#print axioms ordinary_uniform
#print axioms scaled_uniform
end XiPrime8845.PRZZCutoffJets
