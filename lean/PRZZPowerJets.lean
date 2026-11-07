import PRZZCutoffJets

/-! Positive-real complex powers: exact ordinary jets and their scaled norms.
The shift dependence is explicit; no height-dependent compact supremum. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.PRZZPowerJets

def power (z : ℂ) (x : ℝ) : ℂ := Complex.exp (-z*(Real.log x:ℂ))
def coeff (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => coeff z n * (-z-(n:ℂ))
def jet (z : ℂ) (n : ℕ) (x : ℝ) : ℂ := coeff z n*power z x/(x:ℂ)^n

theorem jet_deriv (z : ℂ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (jet z n) (jet z (n+1) x) x := by
  have he := ((Real.hasDerivAt_log hx.ne').ofReal_comp.const_mul (-z)).cexp
  have hh := (he.const_mul (coeff z n)).div (Complex.ofRealCLM.hasDerivAt.pow n)
    (pow_ne_zero n (by change (x:ℂ) ≠ 0; exact_mod_cast hx.ne'))
  convert hh using 1 <;> first | rfl | skip
  simp only [jet,coeff,power,Complex.real_smul,Function.comp_apply,
    Complex.ofRealCLM_apply,Pi.pow_apply,Pi.mul_apply,Complex.ofReal_one]
  push_cast
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  cases n <;> simp only [Nat.add_sub_cancel,pow_zero,pow_succ,Nat.cast_zero,
    zero_mul,mul_zero,sub_zero]
  all_goals field_simp [hxC] <;> ring

theorem iterated (z : ℂ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (power z) x = jet z n x := by
  induction n generalizing x with
  | zero => simp [jet,coeff]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (power z) =ᶠ[𝓝 x] jet z n := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (jet_deriv z n x hx).deriv

theorem scaled_norm (z : ℂ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖(x:ℂ)^n*iteratedDeriv n (power z) x‖ =
      ‖coeff z n‖*Real.exp (-z.re*Real.log x) := by
  rw [iterated z n x hx,jet]
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have he : (x:ℂ)^n*(coeff z n*power z x/(x:ℂ)^n) = coeff z n*power z x := by
    field_simp
  rw [he,norm_mul]
  simp [power,Complex.norm_exp]

#print axioms jet_deriv
#print axioms iterated
#print axioms scaled_norm
end XiPrime8845.PRZZPowerJets
