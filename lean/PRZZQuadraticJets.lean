import PRZZFullWeightSmooth

/-! All ordinary derivatives of sourceW(sigma,k*x^2), uniformly in k>0.
The polynomial recurrence retains the x^-n factor; constants depend only
on derivative order and decay rate, with the sigma singularity explicit. -/
noncomputable section
open Polynomial Filter Topology
namespace XiPrime8845.PRZZQuadraticJets
open PRZZGaussianDerivatives PRZZDyadicEnvelope

def next (n : ℕ) (P : ℝ[X]) : ℝ[X] := C 2*step P-C (n:ℝ)*P
def polys (P : ℝ[X]) : ℕ → ℝ[X]
  | 0 => P
  | n+1 => next (n+1) (polys P n)
def term (n : ℕ) (P : ℝ[X]) (k x : ℝ) : ℝ :=
  weighted P (Real.log (k*x^2))/x^n

theorem term_deriv (n : ℕ) (P : ℝ[X]) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    HasDerivAt (term n P k) (term (n+1) (next n P) k x) x := by
  have hl := (Real.hasDerivAt_log (by positivity : k*x^2 ≠ 0)).comp x
    (((hasDerivAt_id x).pow 2).const_mul k)
  have hh := ((weighted_hasDerivAt P _).comp x hl).div
    ((hasDerivAt_id x).pow n) (pow_ne_zero n hx.ne')
  convert hh using 1 <;> first | rfl | skip
  simp only [term,next,weighted,eval_sub,eval_mul,eval_C,id_eq,
    Pi.pow_apply,Function.comp_apply]
  cases n <;> simp only [Nat.add_sub_cancel,pow_zero,pow_succ,Nat.cast_zero,
    zero_mul,mul_zero,sub_zero]
  all_goals field_simp <;> ring

def jet (sigma : ℂ) (n : ℕ) (k x : ℝ) : ℂ :=
  (term (n+1) (polys (C (-2)) n) k x:ℂ)/(2*(Real.sqrt Real.pi:ℂ)) -
  (term (n+1) (polys (C 2*step X) n) k x:ℂ)/((Real.sqrt Real.pi:ℂ)*sigma^2)

theorem first_deriv (sigma : ℂ) (hs : sigma ≠ 0) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    HasDerivAt (PRZZPoissonWDerivative.quadratic sigma k) (jet sigma 0 k x) x := by
  have hh := PRZZPoissonWDerivative.quadratic_hasDerivAt sigma hs k x hk hx
  have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  convert hh using 1 <;> first | rfl | skip
  simp [jet,polys,term,PRZZSourceWDerivatives.jet,PRZZLogDerivatives.scaled,
    PRZZLogDerivatives.tailPolys,PRZZLogDerivatives.polys,PRZZLogDerivatives.next,
    weighted,step]
  push_cast
  field_simp [hkC,hxC]
  <;> ring

theorem jet_deriv (sigma : ℂ) (n : ℕ) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    HasDerivAt (jet sigma n k) (jet sigma (n+1) k x) x :=
  ((term_deriv _ _ k x hk hx).ofReal_comp.div_const _).sub
    ((term_deriv _ _ k x hk hx).ofReal_comp.div_const _)

theorem iterated (sigma : ℂ) (hs : sigma ≠ 0) (n : ℕ) (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    iteratedDeriv (n+1) (PRZZPoissonWDerivative.quadratic sigma k) x = jet sigma n k x := by
  induction n generalizing x with
  | zero => simpa using (first_deriv sigma hs k x hk hx).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (PRZZPoissonWDerivative.quadratic sigma k) =ᶠ[𝓝 x]
        jet sigma n k := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (jet_deriv sigma n k x hk hx).deriv

theorem term_bound (n : ℕ) (P : ℝ[X]) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x : ℝ, 0 < k → 0 < x →
      |term n P k x| ≤ C*(k*x^2)^(-a)/x^n := by
  obtain ⟨C,hC,h⟩ := PRZZLogDerivatives.weighted_decay P a
  refine ⟨C,hC,?_⟩
  intro k x hk hx
  rw [term,abs_div,abs_of_pos (pow_pos hx n)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [Real.rpow_def_of_pos (by positivity : 0 < k*x^2),mul_comm] using h (Real.log (k*x^2))

theorem decay (n : ℕ) (a : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 →
      ∀ k x : ℝ, 0 < k → 0 < x →
      ‖iteratedDeriv (n+1) (PRZZPoissonWDerivative.quadratic sigma k) x‖ ≤
        (C+D/‖sigma‖^2)*(k*x^2)^(-a)/x^(n+1) := by
  obtain ⟨C,hC,hc⟩ := term_bound (n+1) (polys (C (-2)) n) a
  obtain ⟨D,hD,hd⟩ := term_bound (n+1) (polys (Polynomial.C 2*step X) n) a
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨C/(2*Real.sqrt Real.pi),D/Real.sqrt Real.pi,by positivity,by positivity,?_⟩
  intro sigma hs k x hk hx
  rw [iterated sigma hs n k x hk hx,jet]
  apply (norm_sub_le _ _).trans
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  norm_num only [Complex.norm_ofNat]
  exact (add_le_add (div_le_div_of_nonneg_right (hc k x hk hx) (by positivity))
    (div_le_div_of_nonneg_right (hd k x hk hx) (by positivity))).trans_eq (by ring)

/-- Includes the undifferentiated tail. -/
theorem all_decay (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 →
      ∀ k x : ℝ, 0 < k → 0 < x →
      ‖iteratedDeriv n (PRZZPoissonWDerivative.quadratic sigma k) x‖ ≤
        (C+D/‖sigma‖^2)*(k*x^2)^(-a)/x^n := by
  cases n with
  | zero =>
    obtain ⟨C,D,hC,hD,h⟩ := PRZZSourceWDerivatives.source_all_decay 0 a ha
    refine ⟨C,D,hC,hD,?_⟩
    intro sigma hs k x hk hx
    simpa [PRZZPoissonWDerivative.quadratic] using h sigma hs (k*x^2) (by positivity)
  | succ n => exact decay n a

/-- All scale dependence is explicit; the constants precede the shift
family and height parameter L (in applications L=log T). -/
theorem scaled_shifts (n : ℕ) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (A B : ℂ) (L k x : ℝ),
      L ≠ 0 → r ≤ ‖A+B‖ → 0 < k → 0 < x →
      ‖iteratedDeriv n (PRZZPoissonWDerivative.quadratic ((A+B)/(L:ℂ)) k) x‖ ≤
        (C+D*L^2/r^2)*(k*x^2)^(-a)/x^n := by
  obtain ⟨C,D,hC,hD,h⟩ := all_decay n a ha
  refine ⟨C,D,hC,hD,?_⟩
  intro A B L k x hL hsep hk hx
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL
  have hh := h ((A+B)/(L:ℂ)) (div_ne_zero hab hLc) k x hk hx
  have he : D/‖(A+B)/(L:ℂ)‖^2 = D*L^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

/-- Dimensionless form for direct insertion into scaled Leibniz. -/
theorem scaled_bound (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 →
      ∀ k x : ℝ, 0 < k → 0 < x →
      ‖(x:ℂ)^n*iteratedDeriv n (PRZZPoissonWDerivative.quadratic sigma k) x‖ ≤
        (C+D/‖sigma‖^2)*(k*x^2)^(-a) := by
  obtain ⟨C,D,hC,hD,h⟩ := all_decay n a ha
  refine ⟨C,D,hC,hD,?_⟩
  intro sigma hs k x hk hx
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left (h sigma hs k x hk hx) (pow_nonneg hx.le n)
  exact hh.trans_eq (by field_simp)

#print axioms scaled_bound
#print axioms all_decay
#print axioms scaled_shifts
#print axioms term_deriv
#print axioms first_deriv
#print axioms jet_deriv
#print axioms iterated
#print axioms term_bound
#print axioms decay
end XiPrime8845.PRZZQuadraticJets
