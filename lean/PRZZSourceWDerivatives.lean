import PRZZLogDerivatives

/-! Ordinary derivatives of the actual complex sourceW, on positive arguments.
The tail and correction are combined before estimating the norm. Constants
in the decay bound precede sigma and x; the singular sigma dependence is
retained explicitly. No Gamma-ratio AFE assertion is made here. -/
noncomputable section
open Polynomial Filter Topology
namespace XiPrime8845.PRZZSourceWDerivatives
open PRZZGaussianDerivatives PRZZLogDerivatives PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def jet (sigma : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (scaled (n+1) (tailPolys n) x:ℂ)/(2*(Real.sqrt Real.pi:ℂ)) -
  (scaled (n+1) (polys X (n+1)) x:ℂ)/((Real.sqrt Real.pi:ℂ)*sigma^2)

theorem source_hasDerivAt (sigma : ℂ) (hs : sigma ≠ 0) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (sourceW sigma) (jet sigma 0 x) x := by
  have ht := (PRZZSourceDecay.tail_hasDerivAt (Real.log x)).comp x
    (Real.hasDerivAt_log hx.ne')
  have hc := (weighted_hasDerivAt X (Real.log x)).comp x
    (Real.hasDerivAt_log hx.ne')
  have hh := (ht.ofReal_comp.div_const (2*(Real.sqrt Real.pi:ℂ))).sub
    (hc.ofReal_comp.div_const ((Real.sqrt Real.pi:ℂ)*sigma^2))
  have he : sourceW sigma =ᶠ[𝓝 x] (fun y =>
      (PRZZSourceW.tail (Real.log y):ℂ)/(2*(Real.sqrt Real.pi:ℂ)) -
      (weighted X (Real.log y):ℂ)/((Real.sqrt Real.pi:ℂ)*sigma^2)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    simpa [weighted] using PRZZSourceW.sourceW_eq sigma hs y hy
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hh using 1 <;> first | rfl | skip
  simp [jet,scaled,tailPolys,polys,next,weighted,div_eq_mul_inv]

theorem jet_hasDerivAt (sigma : ℂ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (jet sigma n) (jet sigma (n+1) x) x := by
  exact ((scaled_hasDerivAt (n+1) (tailPolys n) x hx).ofReal_comp.div_const _).sub
    ((scaled_hasDerivAt (n+1) (polys X (n+1)) x hx).ofReal_comp.div_const _)

theorem source_iterated (sigma : ℂ) (hs : sigma ≠ 0) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv (n+1) (sourceW sigma) x = jet sigma n x := by
  induction n generalizing x with
  | zero => simpa using (source_hasDerivAt sigma hs x hx).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (sourceW sigma) =ᶠ[𝓝 x] jet sigma n := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (jet_hasDerivAt sigma n x hx).deriv

/-- Every positive ordinary derivative has arbitrary power decay. The two
constants depend only on the order and rate, never on sigma or x. -/
theorem source_derivative_decay (n : ℕ) (a : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 → ∀ x : ℝ, 0 < x →
      ‖iteratedDeriv (n+1) (sourceW sigma) x‖ ≤
        (C+D/‖sigma‖^2)*x^(-a)/x^(n+1) := by
  obtain ⟨C,hC,hc⟩ := tail_ordinary_decay n a
  obtain ⟨D,hD,hd⟩ := ordinary_decay X (n+1) a
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨C/(2*Real.sqrt Real.pi),D/Real.sqrt Real.pi,by positivity,by positivity,?_⟩
  intro sigma hs x hx
  have ht := hc x hx
  have hu := hd x hx
  rw [tail_ordinary n x hx] at ht
  rw [ordinary_iterated X (n+1) x hx] at hu
  rw [source_iterated sigma hs n x hx,jet]
  apply (norm_sub_le _ _).trans
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr]
  norm_num only [Complex.norm_ofNat]
  exact (add_le_add
    (div_le_div_of_nonneg_right ht (by positivity))
    (div_le_div_of_nonneg_right hu (by positivity))).trans_eq (by ring)

/-- Includes order zero. Positive decay rates are required only for the
undifferentiated tail; no uniformity across sigma=0 is claimed. -/
theorem source_all_decay (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 → ∀ x : ℝ, 0 < x →
      ‖iteratedDeriv n (sourceW sigma) x‖ ≤ (C+D/‖sigma‖^2)*x^(-a)/x^n := by
  cases n with
  | zero =>
    refine ⟨Real.exp (a^2)/(2*Real.sqrt Real.pi*a),
      (2+2*|a|)*Real.exp (a^2)/Real.sqrt Real.pi,by positivity,by positivity,?_⟩
    intro sigma hs x hx
    simpa [div_div] using PRZZSourceDecay.sourceW_decay sigma hs a x ha hx
  | succ n => exact source_derivative_decay n a

/-- The actual logarithmically scaled shifts. Constants are selected before
A,B,L,x; all height dependence is displayed in the quadratic L cost. -/
theorem source_scaled_decay (n : ℕ) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (A B : ℂ) (L x : ℝ),
      L ≠ 0 → r ≤ ‖A+B‖ → 0 < x →
      ‖iteratedDeriv n (sourceW ((A+B)/(L:ℂ))) x‖ ≤
        (C+D*L^2/r^2)*x^(-a)/x^n := by
  obtain ⟨C,D,hC,hD,h⟩ := source_all_decay n a ha
  refine ⟨C,D,hC,hD,?_⟩
  intro A B L x hL hsep hx
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL
  have hh := h ((A+B)/(L:ℂ)) (div_ne_zero hab hLc) x hx
  have he : D/‖(A+B)/(L:ℂ)‖^2 = D*L^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

#print axioms source_scaled_decay
#print axioms source_derivative_decay
#print axioms source_all_decay
#print axioms source_hasDerivAt
#print axioms jet_hasDerivAt
#print axioms source_iterated
end XiPrime8845.PRZZSourceWDerivatives
