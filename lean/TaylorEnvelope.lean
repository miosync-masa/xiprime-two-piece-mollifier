import IntegralJet

/-! Explicit errors for differentiate-then-truncate K2 evaluation.
No arithmetic main-term or zero-counting axiom is imported. -/
noncomputable section
open scoped BigOperators Topology Interval
open MeasureTheory Set

namespace XiPrime8845.TaylorEnvelope
open FiniteJet IntegralJet
set_option maxHeartbeats 1000000

def expPartial (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), z ^ j / (j.factorial : ℂ)

def tailFactor (N : ℕ) (r : ℝ) : ℝ := r ^ (N + 1) / ((N + 1).factorial : ℝ)

theorem expPartial_error (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - expPartial N z‖ ≤ 3 * tailFactor N ‖z‖ := by
  have h := Complex.exp_bound' (n := N + 1) (x := z) (by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ↑(N + 1 + 1))).2
    have : (2 : ℝ) ≤ ↑(N + 1 + 1) := by exact_mod_cast (by omega : 2 ≤ N + 1 + 1)
    linarith)
  change ‖Complex.exp z - expPartial N z‖ ≤ _ at h
  unfold tailFactor
  nlinarith [div_nonneg (pow_nonneg (norm_nonneg z) (N + 1))
    (show (0 : ℝ) ≤ ↑(N + 1).factorial by positivity)]

theorem exp_norm_le_three (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖Complex.exp z‖ ≤ 3 := by
  have h := Complex.exp_bound' (n := 1) (x := z) (by norm_num; linarith)
  norm_num at h
  have ht := norm_add_le (Complex.exp z - 1) (1 : ℂ)
  simp only [sub_add_cancel, norm_one] at ht
  linarith

def coeffNorm (F : Polynomial ℂ) : ℝ := ∑ d ∈ F.support, ‖F.coeff d‖

theorem coeffNorm_nonneg (F : Polynomial ℂ) : 0 ≤ coeffNorm F :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem profile_bound (F : Polynomial ℂ) (u : ℝ) (hu : u ∈ Icc 0 1) :
    ‖F.eval (u : ℂ)‖ ≤ coeffNorm F := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum coeffNorm
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hu.1 hu.2)

/-- The exponential is truncated after taking the normalized shift derivative. -/
def inverseApprox (N a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) : ℂ :=
  (∫ y in 0..w, (-(y : ℂ)) ^ a * expPartial N (-A * y) *
    F.eval (((w - y) / θ : ℝ) : ℂ)) / (a.factorial : ℂ)

def inverseBound (a : ℕ) (θ C : ℝ) : ℝ :=
  3 * C * θ ^ (a + 1) / ((a.factorial : ℝ) * (a + 1))

theorem inverseBound_nonneg (a : ℕ) (θ C : ℝ) (hθ : 0 ≤ θ) (hC : 0 ≤ C) :
    0 ≤ inverseBound a θ C := by unfold inverseBound; positivity

theorem profile_argument (θ w y : ℝ) (hθ : 0 < θ) (hw : w ≤ θ)
    (hy : y ∈ Icc 0 w) : (w - y) / θ ∈ Icc 0 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.2) hθ.le
  · apply (div_le_one hθ).2
    linarith [hy.1]

theorem shift_norm_le (A : ℂ) (θ y : ℝ) (hy : y ∈ Icc 0 θ) :
    ‖-A * (y : ℂ)‖ ≤ ‖A‖ * θ := by
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1]
  exact mul_le_mul_of_nonneg_left hy.2 (norm_nonneg _)

/-- An integrable power majorant; retains the 1/(a+1) gained by integration. -/
theorem norm_integral_power_bound (f : ℝ → ℂ) (a : ℕ) (w C : ℝ) (hw : 0 ≤ w)
    (hf : ∀ y ∈ Icc 0 w, ‖f y‖ ≤ C * y ^ a) :
    ‖∫ y in 0..w, f y‖ ≤ C * w ^ (a + 1) / (a + 1) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le hw
    (Filter.Eventually.of_forall (fun y hy => hf y ⟨le_of_lt hy.1, hy.2⟩))
    (show IntervalIntegrable (fun y : ℝ => C * y ^ a) volume 0 w from
      (by fun_prop : Continuous (fun y : ℝ => C * y ^ a)).intervalIntegrable 0 w)
  simpa [intervalIntegral.integral_const_mul, integral_pow, mul_div_assoc] using h

theorem inverse_operator_bound (a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ)
    (hθ : 0 < θ) (hw : w ∈ Icc 0 θ) (hA : ‖A‖ * θ ≤ 1) :
    ‖operatorJet (-1) a A θ w F‖ ≤ inverseBound a θ (coeffNorm F) := by
  have hb : ‖inverseMoment a A θ w F‖ ≤ 3 * coeffNorm F * w ^ (a + 1) / (a + 1) := by
    apply norm_integral_power_bound _ a w (3 * coeffNorm F) hw.1
    intro y hy
    have hp := profile_bound F _ (profile_argument θ w y hθ hw.2 hy)
    have he := exp_norm_le_three (-A * y) ((shift_norm_le A θ y ⟨hy.1, hy.2.trans hw.2⟩).trans hA)
    have hy0 := hy.1
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hy.1]
    calc
      _ ≤ y ^ a * 3 * coeffNorm F := by gcongr
      _ = _ := by ring
  simp only [operatorJet, ↓reduceIte, norm_div, norm_natCast]
  calc
    _ ≤ (3 * coeffNorm F * w ^ (a + 1) / (a + 1)) / a.factorial :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ ≤ (3 * coeffNorm F * θ ^ (a + 1) / (a + 1)) / a.factorial := by
      have hC := coeffNorm_nonneg F
      gcongr <;> first | exact hw.1 | exact hw.2
    _ = _ := by unfold inverseBound; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem inverse_operator_error (N a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ)
    (hθ : 0 < θ) (hw : w ∈ Icc 0 θ) (hA : ‖A‖ * θ ≤ 1) :
    ‖operatorJet (-1) a A θ w F - inverseApprox N a A θ w F‖ ≤
      inverseBound a θ (coeffNorm F) * tailFactor N (‖A‖ * θ) := by
  let f : ℝ → ℂ := fun y => (-(y : ℂ)) ^ a *
    (Complex.exp (-A * y) - expPartial N (-A * y)) * F.eval (((w - y) / θ : ℝ) : ℂ)
  have he : operatorJet (-1) a A θ w F - inverseApprox N a A θ w F =
      (∫ y in 0..w, f y) / (a.factorial : ℂ) := by
    simp only [operatorJet, ↓reduceIte, inverseMoment, inverseApprox, ← sub_div]
    rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun y : ℝ => (-(y : ℂ)) ^ a * Complex.exp (-A * y) *
        F.eval (((w - y) / θ : ℝ) : ℂ))).intervalIntegrable 0 w)
      ((by unfold expPartial; fun_prop : Continuous (fun y : ℝ => (-(y : ℂ)) ^ a * expPartial N (-A * y) *
        F.eval (((w - y) / θ : ℝ) : ℂ))).intervalIntegrable 0 w)]
    congr 2
    funext y
    dsimp [f]
    ring
  have ht : 0 ≤ tailFactor N (‖A‖ * θ) := by unfold tailFactor; positivity
  have hb : ‖∫ y in 0..w, f y‖ ≤
      (3 * coeffNorm F * tailFactor N (‖A‖ * θ)) * w ^ (a + 1) / (a + 1) := by
    apply norm_integral_power_bound _ a w _ hw.1
    intro y hy
    have hs := shift_norm_le A θ y ⟨hy.1, hy.2.trans hw.2⟩
    have hp := profile_bound F _ (profile_argument θ w y hθ hw.2 hy)
    have hy0 := hy.1
    have hx := expPartial_error N (-A * y) (hs.trans hA)
    have ht' : tailFactor N ‖-A * (y : ℂ)‖ ≤ tailFactor N (‖A‖ * θ) := by
      unfold tailFactor
      gcongr
    dsimp [f]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hy.1]
    calc
      _ ≤ y ^ a * (3 * tailFactor N (‖A‖ * θ)) * coeffNorm F := by
        gcongr
        exact hx.trans (mul_le_mul_of_nonneg_left ht' (by norm_num))
      _ = _ := by ring
  rw [he, norm_div, norm_natCast]
  calc
    _ ≤ ((3 * coeffNorm F * tailFactor N (‖A‖ * θ)) * w ^ (a + 1) / (a + 1)) / a.factorial :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ ≤ ((3 * coeffNorm F * tailFactor N (‖A‖ * θ)) * θ ^ (a + 1) / (a + 1)) / a.factorial := by
      have hC := coeffNorm_nonneg F
      gcongr <;> first | exact hw.1 | exact hw.2
    _ = _ := by unfold inverseBound; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Error of a product, using bounds on the exact factors, as in the verifier. -/
theorem product_error (x y u v : ℂ) (Bx By Ex Ey : ℝ)
    (hx : ‖x‖ ≤ Bx) (hy : ‖y‖ ≤ By) (he : ‖x - u‖ ≤ Ex) (hf : ‖y - v‖ ≤ Ey) :
    ‖x * y - u * v‖ ≤ Ex * By + Ey * Bx + Ex * Ey := by
  have hEx : 0 ≤ Ex := (norm_nonneg _).trans he
  have hEy : 0 ≤ Ey := (norm_nonneg _).trans hf
  have hBx : 0 ≤ Bx := (norm_nonneg _).trans hx
  have hBy : 0 ≤ By := (norm_nonneg _).trans hy
  have hid : x * y - u * v = (x - u) * y + x * (y - v) - (x - u) * (y - v) := by ring
  rw [hid]
  calc
    _ ≤ (‖x - u‖ * ‖y‖ + ‖x‖ * ‖y - v‖) + ‖x - u‖ * ‖y - v‖ := by
      have h1 := norm_sub_le ((x-u)*y + x*(y-v)) ((x-u)*(y-v))
      have h2 := norm_add_le ((x-u)*y) (x*(y-v))
      simp only [norm_mul] at h1 h2
      linarith
    _ ≤ Ex * By + Ey * Bx + Ex * Ey := by
      have h1 := mul_le_mul he hy (norm_nonneg _) hEx
      have h2 := mul_le_mul hx hf (norm_nonneg _) hBx
      have h3 := mul_le_mul he hf (norm_nonneg _) hEx
      nlinarith

def operatorApprox (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) : ℂ :=
  if e = -1 then inverseApprox N a A θ w F else operatorJet e a A θ w F

def operatorError (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) : ℝ :=
  if e = -1 then inverseBound a θ (coeffNorm F) * tailFactor N (‖A‖ * θ) else 0

/-- A uniform exact-factor bound; the noninverse bound is deliberately allowed
to be looser than the Python verifier's sparse per-order bound. -/
def operatorBound (e : ℤ) (a : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) : ℝ :=
  if e = -1 then inverseBound a θ (coeffNorm F)
  else coeffNorm F.derivative / θ + (‖A‖ + 1) * coeffNorm F

theorem operator_error (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ)
    (hθ : 0 < θ) (hw : w ∈ Icc 0 θ) (hA : ‖A‖ * θ ≤ 1) :
    ‖operatorJet e a A θ w F - operatorApprox N e a A θ w F‖ ≤ operatorError N e a A θ F := by
  by_cases he : e = -1
  · subst e
    exact inverse_operator_error N a A θ w F hθ hw hA
  · simp [operatorApprox, operatorError, he]

theorem operator_bound (e : ℤ) (a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ)
    (hθ : 0 < θ) (hw : w ∈ Icc 0 θ) (hA : ‖A‖ * θ ≤ 1) :
    ‖operatorJet e a A θ w F‖ ≤ operatorBound e a A θ F := by
  by_cases he : e = -1
  · subst e
    exact inverse_operator_bound a A θ w F hθ hw hA
  have hu : w / θ ∈ Icc 0 1 := ⟨div_nonneg hw.1 hθ.le, (div_le_one hθ).2 hw.2⟩
  have hp := profile_bound F _ hu
  have hd := profile_bound F.derivative _ hu
  have hC := coeffNorm_nonneg F
  have hC' := coeffNorm_nonneg F.derivative
  have hB : 0 ≤ coeffNorm F.derivative / θ + (‖A‖ + 1) * coeffNorm F := by positivity
  have hp' : ‖F.eval ((w / θ : ℝ) : ℂ)‖ ≤
      coeffNorm F.derivative / θ + (‖A‖ + 1) * coeffNorm F := by
    nlinarith [div_nonneg hC' hθ.le, mul_nonneg (norm_nonneg A) hC]
  simp only [operatorBound, he, ↓reduceIte]
  simp only [operatorJet, he, ↓reduceIte]
  split_ifs with ha h1
  · unfold BetaKernel.D
    split_ifs with he1 he0
    · calc
        _ ≤ ‖F.derivative.eval ((w / θ : ℝ) : ℂ) / (θ : ℂ)‖ +
          ‖A * F.eval ((w / θ : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ coeffNorm F.derivative / θ + ‖A‖ * coeffNorm F := by
          simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ, norm_mul]
          gcongr
        _ ≤ _ := by nlinarith
    · exact hp'
    · simpa using hB
  · exact hp'
  · simpa using hB

theorem operatorApprox_continuous (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ : ℝ)
    (F : Polynomial ℂ) : Continuous (fun w => operatorApprox N e a A θ w F) := by
  by_cases he : e = -1
  · simp only [operatorApprox, he, ↓reduceIte, inverseApprox]
    apply Continuous.div_const
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · unfold Function.uncurry expPartial
      fun_prop
    · exact continuous_id
  · simp only [operatorApprox, he, ↓reduceIte]
    convert! (operatorJet_continuous e a θ F).comp
      ((continuous_const : Continuous (fun _ : ℝ => A)).prodMk continuous_id) using 1

def productError (N : ℕ) (e f : ℤ) (i j : ℕ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℝ :=
  operatorError N e i A θ F * operatorBound f j B θ G +
  operatorError N f j B θ G * operatorBound e i A θ F +
  operatorError N e i A θ F * operatorError N f j B θ G

def monomialApprox (N : ℕ) (e f : ℤ) (n i j : ℕ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℂ :=
  ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
    operatorApprox N e i A θ (θ - v) F * operatorApprox N f j B θ (θ - v) G

theorem monomial_error (N : ℕ) (e f : ℤ) (n i j : ℕ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) (hθ : 0 < θ) (hn : 0 < n)
    (hA : ‖A‖ * θ ≤ 1) (hB : ‖B‖ * θ ≤ 1) :
    ‖monomialJet e f n i j A B θ F G - monomialApprox N e f n i j A B θ F G‖ ≤
      productError N e f i j A B θ F G * θ ^ n / (n.factorial : ℝ) := by
  have hc (e : ℤ) (a : ℕ) (A : ℂ) (F : Polynomial ℂ) :
      Continuous (fun v : ℝ => operatorJet e a A θ (θ - v) F) := by
    convert! (operatorJet_continuous e a θ F).comp
      ((continuous_const : Continuous (fun _ : ℝ => A)).prodMk
        (show Continuous (fun v : ℝ => θ - v) by fun_prop)) using 1
  have ht (e : ℤ) (a : ℕ) (A : ℂ) (F : Polynomial ℂ) :
      Continuous (fun v : ℝ => operatorApprox N e a A θ (θ - v) F) :=
    (operatorApprox_continuous N e a A θ F).comp (continuous_const.sub continuous_id)
  unfold monomialJet monomialApprox
  rw [← intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun v : ℝ => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
      operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G)).intervalIntegrable 0 θ)
    ((by fun_prop : Continuous (fun v : ℝ => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
      operatorApprox N e i A θ (θ - v) F * operatorApprox N f j B θ (θ - v) G)).intervalIntegrable 0 θ)]
  have hb := norm_integral_power_bound
    (fun v : ℝ => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G -
      (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * operatorApprox N e i A θ (θ - v) F * operatorApprox N f j B θ (θ - v) G)
    (n - 1) θ (productError N e f i j A B θ F G / ((n - 1).factorial : ℝ)) hθ.le (by
      intro v hv
      have hw : θ - v ∈ Icc 0 θ := ⟨sub_nonneg.mpr hv.2, sub_le_self _ hv.1⟩
      have hp := product_error _ _ _ _ _ _ _ _
        (operator_bound e i A θ (θ - v) F hθ hw hA)
        (operator_bound f j B θ (θ - v) G hθ hw hB)
        (operator_error N e i A θ (θ - v) F hθ hw hA)
        (operator_error N f j B θ (θ - v) G hθ hw hB)
      rw [show (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G -
        (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * operatorApprox N e i A θ (θ - v) F * operatorApprox N f j B θ (θ - v) G =
        ((v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ)) *
        (operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G -
        operatorApprox N e i A θ (θ - v) F * operatorApprox N f j B θ (θ - v) G) by ring]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hv.1, norm_natCast]
      calc
        _ ≤ (v ^ (n - 1) / ((n - 1).factorial : ℝ)) * productError N e f i j A B θ F G :=
          mul_le_mul_of_nonneg_left hp (div_nonneg (pow_nonneg hv.1 _) (by positivity))
        _ = _ := by ring)
  convert hb using 1
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Absolute-value propagation through the literal finite pole sum. -/
def poleError (l m : ℕ) (E : ℤ → ℤ → ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (min l m + 1), ∑ r ∈ Finset.range (l - k + 1),
    ∑ t ∈ Finset.range (m - k + 1),
      ‖(Nat.choose l k : ℂ) * m.descFactorial k * Nat.choose (l - k) r *
        Nat.choose (m - k) t * (-1 : ℂ) ^ (l + m + r + t)‖ *
      E (1 - (l : ℤ) + k + r) (1 - (m : ℤ) + k + t) (1 + 2*k + r + t)

theorem poleSum_error (l m : ℕ) (X Y : ℤ → ℤ → ℕ → ℂ) (E : ℤ → ℤ → ℕ → ℝ)
    (hE : ∀ e f n, 0 < n → ‖X e f n - Y e f n‖ ≤ E e f n) :
    ‖BetaKernel.poleSum l m X - BetaKernel.poleSum l m Y‖ ≤ poleError l m E := by
  unfold BetaKernel.poleSum poleError
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hE _ _ _ (by omega)) (norm_nonneg _)

def HApprox (N l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  BetaKernel.poleSum l m (fun e f n => monomialApprox N e f n i j A B θ F G) / (θ : ℂ) ^ (l + m)

def HError (N l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℝ :=
  poleError l m (fun e f n => productError N e f i j A B θ F G * θ ^ n / (n.factorial : ℝ)) /
    θ ^ (l + m)

theorem H_error (N l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ * θ ≤ 1) (hB : ‖B‖ * θ ≤ 1) :
    ‖HJet l m i j A B θ F G - HApprox N l m i j A B θ F G‖ ≤
      HError N l m i j A B θ F G := by
  simp only [HJet, HApprox, ← sub_div, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hθ, HError]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply poleSum_error
  intro e f n hn
  exact monomial_error N e f n i j A B θ F G hθ hn hA hB

def fourApprox (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  HApprox N 0 0 i j A B θ F F + HApprox N 0 2 i j A B θ F G +
    HApprox N 2 0 i j A B θ G F + HApprox N 2 2 i j A B θ G G

def fourError (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℝ :=
  HError N 0 0 i j A B θ F F + HError N 0 2 i j A B θ F G +
    HError N 2 0 i j A B θ G F + HError N 2 2 i j A B θ G G

theorem add_error (x y u v : ℂ) (E F : ℝ) (hx : ‖x - u‖ ≤ E) (hy : ‖y - v‖ ≤ F) :
    ‖(x + y) - (u + v)‖ ≤ E + F := by
  rw [show x + y - (u + v) = (x - u) + (y - v) by ring]
  exact (norm_add_le _ _).trans (add_le_add hx hy)

theorem four_error (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ * θ ≤ 1) (hB : ‖B‖ * θ ≤ 1) :
    ‖fourTermsJet i j A B θ F G - fourApprox N i j A B θ F G‖ ≤
      fourError N i j A B θ F G :=
  add_error _ _ _ _ _ _ (add_error _ _ _ _ _ _ (add_error _ _ _ _ _ _
    (H_error N 0 0 i j A B θ F F hθ hA hB) (H_error N 0 2 i j A B θ F G hθ hA hB))
    (H_error N 2 0 i j A B θ G F hθ hA hB)) (H_error N 2 2 i j A B θ G G hθ hA hB)

theorem weighted_error (D : ℕ) (W X Y : ℕ → ℕ → ℂ) (E : ℕ → ℕ → ℝ)
    (he : ∀ i j, ‖X i j - Y i j‖ ≤ E i j) :
    ‖(∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), W i j * X i j) -
      (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), W i j * Y i j)‖ ≤
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), ‖W i j‖ * E i j := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (he i j) (norm_nonneg _)

def finiteEvaluator (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
    W D (opMinus q) (A + B) i j * fourApprox N i j A B θ F G) +
  Complex.exp (-A - B) *
    ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D (opPlus D q) (-A + -B) i j * fourApprox N i j (-A) (-B) θ F G

def evaluatorError (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℝ :=
  (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
    ‖W D (opMinus q) (A + B) i j‖ * fourError N i j A B θ F G) +
  ‖Complex.exp (-A - B)‖ *
    ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      ‖W D (opPlus D q) (-A + -B) i j‖ * fourError N i j (-A) (-B) θ F G

theorem exact_finite_error (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ * θ ≤ 1) (hB : ‖B‖ * θ ≤ 1) :
    ‖exactEvaluator D q A B θ F G - finiteEvaluator N D q A B θ F G‖ ≤
      evaluatorError N D q A B θ F G := by
  apply add_error
  · exact weighted_error D _ _ _ _ (fun i j => four_error N i j A B θ F G hθ hA hB)
  · rw [← mul_sub, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact weighted_error D _ _ _ _ (fun i j => four_error N i j (-A) (-B) θ F G hθ
      (by simpa only [norm_neg] using hA) (by simpa only [norm_neg] using hB))

/-- The full differential functional is enclosed, not just an assumed jet array. -/
theorem K2_Taylor_enclosure (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (h : A + B ≠ 0) (hθ : 0 < θ) (hA : ‖A‖ * θ ≤ 1) (hB : ‖B‖ * θ ≤ 1) :
    ‖contract₂ D (opMinus q) (fun x y => BetaKernel.shiftedFunctional x y θ F G) A B -
      finiteEvaluator N D q A B θ F G‖ ≤ evaluatorError N D q A B θ F G := by
  rw [K2_exact_evaluator D q A B h θ F G]
  exact exact_finite_error N D q A B θ F G hθ hA hB

#print axioms expPartial_error
#print axioms inverse_operator_bound
#print axioms inverse_operator_error
#print axioms operator_bound
#print axioms operator_error
#print axioms product_error
#print axioms monomial_error
#print axioms poleSum_error
#print axioms H_error
#print axioms four_error
#print axioms weighted_error
#print axioms exact_finite_error
#print axioms K2_Taylor_enclosure

end XiPrime8845.TaylorEnvelope
