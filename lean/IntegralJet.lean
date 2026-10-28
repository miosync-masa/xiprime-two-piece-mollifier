import FiniteJet
import BetaKernel

/-! Differentiation under the finite K2 integrals. No Mellin or PRZZ assertion. -/
noncomputable section
open scoped BigOperators Topology Interval
open Filter Set MeasureTheory

namespace XiPrime8845.IntegralJet
open FiniteJet

@[simp] theorem jet_zero (f : ℂ → ℂ) (A : ℂ) : jet 0 f A = f A := by simp [jet]

/-- Compactness supplies the dominating function; no integral derivative is assumed. -/
theorem hasDerivAt_integral (F F' : ℂ → ℝ → ℂ) (a b : ℝ) (A : ℂ)
    (hc : Continuous (Function.uncurry F)) (hc' : Continuous (Function.uncurry F'))
    (hd : ∀ z t, HasDerivAt (fun x => F x t) (F' z t) z) :
    HasDerivAt (fun z => ∫ t in a..b, F z t) (∫ t in a..b, F' A t) A := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall A 1).prod
    (isCompact_Icc (a := min a b) (b := max a b))).exists_bound_of_continuousOn hc'.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball A 1) (bound := fun _ => C) (Metric.ball_mem_nhds A (by norm_num))
    (Filter.Eventually.of_forall (fun z =>
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
    ((hc'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t ht z hz => hC (z, t)
      ⟨Metric.mem_closedBall.mpr (le_of_lt hz), uIoc_subset_uIcc ht⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun t _ z _ => hd z t))).2

def inverseMoment (n : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) : ℂ :=
  ∫ y in 0..w, (-(y : ℂ)) ^ n * Complex.exp (-A * y) *
    F.eval (((w - y) / θ : ℝ) : ℂ)

theorem inverseMoment_hasDerivAt (n : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) :
    HasDerivAt (fun z => inverseMoment n z θ w F)
      (inverseMoment (n + 1) A θ w F) A := by
  unfold inverseMoment
  apply hasDerivAt_integral
    (fun z y => (-(y : ℂ)) ^ n * Complex.exp (-z * y) * F.eval (((w - y) / θ : ℝ) : ℂ))
    (fun z y => (-(y : ℂ)) ^ (n + 1) * Complex.exp (-z * y) * F.eval (((w - y) / θ : ℝ) : ℂ)) 0 w A
  · unfold Function.uncurry
    fun_prop
  · unfold Function.uncurry
    fun_prop
  · intro z y
    convert! (((hasDerivAt_id z).neg.mul_const (y : ℂ)).cexp.const_mul
      ((-(y : ℂ)) ^ n)).mul_const (F.eval (((w - y) / θ : ℝ) : ℂ)) using 1
    simp only [Pi.neg_apply, id_eq]
    ring

theorem inverseMoment_iteratedDeriv (n : ℕ) (θ w : ℝ) (F : Polynomial ℂ) :
    iteratedDeriv n (fun z => inverseMoment 0 z θ w F) =
      fun z => inverseMoment n z θ w F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (inverseMoment_hasDerivAt n z θ w F).deriv

theorem inverse_operator_jet (n : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) :
    jet n (fun z => BetaKernel.D (-1) z θ w F) A =
      inverseMoment n A θ w F / (n.factorial : ℂ) := by
  have he : (fun z => BetaKernel.D (-1) z θ w F) =
      fun z => inverseMoment 0 z θ w F := by
    funext z
    simp [BetaKernel.D, inverseMoment]
  rw [he, jet, inverseMoment_iteratedDeriv]

theorem inverse_operator_contDiff (n : WithTop ℕ∞) (θ w : ℝ) (F : Polynomial ℂ) :
    ContDiff ℂ n (fun z => BetaKernel.D (-1) z θ w F) := by
  have he : (fun z => BetaKernel.D (-1) z θ w F) =
      fun z => inverseMoment 0 z θ w F := by
    funext z
    simp [BetaKernel.D, inverseMoment]
  rw [he]
  exact (show Differentiable ℂ (fun z => inverseMoment 0 z θ w F) from
    fun z => (inverseMoment_hasDerivAt 0 z θ w F).differentiableAt).contDiff

/-- Joint continuity includes the moving support endpoint w=0. -/
theorem inverseMoment_continuous (n : ℕ) (θ : ℝ) (F : Polynomial ℂ) :
    Continuous (fun p : ℂ × ℝ => inverseMoment n p.1 θ p.2 F) := by
  unfold inverseMoment
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · unfold Function.uncurry
    fun_prop
  · exact continuous_snd

theorem operator_contDiff (e : ℤ) (n : WithTop ℕ∞) (θ w : ℝ) (F : Polynomial ℂ) :
    ContDiff ℂ n (fun z => BetaKernel.D e z θ w F) := by
  by_cases h1 : e = 1
  · simp only [BetaKernel.D, h1, ↓reduceIte]
    fun_prop
  by_cases h0 : e = 0
  · simp only [BetaKernel.D, h0, ↓reduceIte, zero_ne_one]
    fun_prop
  by_cases hm : e = -1
  · subst e
    exact inverse_operator_contDiff n θ w F
  · simp only [BetaKernel.D, h1, h0, hm, ↓reduceIte]
    fun_prop

/-- Explicit normalized derivative array, before exponential truncation. -/
def operatorJet (e : ℤ) (n : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) : ℂ :=
  if e = -1 then inverseMoment n A θ w F / (n.factorial : ℂ)
  else if n = 0 then BetaKernel.D e A θ w F
  else if e = 1 ∧ n = 1 then F.eval (((w / θ : ℝ) : ℂ))
  else 0

theorem operator_jet (e : ℤ) (n : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) :
    jet n (fun z => BetaKernel.D e z θ w F) A = operatorJet e n A θ w F := by
  by_cases hm : e = -1
  · subst e
    simpa [operatorJet] using inverse_operator_jet n A θ w F
  by_cases hn : n = 0
  · subst n
    simp [operatorJet, hm, jet]
  by_cases h1 : e = 1
  · subst e
    simp only [BetaKernel.D, ↓reduceIte, jet]
    rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn), iteratedDeriv_mul_const_field]
    simp [iteratedDeriv_fun_id, operatorJet, hn]
    split_ifs <;> simp_all
  by_cases h0 : e = 0
  · simp [BetaKernel.D, operatorJet, hn, h0, jet, iteratedDeriv_const]
  · simp [BetaKernel.D, operatorJet, hm, hn, h1, h0, jet]

theorem operatorJet_continuous (e : ℤ) (n : ℕ) (θ : ℝ) (F : Polynomial ℂ) :
    Continuous (fun p : ℂ × ℝ => operatorJet e n p.1 θ p.2 F) := by
  by_cases hm : e = -1
  · simp only [operatorJet, hm, ↓reduceIte]
    exact (inverseMoment_continuous n θ F).div_const _
  · simp only [operatorJet, hm, ↓reduceIte, BetaKernel.D]
    split_ifs <;> fun_prop

theorem operator_jet_continuous (e : ℤ) (n : ℕ) (θ : ℝ) (F : Polynomial ℂ) :
    Continuous (fun p : ℂ × ℝ => jet n (fun z => BetaKernel.D e z θ p.2 F) p.1) := by
  simp_rw [operator_jet]
  exact operatorJet_continuous e n θ F

/-- Repeated parameter differentiation on a compact interval, from genuine
slice smoothness and joint continuity of its derivatives. -/
theorem iteratedDeriv_integral (F : ℂ → ℝ → ℂ) (a b : ℝ)
    (hc : ∀ n : ℕ, Continuous (fun p : ℂ × ℝ => iteratedDeriv n (fun z => F z p.2) p.1))
    (hd : ∀ t, ContDiff ℂ ⊤ (fun z => F z t)) (n : ℕ) :
    iteratedDeriv n (fun z => ∫ t in a..b, F z t) =
      fun z => ∫ t in a..b, iteratedDeriv n (fun x => F x t) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    apply HasDerivAt.deriv
    apply hasDerivAt_integral
      (fun x t => iteratedDeriv n (fun z => F z t) x)
      (fun x t => iteratedDeriv (n + 1) (fun z => F z t) x) a b z (hc n) (hc (n + 1))
    intro x t
    simpa only [iteratedDeriv_succ] using
      ((hd t).differentiable_iteratedDeriv n (show (n : WithTop ℕ∞) < ⊤ by simp) x).hasDerivAt

theorem jet_integral (F : ℂ → ℝ → ℂ) (a b : ℝ)
    (hc : ∀ n : ℕ, Continuous (fun p : ℂ × ℝ => iteratedDeriv n (fun z => F z p.2) p.1))
    (hd : ∀ t, ContDiff ℂ ⊤ (fun z => F z t)) (n : ℕ) (A : ℂ) :
    jet n (fun z => ∫ t in a..b, F z t) A =
      ∫ t in a..b, jet n (fun z => F z t) A := by
  simp only [jet, iteratedDeriv_integral F a b hc hd, intervalIntegral.integral_div]

theorem iteratedDeriv_eq_jet_mul (f : ℂ → ℂ) (n : ℕ) (A : ℂ) :
    iteratedDeriv n f A = jet n f A * (n.factorial : ℂ) := by
  simp [jet, Nat.factorial_ne_zero]

theorem weighted_operator_jet (e : ℤ) (θ a b : ℝ) (F : Polynomial ℂ)
    (c : ℝ → ℂ) (w : ℝ → ℝ) (hc : Continuous c) (hw : Continuous w)
    (n : ℕ) (A : ℂ) :
    jet n (fun z => ∫ v in a..b, c v * BetaKernel.D e z θ (w v) F) A =
      ∫ v in a..b, c v * jet n (fun z => BetaKernel.D e z θ (w v) F) A := by
  rw [jet_integral]
  · simp only [jet_const_mul]
  · intro k
    simp only [iteratedDeriv_const_mul_field]
    simp_rw [iteratedDeriv_eq_jet_mul]
    exact (hc.comp continuous_snd).mul
      (((operator_jet_continuous e k θ F).comp
        (continuous_fst.prodMk (hw.comp continuous_snd))).mul continuous_const)
  · intro v
    exact contDiff_const.mul (operator_contDiff e ⊤ θ (w v) F)

/-- Both independent shift derivatives commute with the actual outer integral.
The factors still contain the untruncated exponential. -/
theorem monomialIntegral_jet₂ (e f : ℤ) (n i j : ℕ) (A B : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    jet₂ i j (fun x y => BetaKernel.monomialIntegral x y θ F G e f n) A B =
      ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
        jet i (fun z => BetaKernel.D e z θ (θ - v) F) A *
        jet j (fun z => BetaKernel.D f z θ (θ - v) G) B := by
  have hD (e : ℤ) (P : Polynomial ℂ) (z : ℂ) :
      Continuous (fun v : ℝ => BetaKernel.D e z θ (θ - v) P) := by
    have h := (operator_jet_continuous e 0 θ P).comp
      ((continuous_const : Continuous (fun _ : ℝ => z)).prodMk
        (show Continuous (fun v : ℝ => θ - v) by fun_prop))
    simpa [jet, Function.comp_def] using h
  have hw : Continuous (fun v : ℝ => θ - v) := continuous_const.sub continuous_id
  have hc : Continuous (fun v : ℝ => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ)) := by
    fun_prop
  unfold jet₂
  have hin (x : ℂ) := weighted_operator_jet f θ 0 θ G
    (fun v => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * BetaKernel.D e x θ (θ - v) F)
    (fun v => θ - v) (hc.mul (hD e F x)) hw j B
  simp only [BetaKernel.monomialIntegral, hin]
  have he : (fun x => ∫ v in 0..θ,
      (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) * BetaKernel.D e x θ (θ - v) F *
        jet j (fun z => BetaKernel.D f z θ (θ - v) G) B) =
      fun x => ∫ v in 0..θ,
        ((v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
          jet j (fun z => BetaKernel.D f z θ (θ - v) G) B) * BetaKernel.D e x θ (θ - v) F := by
    funext x
    congr 1
    funext v
    ring
  rw [he, weighted_operator_jet e θ 0 θ F
    (fun v => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
      jet j (fun z => BetaKernel.D f z θ (θ - v) G) B) (fun v => θ - v)
    (by convert!
      hc.mul ((operator_jet_continuous f j θ G).comp
        ((continuous_const : Continuous (fun _ : ℝ => B)).prodMk hw)) using 1) hw]
  congr 1
  funext v
  ring

theorem integral_contDiff (F : ℂ → ℝ → ℂ) (a b : ℝ)
    (hc : ∀ n : ℕ, Continuous (fun p : ℂ × ℝ => iteratedDeriv n (fun z => F z p.2) p.1))
    (hd : ∀ t, ContDiff ℂ ⊤ (fun z => F z t)) (N : WithTop ℕ∞) :
    ContDiff ℂ N (fun z => ∫ t in a..b, F z t) := by
  apply Differentiable.contDiff
  intro A
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_integral F (fun z t => deriv (fun x => F x t) z) a b A
    (hc 0) (by
      convert! hc 1 using 1
      funext p
      simp only [Function.uncurry, iteratedDeriv_one])
  intro z t
  exact ((hd t).differentiable (by simp) z).hasDerivAt

theorem weighted_operator_contDiff (e : ℤ) (θ a b : ℝ) (F : Polynomial ℂ)
    (c : ℝ → ℂ) (w : ℝ → ℝ) (hc : Continuous c) (hw : Continuous w)
    (N : WithTop ℕ∞) :
    ContDiff ℂ N (fun z => ∫ v in a..b, c v * BetaKernel.D e z θ (w v) F) := by
  apply integral_contDiff
  · intro k
    simp only [iteratedDeriv_const_mul_field]
    simp_rw [iteratedDeriv_eq_jet_mul]
    exact (hc.comp continuous_snd).mul
      (((operator_jet_continuous e k θ F).comp
        (continuous_fst.prodMk (hw.comp continuous_snd))).mul continuous_const)
  · intro v
    exact contDiff_const.mul (operator_contDiff e ⊤ θ (w v) F)

theorem monomial_right_smooth (e f : ℤ) (n : ℕ) (A : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    ContDiff ℂ ⊤ (fun y => BetaKernel.monomialIntegral A y θ F G e f n) := by
  apply weighted_operator_contDiff
  · have h := (operator_jet_continuous e 0 θ F).comp
      ((continuous_const : Continuous (fun _ : ℝ => A)).prodMk
        (show Continuous (fun v : ℝ => θ - v) by fun_prop))
    simp only [jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    exact (by fun_prop : Continuous (fun v : ℝ => (v : ℂ) ^ (n - 1) /
      ((n - 1).factorial : ℂ))).mul h
  · fun_prop

set_option maxHeartbeats 800000 in
theorem monomial_slice_smooth (e f : ℤ) (n j : ℕ) (B : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    ContDiff ℂ ⊤ (fun x => jet j (fun y => BetaKernel.monomialIntegral x y θ F G e f n) B) := by
  have he : (fun x => jet j (fun y => BetaKernel.monomialIntegral x y θ F G e f n) B) =
      fun x => ∫ v in 0..θ,
        ((v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
          jet j (fun z => BetaKernel.D f z θ (θ - v) G) B) * BetaKernel.D e x θ (θ - v) F := by
    funext x
    have h := monomialIntegral_jet₂ e f n 0 j x B θ F G
    simp only [jet₂, jet_zero] at h
    rw [h]
    congr 1
    funext v
    ring
  rw [he]
  apply weighted_operator_contDiff e θ 0 θ F
    (fun v => (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
      jet j (fun z => BetaKernel.D f z θ (θ - v) G) B) (fun v => θ - v)
  · convert! (by fun_prop : Continuous (fun v : ℝ => (v : ℂ) ^ (n - 1) /
      ((n - 1).factorial : ℂ))).mul
      ((operator_jet_continuous f j θ G).comp
        ((continuous_const : Continuous (fun _ : ℝ => B)).prodMk
          (show Continuous (fun v : ℝ => θ - v) by fun_prop))) using 1
  · fun_prop

/-- A general numerator, not assumed to be a separable product. -/
theorem quotient_inner_jet (H : ℂ → ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (j : ℕ) (hi : ContDiff ℂ ⊤ (H A)) :
    jet j (fun y => H A y / (A + y)) B =
      ∑ b ∈ Finset.range (j + 1), jet b (H A) B * jet (j - b) (fun y => 1 / (A + y)) B := by
  have he : (fun y => H A y / (A + y)) = fun y => H A y * (1 / (A + y)) := by
    funext y
    ring
  rw [he, jet_mul _ _ B j (hi.of_le le_top).contDiffAt (by fun_prop)]

theorem quotient_outer_smooth (H : ℂ → ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (j D : ℕ) (hi : ∀ x, ContDiff ℂ ⊤ (H x))
    (ho : ∀ b, ContDiff ℂ ⊤ (fun x => jet b (H x) B)) :
    ContDiffAt ℂ D (fun x => jet j (fun y => H x y / (x + y)) B) A := by
  have hx : ∀ᶠ x in nhds A, x + B ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne h
  have he : (fun x => jet j (fun y => H x y / (x + y)) B) =ᶠ[nhds A]
      fun x => ∑ b ∈ Finset.range (j + 1), jet b (H x) B * jet (j - b) (fun y => 1 / (x + y)) B := by
    filter_upwards [hx] with x hx
    exact quotient_inner_jet H x B hx j (hi x)
  apply ContDiffAt.congr_of_eventuallyEq _ he
  apply ContDiffAt.sum
  intro b hb
  exact ((ho b).of_le le_top).contDiffAt.mul (reciprocal_slice_smooth A B h D (j - b))

theorem quotient_general_jet₂ (H : ℂ → ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (i j : ℕ) (hi : ∀ x, ContDiff ℂ ⊤ (H x))
    (ho : ∀ b, ContDiff ℂ ⊤ (fun x => jet b (H x) B)) :
    jet₂ i j (fun x y => H x y / (x + y)) A B =
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        jet₂ a b H A B * reciprocalCoeff (A + B) (i - a) (j - b) := by
  have hx : ∀ᶠ x in nhds A, x + B ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne h
  have he : (fun x => jet j (fun y => H x y / (x + y)) B) =ᶠ[nhds A]
      fun x => ∑ b ∈ Finset.range (j + 1), jet b (H x) B * jet (j - b) (fun y => 1 / (x + y)) B := by
    filter_upwards [hx] with x hx
    exact quotient_inner_jet H x B hx j (hi x)
  unfold jet₂
  rw [show jet i (fun x => jet j (fun y => H x y / (x + y)) B) A =
      jet i (fun x => ∑ b ∈ Finset.range (j + 1), jet b (H x) B *
        jet (j - b) (fun y => 1 / (x + y)) B) A from
    congrArg (fun z : ℂ => z / (i.factorial : ℂ)) (he.iteratedDeriv_eq i)]
  rw [jet_sum _ _ A i (by
    intro b hb
    exact ((ho b).of_le le_top).contDiffAt.mul (reciprocal_slice_smooth A B h i (j - b)))]
  simp_rw [jet_mul _ _ A i ((ho _).of_le le_top).contDiffAt
    (reciprocal_slice_smooth A B h i _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [show jet (i - a) (fun x => jet (j - b) (fun y => 1 / (x + y)) B) A =
    reciprocalCoeff (A + B) (i - a) (j - b) from reciprocal_mixed_jet A B h _ _]

/-- The adjoint convolution accepts an arbitrary rectangular numerator jet. -/
theorem W_matrix_contraction (D : ℕ) (op : ℕ → ℂ) (J : ℕ → ℕ → ℂ) (s : ℂ) :
    (∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
      op a * op b * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        J i j * reciprocalCoeff s (a - i) (b - j))) =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), W D op s i j * J i j := by
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ a ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (a + 1),
          ∑ b ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (b + 1),
            op a * op b * (J i j * reciprocalCoeff s (a - i) (b - j)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ i ∈ Finset.range (D + 1), ∑ a ∈ Finset.Ico i (D + 1),
          ∑ b ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (b + 1),
            op a * op b * (J i j * reciprocalCoeff s (a - i) (b - j)) := sum_lower_swap D _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [sum_lower_swap D]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [W, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

theorem quotient_general_W (H : ℂ → ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (D : ℕ) (op : ℕ → ℂ) (hi : ∀ x, ContDiff ℂ ⊤ (H x))
    (ho : ∀ b, ContDiff ℂ ⊤ (fun x => jet b (H x) B)) :
    contract₂ D op (fun x y => H x y / (x + y)) A B =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op (A + B) i j * jet₂ i j H A B := by
  rw [contract₂_rect D op _ A B (fun b _ => quotient_outer_smooth H A B h b D hi ho)]
  simp_rw [quotient_general_jet₂ H A B h _ _ hi ho]
  exact W_matrix_contraction D op (fun i j => jet₂ i j H A B) (A + B)

/-- W applied to the actual, integrated Laurent monomial. All inverse and
outer-integral regularity conditions are discharged. This is untruncated. -/
theorem monomial_quotient_W (e f : ℤ) (n D : ℕ) (op : ℕ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (θ : ℝ) (F G : Polynomial ℂ) :
    contract₂ D op (fun x y => BetaKernel.monomialIntegral x y θ F G e f n / (x + y)) A B =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op (A + B) i j *
          ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
            operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G := by
  rw [quotient_general_W _ A B h D op
    (fun x => monomial_right_smooth e f n x θ F G)
    (fun j => monomial_slice_smooth e f n j B θ F G)]
  simp_rw [monomialIntegral_jet₂, operator_jet]

/-- The exponential/reflection bridge for an integrated numerator. -/
theorem dual_general_W (H : ℂ → ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (D : ℕ) (q : ℕ → ℂ) (hi : ∀ x, ContDiff ℂ ⊤ (H x))
    (ho : ∀ b, ContDiff ℂ ⊤ (fun x => jet b (H x) (-B))) :
    contract₂ D (opMinus q)
      (fun x y => Complex.exp (-x - y) * (H (-x) (-y) / (-x + -y))) A B =
      Complex.exp (-A - B) *
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          W D (opPlus D q) (-A + -B) i j * jet₂ i j H (-A) (-B) := by
  have hn : -A + -B ≠ 0 := by simpa only [← neg_add, neg_ne_zero] using h
  rw [dual_contract₂ D q (fun x y => H x y / (x + y)) A B]
  · rw [← contract₂_rect D (opPlus D q) _ (-A) (-B)
      (fun b _ => quotient_outer_smooth H (-A) (-B) hn b D hi ho),
      quotient_general_W H (-A) (-B) hn D (opPlus D q) hi ho]
  · have hx : ∀ᶠ x in nhds (-A), x + -B ≠ 0 :=
      (continuousAt_id.add continuousAt_const).eventually_ne hn
    filter_upwards [hx] with x hx
    exact ((hi x).of_le le_top).contDiffAt.div
      (contDiffAt_const.add contDiffAt_id) hx
  · intro b hb
    exact quotient_outer_smooth H (-A) (-B) hn b D hi ho

theorem monomial_dual_W (e f : ℤ) (n D : ℕ) (q : ℕ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (θ : ℝ) (F G : Polynomial ℂ) :
    contract₂ D (opMinus q) (fun x y =>
      -(Complex.exp (-x - y) * BetaKernel.monomialIntegral (-y) (-x) θ F G e f n) /
        (x + y)) A B =
      Complex.exp (-A - B) *
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          W D (opPlus D q) (-A + -B) i j *
            ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
              operatorJet f i (-A) θ (θ - v) G * operatorJet e j (-B) θ (θ - v) F := by
  have he : (fun x y : ℂ =>
      -(Complex.exp (-x - y) * BetaKernel.monomialIntegral (-y) (-x) θ F G e f n) / (x + y)) =
      fun x y => Complex.exp (-x - y) *
        (BetaKernel.monomialIntegral (-x) (-y) θ G F f e n / (-x + -y)) := by
    funext x y
    rw [BetaKernel.monomialIntegral_swap (-y) (-x) θ F G e f n, ← neg_add, div_neg]
    ring
  rw [he, dual_general_W _ A B h D q
    (fun x => monomial_right_smooth f e n x θ G F)
    (fun j => monomial_slice_smooth f e n j (-B) θ G F)]
  simp_rw [monomialIntegral_jet₂, operator_jet]

/-- Entire right slices and entire outer slices of every normalized jet. -/
def Regular (H : ℂ → ℂ → ℂ) : Prop :=
  (∀ x, ContDiff ℂ ⊤ (H x)) ∧
  (∀ B j, ContDiff ℂ ⊤ (fun x => jet j (H x) B))

theorem regular_monomial (e f : ℤ) (n : ℕ) (θ : ℝ) (F G : Polynomial ℂ) :
    Regular (fun x y => BetaKernel.monomialIntegral x y θ F G e f n) :=
  ⟨fun x => monomial_right_smooth e f n x θ F G,
    fun B j => monomial_slice_smooth e f n j B θ F G⟩

theorem regular_const_mul (H : ℂ → ℂ → ℂ) (hH : Regular H) (c : ℂ) :
    Regular (fun x y => c * H x y) := by
  constructor
  · intro x
    exact contDiff_const.mul (hH.1 x)
  · intro B j
    simp only [jet_const_mul]
    exact contDiff_const.mul (hH.2 B j)

theorem regular_sum {ι : Type*} (s : Finset ι) (H : ι → ℂ → ℂ → ℂ)
    (hH : ∀ k ∈ s, Regular (H k)) : Regular (fun x y => ∑ k ∈ s, H k x y) := by
  constructor
  · intro x
    exact ContDiff.sum (fun k hk => (hH k hk).1 x)
  · intro B j
    have he : (fun x => jet j (fun y => ∑ k ∈ s, H k x y) B) =
        fun x => ∑ k ∈ s, jet j (H k x) B := by
      funext x
      exact jet_sum s (fun k => H k x) B j
        (fun k hk => (((hH k hk).1 x).of_le le_top).contDiffAt)
    rw [he]
    exact ContDiff.sum (fun k hk => (hH k hk).2 B j)

theorem jet₂_sum {ι : Type*} (s : Finset ι) (H : ι → ℂ → ℂ → ℂ)
    (hH : ∀ k ∈ s, Regular (H k)) (i j : ℕ) (A B : ℂ) :
    jet₂ i j (fun x y => ∑ k ∈ s, H k x y) A B = ∑ k ∈ s, jet₂ i j (H k) A B := by
  unfold jet₂
  have he : (fun x => jet j (fun y => ∑ k ∈ s, H k x y) B) =
      fun x => ∑ k ∈ s, jet j (H k x) B := by
    funext x
    exact jet_sum s (fun k => H k x) B j
      (fun k hk => (((hH k hk).1 x).of_le le_top).contDiffAt)
  rw [he, jet_sum s _ A i (fun k hk => ((hH k hk).2 B j).contDiffAt.of_le le_top)]

theorem jet₂_const_mul (H : ℂ → ℂ → ℂ) (c : ℂ) (i j : ℕ) (A B : ℂ) :
    jet₂ i j (fun x y => c * H x y) A B = c * jet₂ i j H A B := by
  simp only [jet₂, jet_const_mul]

theorem regular_poleSum (l m : ℕ) (E : ℤ → ℤ → ℕ → ℂ → ℂ → ℂ)
    (hE : ∀ e f n, Regular (E e f n)) :
    Regular (fun A B => BetaKernel.poleSum l m (fun e f n => E e f n A B)) := by
  unfold BetaKernel.poleSum
  apply regular_sum
  intro k hk
  apply regular_sum
  intro r hr
  apply regular_sum
  intro t ht
  exact regular_const_mul _ (hE _ _ _) _

theorem jet₂_poleSum (l m : ℕ) (E : ℤ → ℤ → ℕ → ℂ → ℂ → ℂ)
    (hE : ∀ e f n, Regular (E e f n)) (i j : ℕ) (A B : ℂ) :
    jet₂ i j (fun x y => BetaKernel.poleSum l m (fun e f n => E e f n x y)) A B =
      BetaKernel.poleSum l m (fun e f n => jet₂ i j (E e f n) A B) := by
  unfold BetaKernel.poleSum
  rw [jet₂_sum _ _ (by
    intro k hk
    apply regular_sum
    intro r hr
    apply regular_sum
    intro t ht
    exact regular_const_mul _ (hE _ _ _) _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [jet₂_sum _ _ (by
    intro r hr
    apply regular_sum
    intro t ht
    exact regular_const_mul _ (hE _ _ _) _)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [jet₂_sum _ _ (fun t ht => regular_const_mul _ (hE _ _ _) _)]
  simp only [jet₂_const_mul]

theorem regular_H (l m : ℕ) (θ : ℝ) (F G : Polynomial ℂ) :
    Regular (fun A B => BetaKernel.H l m A B θ F G) := by
  have he : (fun A B => BetaKernel.H l m A B θ F G) = fun A B =>
      ((θ : ℂ) ^ (l + m))⁻¹ * BetaKernel.poleSum l m
        (BetaKernel.monomialIntegral A B θ F G) := by
    funext A B
    unfold BetaKernel.H
    ring
  rw [he]
  exact regular_const_mul _ (regular_poleSum l m _ (fun e f n => regular_monomial e f n θ F G)) _

def monomialJet (e f : ℤ) (n i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
    operatorJet e i A θ (θ - v) F * operatorJet f j B θ (θ - v) G

def HJet (l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  BetaKernel.poleSum l m (fun e f n => monomialJet e f n i j A B θ F G) / (θ : ℂ) ^ (l + m)

theorem H_jet₂ (l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    jet₂ i j (fun x y => BetaKernel.H l m x y θ F G) A B = HJet l m i j A B θ F G := by
  have he (H : ℂ → ℂ → ℂ) (c : ℂ) :
      jet₂ i j (fun x y => H x y / c) A B = jet₂ i j H A B / c := by
    simp only [jet₂, jet, iteratedDeriv_div_const]
    ring
  simp only [BetaKernel.H, he]
  rw [jet₂_poleSum l m _ (fun e f n => regular_monomial e f n θ F G)]
  simp only [monomialIntegral_jet₂, operator_jet, HJet, monomialJet]

theorem regular_add (H K : ℂ → ℂ → ℂ) (hH : Regular H) (hK : Regular K) :
    Regular (fun x y => H x y + K x y) := by
  constructor
  · intro x
    exact (hH.1 x).add (hK.1 x)
  · intro B j
    have he : (fun x => jet j (fun y => H x y + K x y) B) =
        fun x => jet j (H x) B + jet j (K x) B := by
      funext x
      simp only [jet, iteratedDeriv_fun_add ((hH.1 x).of_le le_top).contDiffAt
        ((hK.1 x).of_le le_top).contDiffAt, add_div]
    rw [he]
    exact (hH.2 B j).add (hK.2 B j)

theorem jet₂_add (H K : ℂ → ℂ → ℂ) (hH : Regular H) (hK : Regular K)
    (i j : ℕ) (A B : ℂ) :
    jet₂ i j (fun x y => H x y + K x y) A B = jet₂ i j H A B + jet₂ i j K A B := by
  have he : (fun x => jet j (fun y => H x y + K x y) B) =
      fun x => jet j (H x) B + jet j (K x) B := by
    funext x
    simp only [jet, iteratedDeriv_fun_add ((hH.1 x).of_le le_top).contDiffAt
      ((hK.1 x).of_le le_top).contDiffAt, add_div]
  unfold jet₂
  rw [he]
  have ha := iteratedDeriv_fun_add ((hH.2 B j).of_le (show (i : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffAt
    ((hK.2 B j).of_le (show (i : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffAt (x := A)
  simpa only [jet, add_div] using congrArg (fun v : ℂ => v / (i.factorial : ℂ)) ha

theorem regular_fourTerms (θ : ℝ) (F G : Polynomial ℂ) :
    Regular (fun A B => BetaKernel.fourTerms A B θ F G) :=
  regular_add _ _ (regular_add _ _ (regular_add _ _
    (regular_H 0 0 θ F F) (regular_H 0 2 θ F G)) (regular_H 2 0 θ G F))
    (regular_H 2 2 θ G G)

def fourTermsJet (i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  HJet 0 0 i j A B θ F F + HJet 0 2 i j A B θ F G +
    HJet 2 0 i j A B θ G F + HJet 2 2 i j A B θ G G

theorem fourTerms_jet₂ (i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    jet₂ i j (fun x y => BetaKernel.fourTerms x y θ F G) A B = fourTermsJet i j A B θ F G := by
  unfold BetaKernel.fourTerms
  rw [jet₂_add _ _
    (regular_add _ _ (regular_add _ _ (regular_H 0 0 θ F F) (regular_H 0 2 θ F G))
      (regular_H 2 0 θ G F)) (regular_H 2 2 θ G G),
    jet₂_add _ _ (regular_add _ _ (regular_H 0 0 θ F F) (regular_H 0 2 θ F G))
      (regular_H 2 0 θ G F),
    jet₂_add _ _ (regular_H 0 0 θ F F) (regular_H 0 2 θ F G)]
  simp only [H_jet₂, fourTermsJet]

theorem fourTerms_quotient_W (D : ℕ) (op : ℕ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (θ : ℝ) (F G : Polynomial ℂ) :
    contract₂ D op (fun x y => BetaKernel.fourTerms x y θ F G / (x + y)) A B =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op (A + B) i j * fourTermsJet i j A B θ F G := by
  rw [quotient_general_W _ A B h D op (regular_fourTerms θ F G).1
    ((regular_fourTerms θ F G).2 B)]
  simp only [fourTerms_jet₂]

theorem fourTerms_swap (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    BetaKernel.fourTerms B A θ F G = BetaKernel.fourTerms A B θ F G := by
  simp only [BetaKernel.fourTerms, BetaKernel.H, BetaKernel.assemble00,
    BetaKernel.assemble20, BetaKernel.assemble02, BetaKernel.assemble22]
  simp_rw [BetaKernel.monomialIntegral_swap B A θ]
  ring

theorem fourTerms_dual_W (D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (θ : ℝ) (F G : Polynomial ℂ) :
    contract₂ D (opMinus q) (fun x y =>
      -(Complex.exp (-x - y) * BetaKernel.fourTerms (-y) (-x) θ F G) / (x + y)) A B =
      Complex.exp (-A - B) *
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          W D (opPlus D q) (-A + -B) i j * fourTermsJet i j (-A) (-B) θ F G := by
  have he : (fun x y : ℂ =>
      -(Complex.exp (-x - y) * BetaKernel.fourTerms (-y) (-x) θ F G) / (x + y)) =
      fun x y => Complex.exp (-x - y) *
        (BetaKernel.fourTerms (-x) (-y) θ F G / (-x + -y)) := by
    funext x y
    rw [fourTerms_swap, ← neg_add, div_neg]
    ring
  rw [he, dual_general_W _ A B h D q (regular_fourTerms θ F G).1
    ((regular_fourTerms θ F G).2 (-B))]
  simp only [fourTerms_jet₂]

theorem regular_dual (H : ℂ → ℂ → ℂ) (hH : Regular H) :
    Regular (fun x y => Complex.exp (-x - y) * H (-x) (-y)) := by
  constructor
  · intro x
    exact (show ContDiff ℂ ⊤ (fun y : ℂ => Complex.exp (-x - y)) by fun_prop).mul
      ((hH.1 (-x)).comp contDiff_neg)
  · intro B j
    have he : (fun x => jet j (fun y => Complex.exp (-x - y) * H (-x) (-y)) B) =
        fun x => Complex.exp (-x) *
          ((∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) *
            ((-1 : ℂ) ^ i * Complex.exp (-B)) *
            ((-1 : ℂ) ^ (j - i) *
              (jet (j - i) (H (-x)) (-B) * ((j - i).factorial : ℂ)))) / (j.factorial : ℂ)) := by
      funext x
      have hfun : (fun y : ℂ => Complex.exp (-x - y) * H (-x) (-y)) =
          fun y => Complex.exp (-x) * (Complex.exp (-y) * H (-x) (-y)) := by
        funext y
        rw [sub_eq_add_neg, Complex.exp_add]
        ring
      rw [hfun, jet_const_mul, jet, dual_derivative _ B j ((hH.1 (-x)).of_le le_top)]
      simp_rw [iteratedDeriv_eq_jet_mul]
    rw [he]
    apply ContDiff.mul (by fun_prop)
    apply ContDiff.div_const
    apply ContDiff.sum
    intro i hi
    exact contDiff_const.mul (contDiff_const.mul
      (((hH.2 (-B) (j - i)).comp contDiff_neg).mul contDiff_const))

theorem quotient_add_contract (H K : ℂ → ℂ → ℂ) (hH : Regular H) (hK : Regular K)
    (D : ℕ) (op : ℕ → ℂ) (A B : ℂ) (h : A + B ≠ 0) :
    contract₂ D op (fun x y => (H x y + K x y) / (x + y)) A B =
      contract₂ D op (fun x y => H x y / (x + y)) A B +
      contract₂ D op (fun x y => K x y / (x + y)) A B := by
  rw [quotient_general_W _ A B h D op (regular_add H K hH hK).1
    ((regular_add H K hH hK).2 B),
    quotient_general_W H A B h D op hH.1 (hH.2 B),
    quotient_general_W K A B h D op hK.1 (hK.2 B)]
  simp only [jet₂_add H K hH hK, mul_add, Finset.sum_add_distrib]

/-- Exact evaluator with untruncated inverse moments. Taylor truncation and
its error envelope are deliberately not built into this definition. -/
def exactEvaluator (D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
    W D (opMinus q) (A + B) i j * fourTermsJet i j A B θ F G) +
  Complex.exp (-A - B) *
    ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D (opPlus D q) (-A + -B) i j * fourTermsJet i j (-A) (-B) θ F G

/-- The actual two-variable differential operator on the full K2 functional
equals the assembled exact W evaluator. No derivative/interchange premise remains. -/
theorem K2_exact_evaluator (D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (θ : ℝ) (F G : Polynomial ℂ) :
    contract₂ D (opMinus q) (fun x y => BetaKernel.shiftedFunctional x y θ F G) A B =
      exactEvaluator D q A B θ F G := by
  have he : (fun x y => BetaKernel.shiftedFunctional x y θ F G) =
      fun x y => (BetaKernel.fourTerms x y θ F G +
        (-1) * (Complex.exp (-x - y) * BetaKernel.fourTerms (-x) (-y) θ F G)) / (x + y) := by
    funext x y
    unfold BetaKernel.shiftedFunctional
    rw [fourTerms_swap (-x) (-y) θ F G]
    ring
  rw [he, quotient_add_contract _ _ (regular_fourTerms θ F G)
    (regular_const_mul _ (regular_dual _ (regular_fourTerms θ F G)) (-1)) D (opMinus q) A B h,
    fourTerms_quotient_W D (opMinus q) A B h θ F G]
  have hd : (fun x y : ℂ => (-1) * (Complex.exp (-x - y) * BetaKernel.fourTerms (-x) (-y) θ F G) / (x + y)) =
      fun x y => -(Complex.exp (-x - y) * BetaKernel.fourTerms (-y) (-x) θ F G) / (x + y) := by
    funext x y
    rw [fourTerms_swap]
    ring
  rw [hd, fourTerms_dual_W D q A B h θ F G]
  rfl

theorem monomialJet_swap (e f : ℤ) (n i j : ℕ) (A B : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    monomialJet e f n i j A B θ F G = monomialJet f e n j i B A θ G F := by
  unfold monomialJet
  congr 1
  funext v
  ring

theorem HJet02_swap (i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    HJet 0 2 i j A B θ F G = HJet 2 0 j i B A θ G F := by
  simp only [HJet, BetaKernel.assemble02, BetaKernel.assemble20]
  rw [monomialJet_swap 1 1 3 i j A B θ F G,
    monomialJet_swap 1 0 2 i j A B θ F G,
    monomialJet_swap 1 (-1) 1 i j A B θ F G]

theorem contracted_cross_eq (D : ℕ) (op : ℕ → ℂ) (s A : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D op s i j * HJet 0 2 i j A A θ F G) =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op s i j * HJet 2 0 i j A A θ G F := by
  simp_rw [HJet02_swap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [W_symm D op s j i]

theorem contracted_fourTerms_diagonal (D : ℕ) (op : ℕ → ℂ) (s A : ℂ)
    (θ : ℝ) (F G : Polynomial ℂ) :
    (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D op s i j * fourTermsJet i j A A θ F G) =
      (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op s i j * HJet 0 0 i j A A θ F F) +
      2 * (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op s i j * HJet 2 0 i j A A θ G F) +
      (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op s i j * HJet 2 2 i j A A θ G G) := by
  simp only [fourTermsJet, mul_add, Finset.sum_add_distrib]
  rw [contracted_cross_eq]
  ring

#print axioms contracted_fourTerms_diagonal
#print axioms contracted_cross_eq
#print axioms K2_exact_evaluator
#print axioms fourTerms_jet₂
#print axioms fourTerms_quotient_W
#print axioms fourTerms_swap
#print axioms fourTerms_dual_W
#print axioms H_jet₂
#print axioms regular_H
#print axioms dual_general_W
#print axioms monomial_dual_W
#print axioms W_matrix_contraction
#print axioms quotient_general_W
#print axioms monomial_quotient_W
#print axioms monomial_right_smooth
#print axioms monomial_slice_smooth
#print axioms quotient_outer_smooth
#print axioms quotient_general_jet₂
#print axioms weighted_operator_jet
#print axioms monomialIntegral_jet₂

#print axioms operator_jet
#print axioms operator_jet_continuous
#print axioms iteratedDeriv_integral
#print axioms jet_integral

#print axioms inverse_operator_contDiff
#print axioms inverseMoment_continuous
#print axioms operator_contDiff
#print axioms hasDerivAt_integral
#print axioms inverseMoment_hasDerivAt
#print axioms inverseMoment_iteratedDeriv
#print axioms inverse_operator_jet
end XiPrime8845.IntegralJet
