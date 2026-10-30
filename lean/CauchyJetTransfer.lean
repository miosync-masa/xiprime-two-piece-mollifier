import ArithmeticRegularity
import IntegralJet

/-! Cauchy transfer on the negative-shift bidisc. All slice regularity is
explicit or proved from the actual integral kernel. No PRZZ estimate is used. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Topology
namespace XiPrime8845.CauchyJetTransfer
open FiniteJet IntegralJet PRZZAsymptotic ArithmeticRegularity CompactShiftIntegral

/-- Local regularity, including the outer slices of every normalized right jet. -/
def RegularNegative (H : ℂ → ℂ → ℂ) : Prop :=
  (∀ x y : ℂ, x.re < 0 → y.re < 0 → ∀ n : ℕ, ContDiffAt ℂ n (H x) y) ∧
  (∀ y : ℂ, y.re < 0 → ∀ j : ℕ, ∀ x : ℂ, x.re < 0 → ∀ n : ℕ,
    ContDiffAt ℂ n (fun x => jet j (H x) y) x)

theorem regularNegative_of_smooth (H : ℂ → ℂ → ℂ)
    (h : ContDiffOn ℂ ∞ (fun p : ℂ × ℂ => H p.1 p.2) negativeShifts) :
    RegularNegative H := by
  constructor
  · intro x y hx hy n
    exact (((h (x,y) ⟨hx,hy⟩).contDiffAt
      (negativeShifts_open.mem_nhds ⟨hx,hy⟩)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  · intro y hy j x hx n
    have hs := rightIterated_smooth j (fun p : ℂ × ℂ => H p.1 p.2)
      negativeShifts negativeShifts_open h
    exact (((((hs (x,y) ⟨hx,hy⟩).contDiffAt
      (negativeShifts_open.mem_nhds ⟨hx,hy⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).div_const (j.factorial:ℂ)).of_le
        (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))

theorem jet_sub_at (H K : ℂ → ℂ → ℂ) (hH : RegularNegative H) (hK : RegularNegative K)
    (x y : ℂ) (hx : x.re < 0) (hy : y.re < 0) (j : ℕ) :
    jet j (fun y => H x y-K x y) y = jet j (H x) y-jet j (K x) y := by
  simp only [jet,iteratedDeriv_fun_sub (hH.1 x y hx hy j) (hK.1 x y hx hy j),sub_div]

theorem regularNegative_sub (H K : ℂ → ℂ → ℂ)
    (hH : RegularNegative H) (hK : RegularNegative K) :
    RegularNegative (fun x y => H x y-K x y) := by
  refine ⟨fun x y hx hy n => (hH.1 x y hx hy n).sub (hK.1 x y hx hy n),?_⟩
  intro y hy j x hx n
  have he : (fun x => jet j (fun y => H x y-K x y) y) =ᶠ[nhds x]
      (fun x => jet j (H x) y-jet j (K x) y) := by
    filter_upwards [(show ContinuousAt Complex.re x by fun_prop).eventually (gt_mem_nhds hx)] with z hz
    exact jet_sub_at H K hH hK z y hz hy j
  exact ((hH.2 y hy j x hx n).sub (hK.2 y hy j x hx n)).congr_of_eventuallyEq he

theorem jet₂_sub_at (H K : ℂ → ℂ → ℂ) (hH : RegularNegative H) (hK : RegularNegative K)
    (x y : ℂ) (hx : x.re < 0) (hy : y.re < 0) (a b : ℕ) :
    jet₂ a b (fun x y => H x y-K x y) x y = jet₂ a b H x y-jet₂ a b K x y := by
  have he : (fun x => jet b (fun y => H x y-K x y) y) =ᶠ[nhds x]
      (fun x => jet b (H x) y-jet b (K x) y) := by
    filter_upwards [(show ContinuousAt Complex.re x by fun_prop).eventually (gt_mem_nhds hx)] with z hz
    exact jet_sub_at H K hH hK z y hz hy b
  simp only [jet₂]
  unfold jet
  change iteratedDeriv a (fun x => jet b (fun y => H x y-K x y) y) x/(a.factorial:ℂ) = _
  rw [he.iteratedDeriv_eq a,iteratedDeriv_fun_sub (hH.2 y hy b x hx a) (hK.2 y hy b x hx a),sub_div]
  rfl

def cauchyConstant (a b : ℕ) : ℝ :=
  ((a.factorial:ℝ)*b.factorial/(R/4)^(a+b))/
    ‖(b.factorial:ℂ)‖/‖(a.factorial:ℂ)‖

theorem jet₂_bound (H : ℂ → ℂ → ℂ) (hH : RegularNegative H)
    (a b : ℕ) (C : ℝ) (hb : ∀ p ∈ witnessBidisc, ‖H p.1 p.2‖ ≤ C) :
    ‖jet₂ a b H (-R) (-R)‖ ≤ cauchyConstant a b*C := by
  have hr : 0 < R/4 := by have := radius_pos; positivity
  have hc : (-(R:ℂ)).re < 0 := by simpa using neg_neg_of_pos radius_pos
  have h := mixed_cauchy_bound H (-(R:ℂ)) (R/4) C a b hr (by
    intro x hx
    apply DifferentiableOn.diffContOnCl
    intro y hy
    exact ((hH.1 x y (closed_disc_re_neg x (Metric.sphere_subset_closedBall hx))
      (closed_disc_re_neg y (Metric.closure_ball_subset_closedBall hy)) 1).differentiableAt
      (by norm_num)).differentiableWithinAt) (by
    apply DifferentiableOn.diffContOnCl
    intro x hx
    have hs := (hH.2 (-R) hc b x
      (closed_disc_re_neg x (Metric.closure_ball_subset_closedBall hx)) 1).mul (contDiffAt_const (c := (b.factorial:ℂ)))
    simp only [jet,div_mul_cancel₀ _ (show (b.factorial:ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero b)] at hs
    exact (hs.differentiableAt (by norm_num)).differentiableWithinAt) (by
    intro x hx y hy
    exact hb (x,y) ⟨by simpa only [dist_eq_norm,sub_neg_eq_add] using (Metric.mem_sphere.mp hx).le,
      by simpa only [dist_eq_norm,sub_neg_eq_add] using (Metric.mem_sphere.mp hy).le⟩)
  simp only [jet₂,jet,iteratedDeriv_div_const,norm_div]
  exact (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right h (norm_nonneg _)) (norm_nonneg _)).trans_eq (by
      unfold cauchyConstant; ring)

/-- Uniform convergence on the closed bidisc controls every finite mixed jet
at its center. The two orders are independent, with no total-order cutoff. -/
theorem jet₂_tendsto (f : ℝ → ℂ → ℂ → ℂ) (H : ℂ → ℂ → ℂ)
    (hf : ∀ᶠ T in atTop, RegularNegative (f T)) (hH : RegularNegative H)
    (hu : TendstoUniformlyOn (fun T (p : ℂ × ℂ) => f T p.1 p.2)
      (fun p => H p.1 p.2) atTop witnessBidisc) (a b : ℕ) :
    Tendsto (fun T => jet₂ a b (f T) (-R) (-R)) atTop (nhds (jet₂ a b H (-R) (-R))) := by
  have hC : 0 ≤ cauchyConstant a b := by
    have hr : 0 < R/4 := by have := radius_pos; positivity
    unfold cauchyConstant
    positivity
  have hc : (-(R:ℂ)).re < 0 := by simpa using neg_neg_of_pos radius_pos
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he : 0 < eps/(cauchyConstant a b+1) := by positivity
  filter_upwards [hf,Metric.tendstoUniformlyOn_iff.mp hu _ he] with T hT huT
  rw [dist_eq_norm,← jet₂_sub_at (f T) H hT hH (-R) (-R) hc hc]
  apply (jet₂_bound _ (regularNegative_sub _ _ hT hH) a b _ (by
    intro p hp
    have hh := huT p hp
    rw [dist_comm,dist_eq_norm] at hh
    exact hh.le)).trans_lt
  have hh := mul_lt_mul_of_pos_left (lt_add_one (cauchyConstant a b)) he
  have heq : (eps/(cauchyConstant a b+1))*(cauchyConstant a b+1) = eps :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- The true quotient kernel, including the reflected height exponential. -/
theorem shiftedFunctional_regular (θ : ℝ) (F G : Polynomial ℂ) :
    RegularNegative (fun x y => BetaKernel.shiftedFunctional x y θ F G) := by
  let N := fun x y => BetaKernel.fourTerms x y θ F G+
    (-1)*(Complex.exp (-x-y)*BetaKernel.fourTerms (-x) (-y) θ F G)
  have hN : Regular N := regular_add _ _ (regular_fourTerms θ F G)
    (regular_const_mul _ (regular_dual _ (regular_fourTerms θ F G)) (-1))
  have he : (fun x y => BetaKernel.shiftedFunctional x y θ F G) =
      (fun x y => N x y/(x+y)) := by
    funext x y
    unfold BetaKernel.shiftedFunctional N
    rw [fourTerms_swap (-x) (-y) θ F G]
    ring
  have hn (x y : ℂ) (hx : x.re < 0) (hy : y.re < 0) : x+y ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re,Complex.zero_re] at hh
    linarith
  rw [he]
  constructor
  · intro x y hx hy n
    exact ((hN.1 x).of_le le_top).contDiffAt.div (by fun_prop) (hn x y hx hy)
  · intro y hy j x hx n
    exact quotient_outer_smooth N x y (hn x y hx hy) j n hN.1 (hN.2 y)

#print axioms regularNegative_of_smooth
#print axioms jet_sub_at
#print axioms regularNegative_sub
#print axioms jet₂_sub_at
#print axioms jet₂_bound
#print axioms jet₂_tendsto
#print axioms shiftedFunctional_regular
end XiPrime8845.CauchyJetTransfer

