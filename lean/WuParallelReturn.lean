import WuDeflatedContour
import WuBoundaryPhase
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Return from zero-free parallel vertical paths to the deflated critical
curve. All neighborhood choices are made with L,u,v frozen. No uniform
zero-free strip for the moving T family is asserted. -/
noncomputable section
open scoped BigOperators
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuParallelReturn
open WuLittlewood WuCriticalDeflation WuAuxiliary WuDeflatedContour
set_option maxHeartbeats 2000000

theorem nonzero_strip (f : ℂ → ℂ) (hf : Continuous f) (a u v : ℝ)
    (hn : ∀ t ∈ Icc u v, f (point a t) ≠ 0) :
    ∃ r > 0, ∀ x ∈ Icc (a-r) (a+r), ∀ t ∈ Icc u v, f (point x t) ≠ 0 := by
  have hopen : IsOpen {p : ℝ × ℝ | f (point p.1 p.2) ≠ 0} :=
    (isClosed_singleton.preimage (hf.comp (by unfold point; fun_prop))).isOpen_compl
  obtain ⟨U,V,hU,hV,ha,hI,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({a}:Set ℝ)) isCompact_Icc hopen (by
      intro p hp
      obtain rfl : p.1 = a := hp.1
      exact hn _ hp.2)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (ha (show a ∈ ({a}:Set ℝ) from rfl)))
  refine ⟨r/2,by positivity,?_⟩
  intro x hx t ht
  apply hUV (show (x,t) ∈ U ×ˢ V from ⟨hrU ?_,hI ht⟩)
  rw [Metric.mem_ball,Real.dist_eq,abs_lt]
  constructor <;> linarith [hx.1,hx.2]

theorem vertical_continuousAt (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a u v : ℝ) (huv : u ≤ v) (hn : ∀ t ∈ Icc u v, f (point a t) ≠ 0) :
    ContinuousAt (fun x => ∫ t in u..v, I*logDeriv f (point x t)) a := by
  obtain ⟨r,hr,hnr⟩ := nonzero_strip f hf.continuous a u v hn
  have hab : a-r ≤ a+r := by linarith
  let F := fun x t : ℝ => I*logDeriv f
    (point (projIcc (a-r) (a+r) hab x) (projIcc u v huv t))
  have hF : Continuous (Function.uncurry F) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hne := hnr (projIcc (a-r) (a+r) hab p.1)
      (projIcc (a-r) (a+r) hab p.1).property (projIcc u v huv p.2)
      (projIcc u v huv p.2).property
    have hld : ContinuousAt (logDeriv f)
        (point (projIcc (a-r) (a+r) hab p.1) (projIcc u v huv p.2)) :=
      ((hf.analyticAt _).deriv.continuousAt).div (hf.continuous.continuousAt) hne
    exact continuousAt_const.mul (hld.comp (f := fun p : ℝ × ℝ => point
        (projIcc (a-r) (a+r) hab p.1) (projIcc u v huv p.2)) (by
      unfold point; fun_prop))
  have he (x : ℝ) (hx : x ∈ Icc (a-r) (a+r)) :
      (∫ t in u..v, F x t) = ∫ t in u..v, I*logDeriv f (point x t) := by
    apply integral_congr
    intro t ht
    simp only [F,projIcc_of_mem hab hx,projIcc_of_mem huv (by simpa [uIcc_of_le huv] using ht)]
  have h : ContinuousAt (fun x => ∫ t in u..v, F x t) a :=
    (continuous_parametric_intervalIntegral_of_continuous' hF u v).continuousAt
  rw [ContinuousAt,he a (by constructor <;> linarith)] at h
  apply h.congr'
  filter_upwards [Icc_mem_nhds (show a-r < a by linarith) (show a < a+r by linarith)] with x hx
  exact he x hx

/-- The original eta phase on a zero-free parallel path is bounded by the
full critical xi' multiplicity, up to an arbitrarily small fixed-window
error. This includes critical eta zeros, without a simplicity hypothesis. -/
theorem parallel_phase_count (L u v : ℝ) (hL : L ≠ 0) (huv : u ≤ v) :
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ Zeta23.XiPrime.xiDeriv s = 0) ∧
      ∀ ε > 0, ∃ r > 0, ∀ x : ℝ, 0 < |x-1/2| → |x-1/2| < r →
        (∀ t ∈ Icc u v, WuAuxiliary.eta L (point x t) ≠ 0) ∧
        |(∫ t in u..v, I*logDeriv (WuAuxiliary.eta L) (point x t)).im| ≤
          Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)+ε := by
  obtain ⟨d,q,S,hS,hcount⟩ := WuPhaseCrossings.critical_phase_count L u v hL huv
  refine ⟨S,hS,?_⟩
  intro ε hε
  obtain ⟨r,hr,hnr⟩ := nonzero_strip d.etaPart d.eta_entire.continuous (1/2) u v
    (by simpa [point,critical] using d.nonzero)
  have hf : Differentiable ℂ d.curve := d.eta_entire.const_mul _
  have hc := vertical_continuousAt d.curve hf (1/2) u v huv
    (by simpa [point,critical] using d.curve_nonzero)
  have he := WuBoundaryPhase.edge_increment q huv u v le_rfl huv le_rfl
  have he' : (∫ t in u..v, I*logDeriv d.curve (point (1/2) t)).im =
      (q.value v).im-(q.value u).im := by simpa [point] using congrArg Complex.im he
  have hnear : ∀ᶠ x in 𝓝 (1/2:ℝ),
      |(∫ t in u..v, I*logDeriv d.curve (point x t)).im| <
        |(q.value v).im-(q.value u).im|+ε := by
    have h := (Complex.continuous_im.continuousAt.comp hc).abs
    dsimp only [Function.comp_def] at h
    rw [ContinuousAt,he'] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r',hr',hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min r r',lt_min hr hr',?_⟩
  intro x hx hxr
  have hx' : x ∈ Icc (1/2-r) (1/2+r) := by
    have ha := abs_lt.mp (hxr.trans_le (min_le_left _ _))
    constructor <;> linarith
  have hoff (t : ℝ) (c : ℂ) (hc : c ∈ d.zeros) : point x t ≠ c := by
    obtain ⟨y,hy,rfl⟩ := ((d.mem_zeros c).mp hc).1
    intro he
    have hre := congrArg Complex.re he
    simp [point,critical] at hre
    norm_num [hre] at hx
  have hg := fun t ht => hnr x hx' t ht
  refine ⟨?_,?_⟩
  · intro t ht
    rw [d.eta_factor]
    apply mul_ne_zero _ (hg t ht)
    unfold WuFiniteDeflation.divisor
    exact Finset.prod_ne_zero_iff.mpr (fun c hc => pow_ne_zero _ (sub_ne_zero.mpr (hoff t c hc)))
  · have hb := vertical_comparison d x huv (fun t _ c hc => hoff t c hc) hg
    have hh' := hh (by simpa [Real.dist_eq] using hxr.trans_le (min_le_right _ _))
    have hn := (div_le_iff₀ Real.pi_pos).mp (show
        |(q.value v).im-(q.value u).im|/Real.pi ≤
          (∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1-d.totalOrder by linarith)
    nlinarith

#print axioms nonzero_strip
#print axioms vertical_continuousAt
#print axioms parallel_phase_count
end XiPrime8845.WuParallelReturn
