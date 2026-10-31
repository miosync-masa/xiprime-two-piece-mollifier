import WuEdgeLog
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Countable endpoint avoidance. A fixed countable family of bad-height
sets can be avoided simultaneously after scaling. For a moving family f_T,
countability of each fixed-T zero set does NOT imply countability of the
diagonal bad terminal set. That supplier is intentionally not asserted. -/
noncomputable section
open Set Complex
namespace XiPrime8845.WuSafeEndpoints
open WuLittlewood

def badTerminals (scale : ℕ → ℝ) (bad : ℕ → Set ℝ) : Set ℝ :=
  ⋃ j, (fun t => t/scale j) '' bad j

theorem badTerminals_countable (scale : ℕ → ℝ) (bad : ℕ → Set ℝ)
    (hb : ∀ j, (bad j).Countable) : (badTerminals scale bad).Countable :=
  countable_iUnion (fun j => (hb j).image _)

/-- One terminal parameter avoids ALL the prescribed scaled endpoints.
The bad sets must be fixed before choosing that parameter. -/
theorem exists_safe_terminal (scale : ℕ → ℝ) (hs : ∀ j, scale j ≠ 0)
    (bad : ℕ → Set ℝ) (hb : ∀ j, (bad j).Countable)
    (l r : ℝ) (hlr : l < r) :
    ∃ X ∈ Ioo l r, ∀ j, X*scale j ∉ bad j := by
  obtain ⟨X,hX,hinterval⟩ := ((badTerminals_countable scale bad hb).dense_compl ℝ).exists_between hlr
  refine ⟨X,hinterval,?_⟩
  intro j hj
  apply hX
  exact mem_iUnion.mpr ⟨j,⟨X*scale j,hj,mul_div_cancel_right₀ X (hs j)⟩⟩

def badHeights (f : ℂ → ℂ) : Set ℝ := Complex.im '' {s | f s = 0}

theorem badHeights_countable (f : ℂ → ℂ) (hf : {s | f s = 0}.Countable) :
    (badHeights f).Countable := hf.image _

theorem horizontal_nonzero (f : ℂ → ℂ) (t : ℝ) (ht : t ∉ badHeights f) (x : ℝ) :
    f (point x t) ≠ 0 := by
  intro hz
  apply ht
  exact ⟨point x t,hz,by simp [point]⟩

/-- Horizontal avoidance does not replace the two vertical nonvanishing
conditions required by AF's rectangle argument principle. -/
theorem boundary_nonzero (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (hu : u ∉ badHeights f) (hv : v ∉ badHeights f)
    (ha : ∀ t ∈ Icc u v, f (point a t) ≠ 0)
    (hb : ∀ t ∈ Icc u v, f (point b t) ≠ 0) :
    ∀ s ∈ RectangleBorder (point a u) (point b v), f s ≠ 0 := by
  intro s hs
  simp only [RectangleBorder,point,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
    mul_zero,sub_self,add_zero,add_im,mul_im,mul_one,zero_add,
    uIcc_of_le hab,uIcc_of_le huv,mem_union,mem_reProdIm,mem_singleton_iff] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · have he : s = point s.re u := by apply Complex.ext <;> simp [point,hs.2]
    rw [he]; exact horizontal_nonzero f u hu s.re
  · have he : s = point a s.im := by apply Complex.ext <;> simp [point,hs.1]
    rw [he]; exact ha s.im hs.2
  · have he : s = point s.re v := by apply Complex.ext <;> simp [point,hs.2]
    rw [he]; exact horizontal_nonzero f v hv s.re
  · have he : s = point b s.im := by apply Complex.ext <;> simp [point,hs.1]
    rw [he]; exact hb s.im hs.2

/-- Terminal-anchored geometric endpoints for a fixed countable family.
Every horizontal line is safe for every member, so adjacent cells may use
different members without losing their common safe endpoint. -/
theorem exists_safe_geometric_family (F : ℕ → ℂ → ℂ)
    (hF : ∀ k, {s | F k s = 0}.Countable) (r : ℝ) (hr : r ≠ 0)
    (l h : ℝ) (hlh : l < h) :
    ∃ X ∈ Ioo l h, ∀ j k : ℕ, ∀ x : ℝ, F k (point x (X*r^j)) ≠ 0 := by
  let bad : Set ℝ := ⋃ k, badHeights (F k)
  have hb : bad.Countable := countable_iUnion (fun k => badHeights_countable (F k) (hF k))
  obtain ⟨X,hX,hgood⟩ := exists_safe_terminal (fun j => r^j) (fun j => pow_ne_zero j hr)
    (fun _ => bad) (fun _ => hb) l h hlh
  refine ⟨X,hX,?_⟩
  intro j k x
  apply horizontal_nonzero
  intro ht
  exact hgood j (mem_iUnion.mpr ⟨k,ht⟩)

/-- Connect safe horizontal heights and separately verified vertical sides
to Littlewood, constructing both the finite zero set and the edge lifts. -/
theorem littlewood_of_safe_heights (f : ℂ → ℂ) (a b u v : ℝ)
    (hab : a ≤ b) (huv : u ≤ v)
    (hf : AnalyticOnNhd ℂ f (Rectangle (point a u) (point b v)))
    (hu : u ∉ badHeights f) (hv : v ∉ badHeights f)
    (ha : ∀ t ∈ Icc u v, f (point a t) ≠ 0)
    (hb : ∀ t ∈ Icc u v, f (point b t) ≠ 0) :
    ∃ Z : Finset ℂ, ∃ q : BoundaryLogs f a b u v,
      (∀ s, s ∈ Z ↔ s ∈ Rectangle (point a u) (point b v) ∧ f s = 0) ∧
      2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt f s:ℝ)*(s.re-a)) = boundaryLog f a b u v q := by
  classical
  have hn := boundary_nonzero f a b u v hab huv hu hv ha hb
  have hcorner : point a u ∈ Rectangle (point a u) (point b v) := left_mem_rect _ _
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf hcorner (ha u ⟨le_rfl,huv⟩)
  let Z := hfin.toFinset
  have he (s : ℂ) : s ∈ Z ↔ s ∈ Rectangle (point a u) (point b v) ∧ f s = 0 := by
    simp [Z]
  obtain ⟨q,hq⟩ := littlewood_of_boundary_nonzero f a b u v hab huv hf hn Z
    (fun s hs => ⟨fun hz => (he s).mpr ⟨hs,hz⟩,fun hz => ((he s).mp hz).2⟩)
    (fun s hs => ((he s).mp hs).1)
  exact ⟨Z,q,he,hq⟩

/-- A diagnostic example: every fixed-T function has only one zero, but
the moving upper endpoint is a zero for every T. -/
theorem moving_endpoint_zero (T : ℝ) :
    (fun s : ℂ => s-point (1/2) T) (point (1/2) T) = 0 := sub_self _

#print axioms badTerminals_countable
#print axioms exists_safe_terminal
#print axioms badHeights_countable
#print axioms horizontal_nonzero
#print axioms boundary_nonzero
#print axioms exists_safe_geometric_family
#print axioms littlewood_of_safe_heights
#print axioms moving_endpoint_zero
end XiPrime8845.WuSafeEndpoints
