import PRZZNoncentralResidues
import Zeta23.Analytic.RectangleLogDeriv
import Zeta23.FromPNTPlus.ZetaBounds

/-! Principal parts and the finite rectangle identity for the actual AFE
contour. All five possible poles are retained. Infinite vertical limits
and the identification of the direct/dual arithmetic sums are separate. -/
noncomputable section
open Complex Set Filter Topology Asymptotics
open scoped BigOperators
namespace XiPrime8845.PRZZFiniteContour
open PRZZAFEDual PRZZNoncentralResidues
set_option maxHeartbeats 3000000

def poleSet (a b : ℂ) (t : ℝ) : Finset ℂ :=
  {0,-leftArg a t,1-leftArg a t,-rightArg b t,1-rightArg b t}

def integrand (a b : ℂ) (t : ℝ) (s : ℂ) : ℂ := contourNumerator a b s t/s

/-- A finite possible-pole set supplies a punctured analytic neighborhood.
The residue limit then supplies a bounded remainder, not just a bounded
product (s-p)f(s). -/
theorem principal_part_of_limit (f : ℂ → ℂ) (S : Finset ℂ) (p A : ℂ)
    (hf : ∀ s, s ∉ S → DifferentiableAt ℂ f s)
    (hl : Tendsto (fun s => (s-p)*f s) (𝓝[≠] p) (𝓝 A)) :
    (f - fun s => A/(s-p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  classical
  let U : Set ℂ := ((S.erase p : Finset ℂ) : Set ℂ)ᶜ
  have hU : U ∈ 𝓝 p := (S.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  have hh : HolomorphicOn f (U \ {p}) := by
    intro s hs
    apply (hf s ?_).differentiableWithinAt
    intro hmem
    have hsp : s ≠ p := by simpa using hs.2
    exact hs.1 (Finset.mem_erase.mpr ⟨hsp,hmem⟩)
  obtain ⟨V,hV,hbdd⟩ := ResidueOfTendsTo hU hh hl
  simpa only [div_eq_mul_inv] using BddAbove_to_IsBigO hV hbdd

theorem pole_limit_exists (a b : ℂ) (t : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t)
    (p : ℂ) (hp : p ∈ poleSet a b t) :
    ∃ A : ℂ, Tendsto (fun s => (s-p)*integrand a b t s) (𝓝[≠] p) (𝓝 A) := by
  have hleft := small_shift_residues a b t ha hb ht (leftArg a t) (rightArg b t)
    (Or.inl ⟨rfl,rfl⟩)
  have hright := small_shift_residues a b t ha hb ht (rightArg b t) (leftArg a t)
    (Or.inr ⟨rfl,rfl⟩)
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hla : leftArg a t ≠ 0 ∧ leftArg a t ≠ 1 := by
    constructor <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [leftArg] at hh <;> linarith
  have hrb : rightArg b t ≠ 0 ∧ rightArg b t ≠ 1 := by
    constructor <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [rightArg] at hh <;> linarith
  simp only [poleSet,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,by simpa [integrand] using central_residue a b t hs hla.1 hrb.1 hla.2 hrb.2⟩
  · exact ⟨_,hleft.1⟩
  · exact ⟨_,hleft.2⟩
  · exact ⟨_,hright.1⟩
  · exact ⟨_,hright.2⟩

/-- Every actual possible pole has the locally bounded principal-part
remainder required by the finite residue theorem. -/
theorem principal_parts (a b : ℂ) (t : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) :
    ∀ p ∈ poleSet a b t,
      (integrand a b t - fun s => residue (integrand a b t) p/(s-p))
        =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  intro p hp
  obtain ⟨A,hA⟩ := pole_limit_exists a b t ha hb hs ht p hp
  rw [residue_eq_of_tendsto hA]
  apply principal_part_of_limit _ (poleSet a b t) p A _ hA
  intro s hsn
  apply PRZZContourKernel.contour_differentiable
  simpa [poleSet,PRZZContourKernel.poles] using hsn

/-- The truncation height puts all five possible poles strictly inside
the original rectangle; no boundary avoidance premise is supplied. -/
theorem poles_interior (a b : ℂ) (t H : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (ht : 1 ≤ t) (hH : t+1 < H) :
    ∀ p ∈ poleSet a b t, Rectangle ((-2:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I) ∈ 𝓝 p := by
  intro p hp
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have ai := abs_le.mp ((abs_im_le_norm a).trans ha)
  have bi := abs_le.mp ((abs_im_le_norm b).trans hb)
  rw [rectangle_mem_nhds_iff,mem_reProdIm]
  have hre : ((-2:ℂ)-(H:ℂ)*I).re ≤ ((2:ℂ)+(H:ℂ)*I).re := by simp
  have him : ((-2:ℂ)-(H:ℂ)*I).im ≤ ((2:ℂ)+(H:ℂ)*I).im := by simp; linarith
  rw [Set.uIoo_of_le hre,Set.uIoo_of_le him]
  simp only [poleSet,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [leftArg,rightArg] <;> (repeat' constructor) <;> norm_num at * <;> linarith

/-- The finite contour identity with all actual analytic premises supplied.
`residue` is the simple-pole limit; `pole_limit_exists` establishes its
existence at every member, including any removable possible pole. -/
theorem finite_rectangle (a b : ℂ) (t H : ℝ) (ha : ‖a‖ ≤ 1/4)
    (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) (hH : t+1 < H) :
    RectangleIntegral' (integrand a b t) ((-2:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I) =
      ∑ p ∈ poleSet a b t, residue (integrand a b t) p := by
  apply Zeta23.Analytic.residueTheorem_finset
    (by simp) (by simp; linarith) (poleSet a b t) (residue (integrand a b t))
    (poles_interior a b t H ha hb ht hH) _ (principal_parts a b t ha hb hs ht)
  intro s hmem
  apply (PRZZContourKernel.contour_differentiable a b s t ?_).differentiableWithinAt
  simpa [poleSet,PRZZContourKernel.poles] using hmem.2

#print axioms finite_rectangle
#print axioms poles_interior
#print axioms principal_part_of_limit
#print axioms pole_limit_exists
#print axioms principal_parts
end XiPrime8845.PRZZFiniteContour
