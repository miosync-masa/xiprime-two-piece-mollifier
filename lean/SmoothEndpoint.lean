import PRZZLocalization
import SmoothWindow

/-! Fixed endpoint majorants, with full mass at most 8 delta. Unlike an inner
window bump they cross both dyadic boundaries. No analytic input is used. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.SmoothEndpoint
open PRZZLocalization SmoothWindow

def cap (c δ : ℝ) (hδ : 0 < δ) : ContDiffBump c :=
  ⟨δ, 2*δ, hδ, by linarith⟩

theorem cap_one (c δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : |u-c| ≤ δ) :
    cap c δ hδ u = 1 :=
  (cap c δ hδ).one_of_mem_closedBall (by simpa [Real.dist_eq,cap] using hu)

theorem cap_support (c δ : ℝ) (hδ : 0 < δ) :
    SmoothWeightOn (c-2*δ) (c+2*δ) (cap c δ hδ) := by
  refine ⟨(cap c δ hδ).contDiff, ?_⟩
  intro u hu
  rw [(cap c δ hδ).support_eq] at hu
  have hh : |u-c| < 2*δ := by simpa [cap, Real.dist_eq] using hu
  exact ⟨by linarith [(abs_lt.mp hh).1], by linarith [(abs_lt.mp hh).2]⟩

theorem cap_mass (c δ : ℝ) (hδ : 0 < δ) :
    0 ≤ fullMass (cap c δ hδ) ∧ fullMass (cap c δ hδ) ≤ 4*δ := by
  refine ⟨integral_nonneg (fun _ => (cap c δ hδ).nonneg), ?_⟩
  rw [fullMass_eq (cap_support c δ hδ)]
  have hh := setIntegral_mono_on (integrable (cap_support c δ hδ)).integrableOn
    (integrableOn_const (hs := by simp) : IntegrableOn (fun _ : ℝ => (1:ℝ))
      (Set.Icc (c-2*δ) (c+2*δ))) measurableSet_Icc
    (fun u _ => (cap c δ hδ).le_one)
  have hc : (∫ _ in Set.Icc (c-2*δ) (c+2*δ), (1:ℝ)) = 4*δ := by
    simp
    rw [max_eq_left (by linarith)]
    ring
  exact hh.trans_eq hc

def weight (δ : ℝ) (hδ : 0 < δ) (u : ℝ) : ℝ := cap 1 δ hδ u+cap 2 δ hδ u

theorem weight_nonneg (δ : ℝ) (hδ : 0 < δ) (u : ℝ) : 0 ≤ weight δ hδ u :=
  add_nonneg (cap 1 δ hδ).nonneg (cap 2 δ hδ).nonneg

theorem weight_smooth (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/4) :
    SmoothWeightOn (1/2) (5/2) (weight δ hδ) := by
  refine ⟨(cap 1 δ hδ).contDiff.add (cap 2 δ hδ).contDiff, ?_⟩
  intro u hu
  by_cases h1 : cap 1 δ hδ u = 0
  · have h2 : cap 2 δ hδ u ≠ 0 := by intro hz; exact hu (by simp [weight,h1,hz])
    have hh := (cap_support 2 δ hδ).2 h2
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · have hh := (cap_support 1 δ hδ).2 h1
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem weight_mass (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ fullMass (weight δ hδ) ∧ fullMass (weight δ hδ) ≤ 8*δ := by
  refine ⟨integral_nonneg (weight_nonneg δ hδ), ?_⟩
  unfold fullMass weight
  rw [integral_add (integrable (cap_support 1 δ hδ)) (integrable (cap_support 2 δ hδ))]
  have h1 := (cap_mass 1 δ hδ).2
  have h2 := (cap_mass 2 δ hδ).2
  dsimp [fullMass] at h1 h2
  linarith

/-- Covers the literal set difference, including either original endpoint. -/
theorem endpoint_majorant (δ T t : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (ht : t ∈ window (1/2) T \ window (1/2-δ) T) :
    1 ≤ weight δ hδ (t/T) := by
  have hfull := (scaled_mem (1/2) T t hT).mpr ht.1
  have hnot : t/T ∉ window (1/2-δ) 1 := fun hh => ht.2 ((scaled_mem _ T t hT).mp hh)
  simp only [window, Set.mem_Icc, mul_one] at hfull hnot
  by_cases hl : t/T ≤ 1+δ
  · have he := cap_one 1 δ hδ (t/T) (by rw [abs_le]; constructor <;> linarith [hfull.1])
    simpa [weight,he] using (show 1 ≤ 1+cap 2 δ hδ (t/T) by linarith [(cap 2 δ hδ).nonneg (x := t/T)])
  · have hr : 2-δ < t/T := by
      by_contra hh
      exact hnot ⟨by linarith, by linarith⟩
    have he := cap_one 2 δ hδ (t/T) (by rw [abs_le]; constructor <;> linarith [hfull.2])
    simp only [weight,he]
    linarith [(cap 1 δ hδ).nonneg (x := t/T)]

/-- A single fixed majorant for all seven derivative moments. -/
def fullCap : ContDiffBump (3/2 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

theorem fullCap_smooth : SmoothWeightOn (1/2) (5/2) fullCap := by
  refine ⟨fullCap.contDiff, ?_⟩
  intro u hu
  rw [fullCap.support_eq] at hu
  have hh : |u-3/2| < 1 := by simpa [fullCap,Real.dist_eq] using hu
  exact ⟨by linarith [(abs_lt.mp hh).1], by linarith [(abs_lt.mp hh).2]⟩

theorem fullCap_one (u : ℝ) (hu : u ∈ Set.Icc (1:ℝ) 2) : fullCap u = 1 := by
  apply fullCap.one_of_mem_closedBall
  change |u-3/2| ≤ 1/2
  rw [abs_le]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

#print axioms cap_mass
#print axioms weight_smooth
#print axioms weight_mass
#print axioms endpoint_majorant
#print axioms fullCap_smooth
#print axioms fullCap_one
end XiPrime8845.SmoothEndpoint
