import SmoothWeightWitness

/-! Fixed smooth minorants and majorants for inner dyadic windows.
The radii are chosen before the height limit. No arithmetic input is used. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.SmoothWindow

def window (r T : ℝ) : Set ℝ := Set.Icc ((3/2-r)*T) ((3/2+r)*T)

def bump (a b : ℝ) (ha : 0 < a) (hab : a < b) : ContDiffBump (3/2 : ℝ) :=
  ⟨a, b, ha, hab⟩

theorem bump_one (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x : ℝ) (hx : x ∈ window a 1) : bump a b ha hab x = 1 := by
  apply (bump a b ha hab).one_of_mem_closedBall
  change |x-3/2| ≤ a
  simp only [window, Set.mem_Icc, mul_one] at hx
  rw [abs_le]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem bump_zero (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x : ℝ) (hx : x ∉ window b 1) : bump a b ha hab x = 0 := by
  apply (bump a b ha hab).zero_of_le_dist
  change b ≤ |x-3/2|
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨by simpa only [mul_one] using (show 3/2-b ≤ x by linarith [hh.1]),
    by simpa only [mul_one] using (show x ≤ 3/2+b by linarith [hh.2])⟩

theorem bump_smooth (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1/2) :
    PRZZ.SmoothWeight (bump a b ha hab) := by
  refine ⟨(bump a b ha hab).contDiff, ?_⟩
  intro x hx
  by_contra hh
  apply hx
  apply bump_zero a b ha hab
  intro h
  simp only [window, Set.mem_Icc, mul_one] at h
  exact hh ⟨by linarith [h.1], by linarith [h.2]⟩

theorem window_const (r : ℝ) (hr : 0 ≤ r) :
    (∫ _ in window r 1, (1 : ℝ)) = 2*r := by
  simp [window]
  rw [max_eq_left (by linarith)]
  ring

theorem bump_mass (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1/2) :
    2*a ≤ (∫ x in Set.Icc (1 : ℝ) 2, bump a b ha hab x) ∧
      (∫ x in Set.Icc (1 : ℝ) 2, bump a b ha hab x) ≤ 2*b := by
  have hi : IntegrableOn (bump a b ha hab) (Set.Icc (1 : ℝ) 2) :=
    (bump a b ha hab).continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hs : window a 1 ⊆ Set.Icc (1 : ℝ) 2 := by
    intro x hx
    simp only [window, Set.mem_Icc, mul_one] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  constructor
  · have hm := setIntegral_mono_set hi
      (Filter.Eventually.of_forall (fun x => (bump a b ha hab).nonneg))
      (Filter.Eventually.of_forall hs)
    have he : (∫ x in window a 1, bump a b ha hab x) = 2*a := by
      calc
        _ = ∫ _ in window a 1, (1 : ℝ) :=
          setIntegral_congr_fun measurableSet_Icc (bump_one a b ha hab)
        _ = _ := window_const a ha.le
    exact he ▸ hm
  · have he : (∫ x in Set.Icc (1 : ℝ) 2, bump a b ha hab x) =
        ∫ x in window b 1, bump a b ha hab x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      · intro x hx
        simp only [window, Set.mem_Icc, mul_one] at hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · intro x hx; exact bump_zero a b ha hab x hx.2
    rw [he, ← window_const b (ha.trans hab).le]
    apply setIntegral_mono_on
      ((bump a b ha hab).continuous.continuousOn.integrableOn_compact isCompact_Icc)
      (integrableOn_const (hs := by dsimp [window]; simp)) measurableSet_Icc
    exact fun x _ => (bump a b ha hab).le_one

theorem scaled_mem (r T t : ℝ) (hT : 0 < T) :
    t/T ∈ window r 1 ↔ t ∈ window r T := by
  simp only [window, Set.mem_Icc, mul_one, le_div_iff₀ hT, div_le_iff₀ hT]

theorem integral_le_weighted (a b T : ℝ) (ha : 0 < a) (hab : a < b) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hi : Integrable (fun t => f t*bump a b ha hab (t/T))) :
    (∫ t in window a T, f t) ≤ ∫ t, f t*bump a b ha hab (t/T) := by
  calc
    _ = ∫ t in window a T, f t*bump a b ha hab (t/T) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [bump_one a b ha hab (t/T) ((scaled_mem a T t hT).mpr ht), mul_one]
    _ ≤ _ := setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun t => mul_nonneg (hf t) (bump a b ha hab).nonneg))

/-- The upper and lower bounds keep the same density and the same height. -/
theorem integral_sandwich (a b T : ℝ) (ha : 0 < a) (hab : a < b) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hi : Integrable (fun t => f t*bump a b ha hab (t/T)))
    (hj : IntegrableOn f (window b T)) :
    (∫ t in window a T, f t) ≤ ∫ t, f t*bump a b ha hab (t/T) ∧
      (∫ t, f t*bump a b ha hab (t/T)) ≤ ∫ t in window b T, f t := by
  constructor
  · exact integral_le_weighted a b T ha hab hT f hf hi
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := window b T)
      (fun t ht => by rw [bump_zero a b ha hab (t/T)
        (fun h => ht ((scaled_mem b T t hT).mp h)), mul_zero])]
    exact setIntegral_mono_on hi.integrableOn hj measurableSet_Icc
      (fun t _ => mul_le_of_le_one_right (hf t) (bump a b ha hab).le_one)

#print axioms bump_smooth
#print axioms bump_one
#print axioms bump_zero
#print axioms bump_mass
#print axioms integral_sandwich
end XiPrime8845.SmoothWindow
