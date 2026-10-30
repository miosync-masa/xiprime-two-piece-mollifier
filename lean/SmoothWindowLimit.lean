import SmoothWindow

/-! Interior unsmoothing of a nonnegative height-dependent density.
Each test function is fixed before the height limit; no uniformity over
test functions and no control of concentration at 1 or 2 is assumed. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.SmoothWindowLimit
open SmoothWindow
set_option maxHeartbeats 1000000

def weighted (F : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t, F T t*Phi (t/T))/T

def windowMoment (F : ℝ → ℝ → ℝ) (r T : ℝ) : ℝ :=
  (∫ t in window r T, F T t)/T

theorem window_integrable (F : ℝ → ℝ → ℝ)
    (hi : ∀ Phi, PRZZ.SmoothWeight Phi →
      ∀ᶠ T : ℝ in atTop, Integrable (fun t => F T t*Phi (t/T)))
    (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    ∀ᶠ T : ℝ in atTop, IntegrableOn (F T) (window r T) := by
  let b := (r+1/2)/2
  have hrb : r < b := by dsimp [b]; linarith
  have hb : b ≤ 1/2 := by dsimp [b]; linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hi _ (bump_smooth r b hr hrb hb)] with T hT hI
  apply hI.integrableOn.congr
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  dsimp only
  rw [bump_one r b hr hrb (t/T) ((scaled_mem r T t hT).mpr ht), mul_one]

/-- The actual sharp inner-window limit, not just a bound for a proxy. -/
theorem windowMoment_tendsto (F : ℝ → ℝ → ℝ) (c : ℝ)
    (hF : ∀ T t, 0 ≤ F T t)
    (hi : ∀ Phi, PRZZ.SmoothWeight Phi →
      ∀ᶠ T : ℝ in atTop, Integrable (fun t => F T t*Phi (t/T)))
    (hl : ∀ Phi, PRZZ.SmoothWeight Phi → (∀ x, 0 ≤ Phi x) →
      Tendsto (weighted F Phi) atTop
        (nhds (c*(∫ x in Set.Icc (1 : ℝ) 2, Phi x))))
    (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    Tendsto (windowMoment F r) atTop (nhds (c*(2*r))) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hmin : 0 < min r (min (1/2-r) (eps/(8*(|c|+1)))) :=
    lt_min hr (lt_min (by linarith) (by positivity))
  obtain ⟨a, ha, ham⟩ := exists_between hmin
  have har : a < r := ham.trans_le (min_le_left _ _)
  have hag : a < 1/2-r := ham.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < eps/(8*(|c|+1)) := ham.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlow : 0 < r-a := by linarith
  have hlr : r-a < r := by linarith
  have hra : r < r+a := by linarith
  have hrah : r+a ≤ 1/2 := by linarith
  let lo := bump (r-a) r hlow hlr
  let up := bump r (r+a) hr hra
  have hslo : PRZZ.SmoothWeight lo := bump_smooth _ _ _ _ hrh.le
  have hsup : PRZZ.SmoothWeight up := bump_smooth _ _ _ _ hrah
  have hmasslo := bump_mass (r-a) r hlow hlr hrh.le
  have hmassup := bump_mass r (r+a) hr hra hrah
  have hclose (m : ℝ) (hm : |m-2*r| ≤ 2*a) : |c*m-c*(2*r)| < eps/2 := by
    rw [← mul_sub, abs_mul]
    apply (mul_le_mul_of_nonneg_left hm (abs_nonneg c)).trans_lt
    have hh := (lt_div_iff₀ (show 0 < 8*(|c|+1) by positivity)).mp hae
    nlinarith [abs_nonneg c]
  have hclo := hclose (∫ x in Set.Icc (1 : ℝ) 2, lo x)
    (abs_le.mpr ⟨by dsimp [lo]; linarith [hmasslo.1], by dsimp [lo]; linarith [hmasslo.2]⟩)
  have hcup := hclose (∫ x in Set.Icc (1 : ℝ) 2, up x)
    (abs_le.mpr ⟨by dsimp [up]; linarith [hmassup.1], by dsimp [up]; linarith [hmassup.2]⟩)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hi lo hslo, hi up hsup,
    window_integrable F hi r hr hrh,
    Metric.tendsto_nhds.mp (hl lo hslo (fun x => lo.nonneg)) (eps/2) (by positivity),
    Metric.tendsto_nhds.mp (hl up hsup (fun x => up.nonneg)) (eps/2) (by positivity)]
    with T hT hIlo hIup hIr hLo hUp
  have hlower : weighted F lo T ≤ windowMoment F r T :=
    div_le_div_of_nonneg_right
      (integral_sandwich (r-a) r T hlow hlr hT (F T) (hF T) hIlo hIr).2 hT.le
  have hupper : windowMoment F r T ≤ weighted F up T :=
    div_le_div_of_nonneg_right
      (integral_le_weighted r (r+a) T hr hra hT (F T) (hF T) hIup) hT.le
  rw [Real.dist_eq] at hLo hUp ⊢
  rw [abs_lt] at hLo hUp hclo hcup ⊢
  constructor <;> linarith [hLo.1, hLo.2, hUp.1, hUp.2, hclo.1, hclo.2, hcup.1, hcup.2]

#print axioms window_integrable
#print axioms windowMoment_tendsto
end XiPrime8845.SmoothWindowLimit
