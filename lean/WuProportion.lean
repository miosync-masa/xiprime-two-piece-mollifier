import WuDyadicCounting
import WuTotalAsymptotic

/-! The actual xi-prime proportion, with analytic multiplicity.
The retained width and all error tolerances are fixed before the height.
Only the existing PRZZ input is used: no localized PRZZ, endpoint-tightness,
counting gate, or simplicity assumption is supplied to the final theorem. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.WuProportion
open WuDyadicCounting Zeta23.XiPrime
set_option maxHeartbeats 2000000

theorem dyadic_eventually (c : ℝ) (hc : c < proportion) :
    ∀ᶠ T : ℝ in atTop, c*(Ncount T (2*T):ℝ) ≤ (N0 T (2*T):ℝ) := by
  by_cases hc0 : c ≤ 0
  · exact Eventually.of_forall (fun T =>
      (mul_nonpos_of_nonpos_of_nonneg hc0 (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _))
  have hc0 : 0 < c := lt_of_not_ge hc0
  have hB : 0 < proportion := hc0.trans hc
  let δ : ℝ := (proportion-c)/(8*(proportion+1))
  let ε : ℝ := PRZZAsymptotic.R*δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ*(8*(proportion+1)) = proportion-c := by dsimp [δ]; field_simp
  have hd : δ < 1/2 := by nlinarith
  have hε : 0 < ε := mul_pos PRZZAsymptotic.radius_pos hδ
  have he : leading ε = proportion-2*δ := by
    unfold leading
    dsimp [ε]
    field_simp [PRZZAsymptotic.radius_pos.ne']
  have hgain : c < (1-2*δ)*leading ε := by
    rw [he]
    nlinarith [sq_nonneg δ]
  have hlead : 0 ≤ leading ε := by nlinarith
  have hlim : Tendsto (fun T => budget δ ε T/(T*Real.log T)-
      (Real.pi*c)*((Ncount T (2*T):ℝ)/(T*Real.log T))) atTop
      (nhds (((1-2*δ)*leading ε-c)/2)) := by
    convert (budget_normalized_tendsto δ ε).sub
      (WuTotalAsymptotic.dyadic_normalized.const_mul (Real.pi*c)) using 1
    field_simp
  have hpos : 0 < ((1-2*δ)*leading ε-c)/2 := by linarith
  filter_upwards [budget_eventually_le δ ε hδ hd hε hlead,
    hlim.eventually (lt_mem_nhds hpos),eventually_gt_atTop (1:ℝ)] with T hb hh hT
  rw [← mul_div_assoc,← sub_div] at hh
  have hdT : 0 < T*Real.log T := mul_pos (by linarith) (Real.log_pos hT)
  have hh' : 0 < budget δ ε T-(Real.pi*c)*(Ncount T (2*T):ℝ) :=
    (div_pos_iff_of_pos_right hdT).mp hh
  have hp : Real.pi*(c*(Ncount T (2*T):ℝ)) ≤ Real.pi*(N0 T (2*T):ℝ) := by nlinarith
  nlinarith [Real.pi_pos]

/-- Every coefficient strictly below the certified Wu coefficient holds
eventually, uniformly over ALL terminal real heights. -/
theorem cumulative_eventually (c : ℝ) (hc : c < proportion) :
    ∀ᶠ X : ℝ in atTop, c*(Ncount 0 X:ℝ) ≤ (N0 0 X:ℝ) := by
  have hh := WuTotalAsymptotic.cumulative proportion (fun ε hε =>
    eventually_atTop.mp (dyadic_eventually (proportion-ε) (by linarith)))
  obtain ⟨X₀,hX₀⟩ := hh (proportion-c) (by linarith)
  exact (eventually_ge_atTop X₀).mono (fun X hX => by simpa using hX₀ X hX)

/-- More than 88.45 percent, with multiplicity, under the one existing PRZZ
axiom. A strict margin is retained; this is stronger than an eventual
non-strict 0.8845 bound. -/
theorem strict_proportion : StrictProportion := by
  refine ⟨(proportion+0.8845)/2,by linarith [proportion_gt],?_⟩
  exact cumulative_eventually _ (by linarith [proportion_gt])

/-- Literal quotient statement. The denominator is eventually positive,
as supplied by the actual AF zero-count growth theorem. -/
theorem ratio_eventually_gt :
    ∀ᶠ X : ℝ in atTop, (0.8845:ℝ) < (N0 0 X:ℝ)/(Ncount 0 X:ℝ) := by
  obtain ⟨b,hb,h⟩ := strict_proportion
  filter_upwards [h,WuTotalAsymptotic.total_growth.eventually_gt_atTop 0] with X hX hn
  exact hb.trans_le ((le_div_iff₀ hn).mpr hX)

#print axioms dyadic_eventually
#print axioms cumulative_eventually
#print axioms strict_proportion
#print axioms ratio_eventually_gt
end XiPrime8845.WuProportion
