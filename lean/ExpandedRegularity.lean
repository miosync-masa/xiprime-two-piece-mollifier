import ExpandedGcd
/-! Analytic regularity on the expanded time support; no asymptotic input. -/
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory Complex
namespace XiPrime8845.ExpandedRegularity
open PRZZ CompactShiftIntegral ArithmeticRegularity
theorem time_segment (T : ℝ) (hT : 0 < T) :
    ∀ t ∈ Icc (T/2) (5/2*T), (t : ℂ) ∈ timeStrip := by
  intro t ht
  exact ⟨(half_pos hT).trans_le ht.1, by norm_num⟩

theorem momentWeight_continuous (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) : Continuous (momentWeight P Q theta T Phi) := by
  unfold momentWeight
  have hP := dirichletPolynomial_continuous (coefficient P theta T) (cutoff theta T)
  have hQ := dirichletPolynomial_continuous (coefficient Q theta T) (cutoff theta T)
  exact ((hP.comp (by fun_prop)).mul (hQ.comp (by fun_prop)).star).mul
    (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (by fun_prop)))

theorem twistedMoment_smooth (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (fun p : Shift => twistedMoment P Q theta T Phi p.1 p.2) negativeShifts := by
  have h := compact_integral_smooth (momentCore T) (momentWeight P Q theta T Phi)
    (T/2) (5/2*T) negativeShifts timeStrip negativeShifts_open timeStrip_open
    (momentCore_smooth T hT) (momentWeight_continuous P Q theta T Phi hPhi).continuousOn
    (time_segment T (by linarith))
  apply h.congr
  intro p hp
  rw [twistedMoment, ExpandedGcd.weighted_integral_restrict _ Phi hPhi T (by linarith)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight, momentCore, smul_eq_mul]
  ring


#print axioms twistedMoment_smooth
end XiPrime8845.ExpandedRegularity

