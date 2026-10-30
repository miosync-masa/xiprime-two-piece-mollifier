import ExpandedHeight
import PRZZLocalizedError
import TwoPieceMainTerm

/-! Four-component arithmetic and localized PRZZ on [1/2,5/2].
Only the moment theorem assumes LocalizedEstimate; the gcd limit does not. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.ExpandedMainTerm
open PRZZAsymptotic PRZZLocalization ConreyCoefficientBridge
open GcdDecomposition ConreyMainTerm FengMixedMainTerm

def weightMass (Phi : ℝ → ℝ) : ℂ :=
  ∫ u in Set.Icc (1/2 : ℝ) (5/2), (Phi u : ℂ)

theorem weightMass_full (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    weightMass Phi = (fullMass Phi:ℂ) := by
  rw [weightMass, fullMass_eq hPhi, integral_complex_ofReal]

theorem mass_uniform (Phi : ℝ → ℝ) :
    TendstoUniformlyOn (fun T (_ : ℂ × ℂ) => ExpandedGcd.mass Phi T/(T:ℂ))
      (fun _ => weightMass Phi) atTop witnessBidisc := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  intro p hp
  rw [ExpandedHeight.mass_rescale Phi T hT]
  simpa only [weightMass, dist_self] using heps

theorem height_uniform (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => ExpandedGcd.heightFactor Phi T ((p.1+p.2)/(Real.log T:ℂ))/(T:ℂ))
      (fun p => Complex.exp (-p.1-p.2)*weightMass Phi) atTop witnessBidisc := by
  have h := ExpandedHeight.heightFactor_uniform Phi hPhi (5*R/2)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro p hp
  have hb := witnessBidisc_subset hp
  have hs : ‖p.1+p.2‖ ≤ 5*R/2 := (norm_add_le _ _).trans (by linarith [hb.1,hb.2.1])
  simpa only [neg_add, sub_eq_add_neg, weightMass] using hT (p.1+p.2) hs

theorem height_limit_bounded (Phi : ℝ → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ witnessBidisc,
      ‖Complex.exp (-p.1-p.2)*weightMass Phi‖ ≤ M := by
  refine ⟨Real.exp (5*R/2)*‖weightMass Phi‖, by positivity, ?_⟩
  intro p hp
  have hb := witnessBidisc_subset hp
  have hs : ‖-p.1-p.2‖ ≤ 5*R/2 := by
    rw [sub_eq_add_neg, ← neg_add, norm_neg]
    exact (norm_add_le _ _).trans (by linarith [hb.1,hb.2.1])
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hs)) (norm_nonneg _)




theorem normalized_gcd_uniform_of_arithmetic (P Q : PRZZ.Profiles) (H : ℂ → ℂ → ℂ)
    (ha : TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic P Q PRZZAsymptotic.theta T p.1 p.2)
      (fun p => H p.1 p.2) atTop ElementaryGcd.twoBidiscs)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs, ‖H p.1 p.2‖ ≤ M)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm P Q PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => dualFunctional H p.1 p.2 * weightMass Phi) atTop witnessBidisc := by
  obtain ⟨M,hM,hMb⟩ := hb
  obtain ⟨Z,hZ,hZb⟩ := reciprocal_bounded
  have hdirect := uniform_mul_bounded ZetaPoleScaling.direct_pole_on_bidisc
    (ha.mono (fun _ hp => Or.inl hp))
    ⟨Z,hZ,hZb⟩ ⟨M,hM,fun p hp => hMb p (Or.inl hp)⟩
  have hdual := uniform_mul_bounded ZetaPoleScaling.dual_pole_on_bidisc
    (ElementaryGcd.uniform_reflected ha)
    ⟨Z,hZ,fun p hp => by simpa only [norm_neg] using hZb p hp⟩
    ⟨M,hM,fun p hp => hMb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)⟩
  have hdirect' := uniform_mul_bounded hdirect (mass_uniform Phi)
    ⟨Z*M,mul_nonneg hZ hM,fun p hp => by
      rw [norm_mul]; exact mul_le_mul (hZb p hp) (hMb p (Or.inl hp)) (norm_nonneg _) hZ⟩
    ⟨‖weightMass Phi‖,norm_nonneg _,fun _ _ => le_rfl⟩
  have hdual' := uniform_mul_bounded hdual (height_uniform Phi hPhi)
    ⟨Z*M,mul_nonneg hZ hM,fun p hp => by
      rw [norm_mul,norm_neg]
      exact mul_le_mul (hZb p hp)
        (hMb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)) (norm_nonneg _) hZ⟩
    (height_limit_bounded Phi)
  have hsum := hdirect'.add hdual'
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hsum eps heps,
    eventually_gt_atTop (1:ℝ)] with T hh hT
  intro p hp
  have h := hh p hp
  simp only [Pi.add_apply] at h
  rw [ExpandedGcd.normalized_gcd_split P Q PRZZAsymptotic.theta T Phi hPhi hT]
  convert h using 1
  congr 1
  unfold dualFunctional ElementaryGcd.reflect
  ring

theorem kernel_bounded (P Q : PRZZ.Profiles) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖TwoPieceMainTerm.kernel P Q p.1 p.2‖ ≤ M := by
  obtain ⟨a,ha,ha'⟩ := H00_bounded (complexify P.conrey) (complexify Q.conrey)
  obtain ⟨b,hb,hb'⟩ := H02_bounded (complexify P.conrey) (complexify Q.feng)
  obtain ⟨c,hc,hc'⟩ := H20_bounded (complexify P.feng) (complexify Q.conrey)
  obtain ⟨d,hd,hd'⟩ := FengSquareMainTerm.H22_bounded (complexify P.feng) (complexify Q.feng)
  refine ⟨a+b+c+d,by positivity,?_⟩
  intro p hp
  unfold TwoPieceMainTerm.kernel
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (ha' p hp) (hb' p hp))) (hc' p hp))) (hd' p hp))

theorem normalized_gcd_uniform (P Q : PRZZ.Profiles)
    (hPc : P.conrey.eval 0 = 0) (hPf : P.feng.eval 0 = 0)
    (hQc : Q.conrey.eval 0 = 0) (hQf : Q.feng.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm P Q PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => TwoPieceMainTerm.functional P Q p.1 p.2 * (fullMass Phi:ℂ))
      atTop witnessBidisc := by
  simpa only [TwoPieceMainTerm.functional,weightMass_full Phi hPhi] using
    normalized_gcd_uniform_of_arithmetic P Q (TwoPieceMainTerm.kernel P Q)
      (TwoPieceMainTerm.scaledArithmetic_twoBidiscs P Q hPc hPf hQc hQf)
      (kernel_bounded P Q) Phi hPhi

theorem normalized_witness_uniform (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn (normalizedGcd Phi)
      (fun p => BetaKernel.shiftedFunctional p.1 p.2 PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng) * (fullMass Phi:ℂ))
      atTop witnessBidisc :=
  normalized_gcd_uniform PRZZ.witness PRZZ.witness PRZZ.witness_endpoints.1
    PRZZ.witness_endpoints.2.1 PRZZ.witness_endpoints.1 PRZZ.witness_endpoints.2.1 Phi hPhi

theorem normalizedMoment_uniform (hlocal : LocalizedEstimate) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn (normalizedMoment Phi)
      (fun p => BetaKernel.shiftedFunctional p.1 p.2 PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng) * (fullMass Phi:ℂ))
      atTop witnessBidisc :=
  PRZZLocalizedError.moment_uniform_limit_of_gcd_limit hlocal (1/2) (5/2)
    (by norm_num) (by norm_num) Phi hPhi _ (normalized_witness_uniform Phi hPhi)

#print axioms weightMass_full
#print axioms normalized_gcd_uniform_of_arithmetic
#print axioms normalized_gcd_uniform
#print axioms normalized_witness_uniform
#print axioms normalizedMoment_uniform
end XiPrime8845.ExpandedMainTerm

