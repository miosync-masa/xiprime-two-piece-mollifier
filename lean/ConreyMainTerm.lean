import ConreyCoefficientBridge
import ZetaPoleScaling
import HeightScaling

/-! Uniform limit of the ORIGINAL normalized pure-Conrey gcd main term.
The arithmetic limit is used on both reflected bidiscs. No PRZZ axiom,
Feng asymptotic, moment identification or zero-counting theorem is used. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.ConreyMainTerm
open PRZZAsymptotic GcdDecomposition ConreyCoefficientBridge
set_option maxHeartbeats 1000000

/-- Multiplication is safe for uniform limits with bounded limiting factors. -/
theorem uniform_mul_bounded {ι : Type*} {s : Set ι}
    {f g : ℝ → ι → ℂ} {f₀ g₀ : ι → ℂ}
    (hf : TendstoUniformlyOn f f₀ atTop s) (hg : TendstoUniformlyOn g g₀ atTop s)
    (hf₀ : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ s, ‖f₀ p‖ ≤ M)
    (hg₀ : ∃ N : ℝ, 0 ≤ N ∧ ∀ p ∈ s, ‖g₀ p‖ ≤ N) :
    TendstoUniformlyOn (fun T p => f T p * g T p) (fun p => f₀ p * g₀ p) atTop s := by
  obtain ⟨M,hM,hMf⟩ := hf₀
  obtain ⟨N,hN,hNg⟩ := hg₀
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  let d := eps / (2*(M+N+1))
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf d hd,
    Metric.tendstoUniformlyOn_iff.mp hg d hd,
    Metric.tendstoUniformlyOn_iff.mp hg 1 (by norm_num)] with T hF hG hG1
  intro p hp
  have heF := hF p hp
  have heG := hG p hp
  have heG1 := hG1 p hp
  rw [dist_comm,dist_eq_norm] at heF heG heG1 ⊢
  have hgt : ‖g T p‖ ≤ N+1 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (g T p) (g₀ p) 0
    simp only [sub_zero] at ht
    linarith [hNg p hp]
  calc
    _ = ‖(f T p-f₀ p)*g T p + f₀ p*(g T p-g₀ p)‖ := by congr 1; ring
    _ ≤ ‖f T p-f₀ p‖*‖g T p‖ + ‖f₀ p‖*‖g T p-g₀ p‖ := by
      simpa only [norm_mul] using norm_add_le ((f T p-f₀ p)*g T p) (f₀ p*(g T p-g₀ p))
    _ ≤ d*(N+1)+M*d := add_le_add
      (mul_le_mul heF.le hgt (norm_nonneg _) hd.le)
      (mul_le_mul (hMf p hp) heG.le (norm_nonneg _) hM)
    _ = eps/2 := by dsimp [d]; field_simp; ring
    _ < eps := by linarith

def weightMass (Phi : ℝ → ℝ) : ℂ := ∫ u in Set.Icc (1 : ℝ) 2, (Phi u : ℂ)

/-- Bilinear Conrey functional, with the swapped reflected shifts retained. -/
def functional (P Q : Polynomial ℝ) (A B : ℂ) : ℂ :=
  (BetaKernel.H 0 0 A B PRZZAsymptotic.theta (complexify P) (complexify Q) -
    Complex.exp (-A-B) * BetaKernel.H 0 0 (-B) (-A) PRZZAsymptotic.theta (complexify P) (complexify Q)) /
      (A+B)

theorem H00_bound (P Q : Polynomial ℂ) (A B : ℂ)
    (hA : ‖A‖ ≤ 5*R/4) (hB : ‖B‖ ≤ 5*R/4) :
    ‖BetaKernel.H 0 0 A B PRZZAsymptotic.theta P Q‖ ≤ PRZZAsymptotic.theta * OuterProfile.valueCap P Q PRZZAsymptotic.theta (5*R/4) PRZZAsymptotic.theta := by
  rw [← OuterProfile.integral_eq_H00]
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := PRZZAsymptotic.theta) (C := OuterProfile.valueCap P Q PRZZAsymptotic.theta (5*R/4) PRZZAsymptotic.theta)
    (fun u hu => OuterProfile.profile_bound PRZZAsymptotic.theta (5*R/4) PRZZAsymptotic.theta u P Q A B hθ hA hB
      (by rw [Set.uIoc_of_le hθ.le] at hu; exact ⟨hu.1.le, hu.2⟩))
  simpa only [sub_zero, abs_of_pos hθ, mul_comm] using hi

theorem H00_bounded (P Q : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P Q‖ ≤ M := by
  refine ⟨max 0 (PRZZAsymptotic.theta * OuterProfile.valueCap P Q PRZZAsymptotic.theta (5*R/4) PRZZAsymptotic.theta), le_max_left _ _, ?_⟩
  intro p hp
  have h := ShiftedMobius.twoBidiscs_norm p hp
  exact (H00_bound P Q p.1 p.2 h.1 h.2).trans (le_max_right _ _)

theorem reciprocal_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ witnessBidisc, ‖1/(p.1+p.2)‖ ≤ M := by
  refine ⟨1/(3*R/2), by have := radius_pos; positivity, ?_⟩
  intro p hp
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by have := radius_pos; positivity) (witnessBidisc_subset hp).2.2

theorem mass_uniform (Phi : ℝ → ℝ) :
    TendstoUniformlyOn (fun T (_ : ℂ × ℂ) => mass Phi T/(T:ℂ))
      (fun _ => weightMass Phi) atTop witnessBidisc := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  intro p hp
  rw [HeightScaling.mass_rescale Phi T hT]
  simpa only [weightMass, dist_self] using heps

theorem height_uniform (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => heightFactor Phi T ((p.1+p.2)/(Real.log T:ℂ))/(T:ℂ))
      (fun p => Complex.exp (-p.1-p.2)*weightMass Phi) atTop witnessBidisc := by
  have h := HeightScaling.heightFactor_uniform Phi hPhi (5*R/2)
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

/-- Literal gcd main term, not an assumed leading-pole evaluation.
No positivity or mass-one normalization is required of the fixed weight. -/
theorem normalized_gcdMainTerm_uniform (P Q : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm (profile P) (profile Q) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => functional P Q p.1 p.2 * weightMass Phi) atTop witnessBidisc := by
  obtain ⟨H,hH,hHb⟩ := H00_bounded (complexify P) (complexify Q)
  obtain ⟨Z,hZ,hZb⟩ := reciprocal_bounded
  have hdirect := uniform_mul_bounded ZetaPoleScaling.direct_pole_on_bidisc
    ((scaledArithmetic_twoBidiscs P Q hP hQ).mono (fun _ hp => Or.inl hp))
    ⟨Z,hZ,hZb⟩ ⟨H,hH,fun p hp => hHb p (Or.inl hp)⟩
  have hdual := uniform_mul_bounded ZetaPoleScaling.dual_pole_on_bidisc
    (scaledArithmetic_reflected P Q hP hQ)
    ⟨Z,hZ,fun p hp => by simpa only [norm_neg] using hZb p hp⟩
    ⟨H,hH,fun p hp => hHb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)⟩
  have hdirect' := uniform_mul_bounded hdirect (mass_uniform Phi)
    ⟨Z*H,mul_nonneg hZ hH,fun p hp => by
      rw [norm_mul]; exact mul_le_mul (hZb p hp) (hHb p (Or.inl hp)) (norm_nonneg _) hZ⟩
    ⟨‖weightMass Phi‖,norm_nonneg _,fun _ _ => le_rfl⟩
  have hdual' := uniform_mul_bounded hdual (height_uniform Phi hPhi)
    ⟨Z*H,mul_nonneg hZ hH,fun p hp => by
      rw [norm_mul,norm_neg]
      exact mul_le_mul (hZb p hp)
        (hHb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)) (norm_nonneg _) hZ⟩
    (height_limit_bounded Phi)
  have hsum := hdirect'.add hdual'
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hsum eps heps,
    eventually_gt_atTop (1:ℝ)] with T hT hT1
  intro p hp
  have hh := hT p hp
  simp only [Pi.add_apply] at hh
  rw [normalized_gcd_split (profile P) (profile Q) PRZZAsymptotic.theta T Phi hPhi hT1]
  convert hh using 1
  congr 1
  unfold functional
  ring

theorem normalized_gcdMainTerm_tendsto (P Q : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => PRZZ.gcdMainTerm (profile P) (profile Q) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      atTop (nhds (functional P Q p.1 p.2 * weightMass Phi)) :=
  (normalized_gcdMainTerm_uniform P Q hP hQ Phi hPhi).tendsto_at hp

#print axioms uniform_mul_bounded
#print axioms H00_bound
#print axioms H00_bounded
#print axioms reciprocal_bounded
#print axioms mass_uniform
#print axioms height_uniform
#print axioms height_limit_bounded
#print axioms normalized_gcdMainTerm_uniform
#print axioms normalized_gcdMainTerm_tendsto
end XiPrime8845.ConreyMainTerm
