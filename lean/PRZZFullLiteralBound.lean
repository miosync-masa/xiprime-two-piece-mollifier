import PRZZLiteralTotalBound
import PRZZLiteralFourierLimit

/-! Transfer the sharp total literal error budget through the PROVED
Fourier exhaustion. Both L and J are removed in this order. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZFullLiteralBound
open PRZZMellinSeparation PRZZLiteralTotalBound
set_option maxHeartbeats 8000000

def fullError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (js : List ℕ)
    (N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
  PRZZLiteralFourierLimit.fullModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
    (Nat.log 2 N+2) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

theorem full_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Tendsto (fun J : ℕ => PRZZLiteralExhaustion.limitModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
        (Nat.log 2 N+2) J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) atTop
        (𝓝 (PRZZLiteralFourierLimit.fullModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
          (Nat.log 2 N+2) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))) ∧
      ‖fullError P Phi js N T eps A B‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZLiteralTotalBound.limit_total_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro N A B hN hscale hA hB hsep
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  have hfull := PRZZLiteralFourierLimit.model_tendsto F F Phi (Nat.log 2 N+2) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) hP hFl hFr hPhi.continuous hsPhi T eps hT0
    _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs
  refine ⟨hfull,?_⟩
  have hnorm : Tendsto (fun J : ℕ => ‖limitError P Phi js J N T eps A B‖) atTop
      (𝓝 ‖fullError P Phi js N T eps A B‖) :=
    (tendsto_const_nhds.sub hfull).norm
  by_contra hb
  have hb' : C*T^delta*PRZZOptimalPowers.target N T < ‖fullError P Phi js N T eps A B‖ :=
    lt_of_not_ge hb
  have hbad := hnorm.eventually (eventually_gt_nhds hb')
  obtain ⟨J,hJ,hbadJ⟩ := ((eventually_ge_atTop (PRZZCompatibleTail.commonCutoff N T eH)).and hbad).exists
  exact (not_lt_of_ge (h N J A B hN hscale hJ hA hB hsep).2) hbadJ

#print axioms full_total_bound
end XiPrime8845.PRZZFullLiteralBound

