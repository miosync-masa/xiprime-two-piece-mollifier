import PRZZPrunedTailRows

/-! The normalized absolute Fourier tail of the actual smooth weight.
Constants precede all source scales and times. This does not identify
an arbitrary finite row family with the original Poisson decomposition. -/
noncomputable section
open scoped ContDiff FourierTransform
open Set
namespace XiPrime8845.PRZZAbsorbedFourierTail
set_option maxHeartbeats 3000000

theorem normalized_cap (C D E : ℕ → ℝ) (a k M R Z P s q : ℝ) (n H : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (hk : 0 ≤ k)
    (hM : 0 < M) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs : 0 ≤ s) (hq : 0 ≤ q) :
    2*((3*M-M/2)*(PRZZJetUniform.uniformCap C D E a k M R Z P s (n+2)/(M/2)^(n+2)))*
      q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n) ≤
    (5*2^(n+2)/(2*Real.pi)^(n+2))*
      (PRZZJetUniform.uniformCap C D E a k M 0 Z P s (n+2)*(1+R)^2*(q/M)*
        ((1+R)*q/(M*((H:ℝ)+1)))^n) := by
  have hh := PRZZPhaseDegree.cap_phase_growth C D E a k M R Z P s (n+2) hc hk hR hZ hs
  calc
    _ ≤ 2*((3*M-M/2)*(PRZZJetUniform.uniformCap C D E a k M 0 Z P s (n+2)*
        (1+R)^(n+2)/(M/2)^(n+2)))*q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n) := by
      gcongr <;> linarith
    _ = _ := (PRZZPhaseDegree.normalized_shape _ M q R n H hM).trans (by ring)

theorem source_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ (H : ℕ) (d T M Q1 Q2 q u t delta : ℝ)
      (alpha beta : ℂ),
      0 < d → 36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < Q1 → 0 < Q2 → 0 < q → q ≤ T → q ≤ 3*Q2/d → 1 ≤ u →
      Q1/2 ≤ d*u → 0 < t → t ≤ 2*T →
      |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      PRZZSourceCutoffs.poissonCutoff d T M Q2 eH ≤ (H:ℝ)+1 →
      let f := PRZZFullWeightSmooth.weight F M (2*Real.pi*u/(t*q)) (delta*t/u)
        (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
      Summable tail ∧ (∑' j, q⁻¹*tail j) ≤ K*T^(-A) := by
  obtain ⟨C,D,E,hc,htail⟩ := PRZZNormalizedTail.uniform_tail F hF hsF a ha
  obtain ⟨n,K,hK,habs⟩ := PRZZZeroPhaseBudget.absorbed C D E a S
    (S*(2*b+Real.log 2+3*Real.log 3)) r 4 2 eD eH A hc ha.le hS hr heD he
  let J : ℝ := 5*2^(n+2)/(2*Real.pi)^(n+2)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hmass : 0 ≤ PRZZWeightTail.squareMass := tsum_nonneg (fun j => by positivity)
  refine ⟨n,J*K*PRZZWeightTail.squareMass+1,by positivity,?_⟩
  intro H d T M Q1 Q2 q u t delta alpha beta hd hT hlog hM hMT hQ1 hQ2 hq hqT hbox
    hu hleft ht ht2 hdelta halpha hsep hcut
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  have hL : Real.log T ≠ 0 := by linarith
  have hsum : alpha+beta ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hsigma : (alpha+beta)/(Real.log T:ℂ) ≠ 0 :=
    div_ne_zero hsum (by exact_mod_cast hL)
  have hk : 0 < 2*Real.pi*u/(t*q) := by positivity
  obtain ⟨hz,hP,hs⟩ := PRZZExtendedTailDomain.shift_envelopes T M b S r alpha beta
    hlog hM hMT hb hT0 halpha hr hsep
  have hh := htail n H M (2*Real.pi*u/(t*q)) (delta*t/u) (8*T^eD) q S
    (S*(2*b+Real.log 2+3*Real.log 3)) ((Real.log T)^2/r^2)
    (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    hM0 hk (by positivity) hq hsigma hS hz hP hs (by
      intro x hx
      exact PRZZSourceTailBudget.phase_radius T M Q1 d eD delta u t x hT0 hM0 hQ1 hd
        hx.1 hleft (by simpa [abs_of_pos ht] using ht2) hdelta)
  refine ⟨hh.1,?_⟩
  have hnorm := normalized_cap C D E a (2*Real.pi*u/(t*q)) M (8*T^eD) S
    (S*(2*b+Real.log 2+3*Real.log 3)) ((Real.log T)^2/r^2) q n H hc hk.le
    hM0 (by positivity) hS (by positivity) hq.le
  have hsc := PRZZExtendedTailDomain.scales T M u q t q hT hM hu hq hqT ht ht2 hq.le hqT
  have habs' := habs d T M Q2 q ((H:ℝ)+1) (2*Real.pi*u/(t*q)) hd (by linarith)
    hM0 hQ2 hq.le hbox hk hcut hsc.1 hsc.2
  have h1 := mul_le_mul_of_nonneg_right hnorm hmass
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs' hJ) hmass
  have hp : 0 ≤ T^(-A) := by positivity
  apply hh.2.trans (h1.trans _)
  dsimp only [J] at h2
  nlinarith only [h2,hp]

#print axioms normalized_cap
#print axioms source_tail
end XiPrime8845.PRZZAbsorbedFourierTail
