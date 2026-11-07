import PRZZPhaseDegree

/-! Zero-phase cap with an order-independent height exponent. Constants
depend on the derivative order, not on the scale or the height. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZZeroPhaseBudget
open PRZZFullWeightJets PRZZEnvelopeMass
set_option maxHeartbeats 2000000

def base (C D E : ℕ → ℝ) (Z P : ℝ) (n : ℕ) : ℝ :=
  convolution (convolution (convolution C (fun i => (Z+i)^i*Real.exp P))
    (fun i => PRZZReciprocalJets.envelope i 1)) (fun i => D i+E i) n

theorem base_nonneg (C D E : ℕ → ℝ) (Z P : ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (hZ : 0 ≤ Z) :
    0 ≤ base C D E Z P n := by
  apply convolution_nonneg
  · apply convolution_nonneg
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i 1 (by norm_num)
  · intro i; obtain ⟨hd,he⟩ := (hc i).2; positivity

theorem zero_cap (C D E : ℕ → ℝ) (a k M Z P s : ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (hk : 0 ≤ k)
    (hZ : 0 ≤ Z) (hs : 0 ≤ s) :
    PRZZJetUniform.uniformCap C D E a k M 0 Z P s n ≤
      base C D E Z P n*((1+s)*(k*(M/2)^2)^(-a)) := by
  let A := convolution (convolution C (fun i => (Z+i)^i*Real.exp P))
    (fun i => PRZZReciprocalJets.envelope i 1)
  have hA : ∀ i, 0 ≤ A i := by
    intro i
    apply convolution_nonneg
    · exact convolution_nonneg _ _ (fun j => (hc j).1) (fun j => by positivity)
    · exact fun j => PRZZReciprocalJets.envelope_nonneg j 1 (by norm_num)
  unfold PRZZJetUniform.uniformCap base
  simp only [add_zero, one_pow, mul_one]
  change convolution A (fun i => (D i+E i*s)*(k*(M/2)^2)^(-a)) n ≤
    convolution A (fun i => D i+E i) n*((1+s)*(k*(M/2)^2)^(-a))
  unfold convolution
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hd := (hc (n-i)).2.1
  have he := (hc (n-i)).2.2
  have hh : D (n-i)+E (n-i)*s ≤ (D (n-i)+E (n-i))*(1+s) := by nlinarith
  calc
    _ ≤ ((n.choose i:ℝ)*A i)*((D (n-i)+E (n-i))*(1+s)*(k*(M/2)^2)^(-a)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (by positivity))
        (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = _ := by ring

theorem zero_cap_power (C D E : ℕ → ℝ) (a k M Z P r rho T : ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hk : 0 < k) (hZ : 0 ≤ Z) (hr : 0 < r) (hT : 1 ≤ T)
    (hscale : T^(-rho) ≤ k*(M/2)^2) :
    PRZZJetUniform.uniformCap C D E a k M 0 Z P ((Real.log T)^2/r^2) n ≤
      (base C D E Z P n*(1+1/r^2))*T^(rho*a+2) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hb := base_nonneg C D E Z P n hc hZ
  have hlog0 := Real.log_nonneg hT
  have hlog : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
  have hs : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*T^2 := by
    have hsq := sq_le_sq₀ hlog0 hT0.le |>.mpr hlog
    have hh := div_le_div_of_nonneg_right hsq (sq_nonneg r)
    have h1 : 1 ≤ T^2 := one_le_pow₀ hT
    calc
      _ ≤ T^2+T^2/r^2 := add_le_add h1 hh
      _ = _ := by ring
  have hkpow : (k*(M/2)^2)^(-a) ≤ T^(rho*a) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 (-rho)) hscale (by linarith : -a ≤ 0)
    rw [← Real.rpow_mul hT0.le,neg_mul_neg] at hh
    exact hh
  apply (zero_cap C D E a k M Z P _ n hc hk.le hZ (by positivity)).trans
  calc
    _ ≤ base C D E Z P n*(((1+1/r^2)*T^2)*T^(rho*a)) := by gcongr
    _ = _ := by rw [Real.rpow_add hT0,Real.rpow_ofNat]; ring

/-- Substitution into the existing cutoff absorption, with the actual
zero-phase cap, rather than an assumed polynomial bound on it. -/
theorem absorbed (C D E : ℕ → ℝ) (a Z P r rho mu eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ d T M Q q h k : ℝ,
      0 < d → 1 ≤ T → 0 < M → 0 < Q → 0 ≤ q → q ≤ 3*Q/d → 0 < k →
      PRZZSourceCutoffs.poissonCutoff d T M Q eH ≤ h →
      T^(-rho) ≤ k*(M/2)^2 → q/M ≤ T^mu →
      PRZZJetUniform.uniformCap C D E a k M 0 Z P ((Real.log T)^2/r^2) (n+2)*
        (1+8*T^eD)^2*(q/M)*((1+8*T^eD)*q/(M*h))^n ≤ K*T^(-A) := by
  obtain ⟨n,hn⟩ := PRZZPhaseDegree.cutoff_absorbed eD eH (rho*a+2+2*eD+mu) A heD he
  let K := 81*(base C D E Z P (n+2)*(1+1/r^2))
  have hK : 0 ≤ K := by
    have := base_nonneg C D E Z P (n+2) hc hZ
    dsimp [K]; positivity
  refine ⟨n,K*27^n+1,by positivity,?_⟩
  intro d T M Q q h k hd hT hM hQ hq hbox hk hh hscale hqm
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hh0 : 0 < h := lt_of_lt_of_le (by unfold PRZZSourceCutoffs.poissonCutoff; positivity) hh
  have hc0 := zero_cap_power C D E a k M Z P r rho T (n+2) hc ha hk hZ hr hT hscale
  have hb := base_nonneg C D E Z P (n+2) hc hZ
  have hp : 1 ≤ T^eD := Real.one_le_rpow hT heD
  have hphase : (1+8*T^eD)^2 ≤ 81*T^(2*eD) := by
    calc
      _ ≤ (9*T^eD)^2 := by gcongr; linarith
      _ = _ := by
        rw [mul_pow,← Real.rpow_natCast (T^eD) 2,← Real.rpow_mul hT0.le]
        norm_num; rw [mul_comm eD 2]
  have hpre : PRZZJetUniform.uniformCap C D E a k M 0 Z P ((Real.log T)^2/r^2) (n+2)*
      (1+8*T^eD)^2*(q/M) ≤ K*T^(rho*a+2+2*eD+mu) := by
    calc
      _ ≤ ((base C D E Z P (n+2)*(1+1/r^2))*T^(rho*a+2))*
          (81*T^(2*eD))*T^mu := by gcongr
      _ = _ := by dsimp [K]; simp only [Real.rpow_add hT0]; ring
  have hgain := hn d T M Q q h hd hT hM hQ hq hbox hh
  have h1 := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ ((1+8*T^eD)*q/(M*h))^n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hgain hK
  have hz : 0 ≤ T^(-A) := by positivity
  nlinarith [h1,h2]

#print axioms absorbed
#print axioms base_nonneg
#print axioms zero_cap
#print axioms zero_cap_power
end XiPrime8845.PRZZZeroPhaseBudget
