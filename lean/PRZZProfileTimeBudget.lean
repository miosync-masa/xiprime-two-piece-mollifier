import PRZZFrozenProfileBound
import PRZZZeroPhaseBudget

/-! A common time-window derivative mass and cutoff absorption with the
local v/M cost retained. Source scale inequalities remain explicit. -/
noncomputable section
namespace XiPrime8845.PRZZProfileTimeBudget
open PRZZJetUniform PRZZZeroPhaseBudget
set_option maxHeartbeats 3000000

/-- Checking the lower spatial scale at t=2T supplies it throughout the
actual time window. The radius is the endpoint reciprocal-phase radius. -/
theorem time_scales (T M u v delta rho : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < u) (hv : 0 < v)
    (hscale : T^(-rho) ≤ (2*Real.pi*u/((2*T)*v))*(M/2)^2)
    (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) :
    T^(-rho) ≤ (2*Real.pi*u/(t*v))*(M/2)^2 ∧
    ∀ x ∈ Set.Icc (M/2) (3*M), |(delta*t/u)/x| ≤ |delta| * (2*T)/u/(M/2) := by
  have ht0 : 0 < t := hT.trans_le ht.1
  constructor
  · apply hscale.trans
    gcongr
    exact ht.2
  · intro x hx
    have hx0 : 0 < x := (by positivity : 0 < M/2).trans_le hx.1
    rw [abs_div,abs_div,abs_mul,abs_of_pos ht0,abs_of_pos hu,abs_of_pos hx0]
    gcongr
    · exact ht.2
    · exact hx.1

/-- Explicit U for the derivative L1 mass, uniform for every t in [T,2T].
No compactness constant depending invisibly on T is used. -/
theorem time_mass (C D E : ℕ → ℝ) (a Z P r rho T M u v R : ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hr : 0 < r) (hT : 1 ≤ T)
    (hM : 0 < M) (hu : 0 < u) (hv : 0 < v) (hR : 0 ≤ R)
    (hscale : T^(-rho) ≤ (2*Real.pi*u/((2*T)*v))*(M/2)^2)
    (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) :
    (3*M-M/2)*(uniformCap C D E a (2*Real.pi*u/(t*v)) M R Z P
      ((Real.log T)^2/r^2) n/(M/2)^n) ≤
    (3*M-M/2)*((base C D E Z P n*(1+1/r^2))*T^(rho*a+2)*(1+R)^n/(M/2)^n) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ht0 : 0 < t := hT0.trans_le ht.1
  have hk : 0 < 2*Real.pi*u/(t*v) := by positivity
  have hs := (time_scales T M u v 0 rho hT0 hM hu hv hscale t ht).1
  have hz := zero_cap_power C D E a _ M Z P r rho T n hc ha hk hZ hr hT hs
  have hg := PRZZPhaseDegree.cap_phase_growth C D E a _ M R Z P _ n
    hc hk.le hR hZ (by positivity : 0 ≤ (Real.log T)^2/r^2)
  have hb := hg.trans (mul_le_mul_of_nonneg_right hz (by positivity))
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity)) (by linarith)

/-- Absorb the additional local row cost V/M by spending nu in the order
selection. The cutoff is ceil(q*T^eH/M); q is the transformed modulus.
The derivative order is chosen before T and all row data. -/
theorem local_absorbed (C D E : ℕ → ℝ) (a Z P r rho mu nu eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ T M q V k : ℝ,
      1 ≤ T → 0 < M → 0 < q → 0 ≤ V → 0 < k →
      T^(-rho) ≤ k*(M/2)^2 → q/M ≤ T^mu → V/M ≤ T^nu →
      let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M q eH⌉₊
      (V/M)*(uniformCap C D E a k M 0 Z P ((Real.log T)^2/r^2) (n+2)*
        (1+8*T^eD)^2*(q/M)*((1+8*T^eD)*q/(M*((H:ℝ)+1)))^n) ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := absorbed C D E a Z P r rho mu eD eH (A+nu) hc ha hZ hr heD he
  refine ⟨n,K,hK,?_⟩
  intro T M q V k hT hM hq hV hk hscale hqm hvm
  dsimp only
  let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M q eH⌉₊
  have hh : PRZZSourceCutoffs.poissonCutoff 1 T M q eH ≤ (H:ℝ)+1 :=
    (Nat.le_ceil _).trans (by linarith)
  have hb := h 1 T M q q ((H:ℝ)+1) k (by norm_num) hT hM hq hq.le
    (by linarith) hk hh hscale hqm
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc
    _ ≤ (V/M)*(K*T^(-(A+nu))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ T^nu*(K*T^(-(A+nu))) := mul_le_mul_of_nonneg_right hvm (by positivity)
    _ = K*T^(-A) := by
      rw [show T^nu*(K*T^(-(A+nu))) = K*(T^nu*T^(-(A+nu))) by ring,
        ← Real.rpow_add hT0]
      congr 2
      ring

/-- The complete derivative mass in the Fourier tail, not just its
zero-phase factor, has arbitrary fixed power decay after order selection. -/
theorem full_tail_absorbed (C D E : ℕ → ℝ) (a Z P r rho mu nu eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ T M q V k : ℝ,
      1 ≤ T → 0 < M → 0 < q → 0 ≤ V → 0 < k →
      T^(-rho) ≤ k*(M/2)^2 → q/M ≤ T^mu → V/M ≤ T^nu →
      let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M q eH⌉₊
      let B := (3*M-M/2)*(uniformCap C D E a k M (8*T^eD) Z P
        ((Real.log T)^2/r^2) (n+2)/(M/2)^(n+2))
      (V/M)*(2*B*q^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*
        PRZZWeightTail.squareMass) ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := local_absorbed C D E a Z P r rho mu nu eD eH A hc ha hZ hr heD he
  let L := (5*2^(n+2)/(2*Real.pi)^(n+2))*PRZZWeightTail.squareMass
  have hmass : 0 ≤ PRZZWeightTail.squareMass := by unfold PRZZWeightTail.squareMass; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨n,L*K+1,by positivity,?_⟩
  intro T M q V k hT hM hq hV hk hscale hqm hvm
  dsimp only
  let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M q eH⌉₊
  let B0 := uniformCap C D E a k M 0 Z P ((Real.log T)^2/r^2) (n+2)
  have hg := PRZZPhaseDegree.cap_phase_growth C D E a k M (8*T^eD) Z P
    ((Real.log T)^2/r^2) (n+2) hc hk.le (by positivity) hZ (by positivity)
  have hh := h T M q V k hT hM hq hV hk hscale hqm hvm
  have hb : (V/M)*(2*((3*M-M/2)*(uniformCap C D E a k M (8*T^eD) Z P
      ((Real.log T)^2/r^2) (n+2)/(M/2)^(n+2)))*q^(n+1)/
      ((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass) ≤
      L*((V/M)*(B0*(1+8*T^eD)^2*(q/M)*
        ((1+8*T^eD)*q/(M*((H:ℝ)+1)))^n)) := by
    calc
      _ ≤ (V/M)*(2*((3*M-M/2)*(B0*(1+8*T^eD)^(n+2)/(M/2)^(n+2)))*q^(n+1)/
        ((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass) := by
          gcongr
          · linarith
      _ = _ := by
        rw [PRZZPhaseDegree.normalized_shape B0 M q (8*T^eD) n H hM]
        dsimp only [L]
        ring
  apply hb.trans
  have hh' := mul_le_mul_of_nonneg_left hh hL
  have hz : 0 ≤ T^(-A) := by positivity
  dsimp only [B0,H] at *
  nlinarith only [hh',hz]

#print axioms full_tail_absorbed
#print axioms time_scales
#print axioms time_mass
#print axioms local_absorbed
end XiPrime8845.PRZZProfileTimeBudget
