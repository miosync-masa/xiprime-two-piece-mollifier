import PRZZActiveFreezeBudget
import PRZZDyadicBudget

/-! Optimize the concrete empty-row-pruned freezing budget. The first
surviving spatial scale is selected inside the given finite family;
no lower-bound hypothesis on its initial scale is requested. -/
noncomputable section
open scoped BigOperators
open Set
namespace XiPrime8845.PRZZFiniteFreezeBudget
open PRZZPrefactorMass PRZZFreezeScales PRZZActiveFreezeBudget
set_option maxHeartbeats 6000000

def live (N d j l : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ) : Prop :=
  (active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps)
    (PRZZSourceCutoffs.poissonCutoff d T M V eH) F1 F2).Nonempty

def rowCharge (N d j l : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ) : ℝ :=
  charge N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps)
    (PRZZSourceCutoffs.poissonCutoff d T M V eH) T M eps F1 F2

/-- The first nonempty scale, with the entire zero prefix removed before
geometric summation. Both the index and its actual support witness survive. -/
theorem first_live (N d j l K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 ≤ Q) (hV : 0 ≤ V) :
    (∑ k ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2) = 0 ∨
    ∃ k < K, live N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2 ∧
      (∀ i < k, ¬ live N d j l T ((2:ℝ)^i*M) Q V eps eH F1 F2) ∧
      (∑ i ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^i*M) Q V eps eH F1 F2) ≤
        (16/15:ℝ)*sourceCost T ((2:ℝ)^k*M) eps j l*
          (5*T^(eps+eH)*(Q*V/((d:ℝ)^2*T))/d) := by
  classical
  by_cases hex : ∃ k, k < K ∧ live N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2
  · let k := Nat.find hex
    have hk : k < K ∧ live N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2 := Nat.find_spec hex
    have hpre (i : ℕ) (hi : i < k) : ¬ live N d j l T ((2:ℝ)^i*M) Q V eps eH F1 F2 := by
      intro hh
      exact Nat.find_min hex hi ⟨lt_trans hi hk.1,hh⟩
    have hz : (∑ i ∈ Finset.range k, rowCharge N d j l T ((2:ℝ)^i*M) Q V eps eH F1 F2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hn := hpre i (Finset.mem_range.mp hi)
      unfold live at hn
      simp [rowCharge,charge,hn]
    have he : (∑ i ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^i*M) Q V eps eH F1 F2) =
        ∑ i ∈ Finset.range (K-k), rowCharge N d j l T ((2:ℝ)^i*((2:ℝ)^k*M)) Q V eps eH F1 F2 := by
      nth_rw 1 [show K = k+(K-k) by omega]
      rw [Finset.sum_range_add,hz,zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      rw [show (2:ℝ)^k*(2:ℝ)^i*M = (2:ℝ)^i*((2:ℝ)^k*M) by ring]
    refine Or.inr ⟨k,hk.1,hk.2,hpre,?_⟩
    rw [he]
    exact dyadic_charge_sum N d j l (K-k) T ((2:ℝ)^k*M) Q V eps eH F1 F2
      hd hT (by positivity) hQ hV
  · left
    apply Finset.sum_eq_zero
    intro k hk
    have hn : ¬ live N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2 :=
      fun hh => hex ⟨k,Finset.mem_range.mp hk,hh⟩
    unfold live at hn
    simp [rowCharge,charge,hn]

/-- Supply the active spatial lower bound and both cutoff-scale ratios
to the literal analytic cost. This is a bound on sourceCost itself. -/
theorem live_cost (N d j l : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (hlive : live N d j l T M Q V eps eH F1 F2) :
    sourceCost T M eps j l ≤
      331776*T^3*Q^2*V^2/((d:ℝ)^4*(T^(1-eps))^6) := by
  obtain ⟨z,hz⟩ := hlive
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 < T := by linarith
  let A := T^(1-eps)
  have hA : 0 < A := Real.rpow_pos_of_pos ht _
  have hAT : A ≤ T := by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hT (show 1-eps ≤ (1:ℝ) by linarith)
  have hlo := active_spatial_lower N d j l T M Q eps _ F1 F2 hd ht z hz
  have hlow : (d:ℝ)*A/Q ≤ M := (div_le_iff₀ hQ).mpr hlo.le
  have hf := active_floor N d j l _ _ M Q V F1 F2 hd hM hV hs1 hs2 z hz
  have hf' : ((d:ℝ)*A)^2/(48*V*Q) ≤ productFloor M j l := by
    calc
      _ = ((d:ℝ)*A/Q)^2*Q/(48*V) := by field_simp
      _ ≤ M^2*Q/(48*V) := by gcongr
      _ ≤ Real.pi*M^2*Q/(48*V) := by
        have hp : M^2 ≤ Real.pi*M^2 := le_mul_of_one_le_left (sq_nonneg M)
          (by linarith [Real.pi_gt_three])
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hQ.le) (by positivity)
      _ ≤ _ := hf
  let U := (ratioCap T eps+2*T*(ratioCap T eps)^2)*(2*T)^2
  have hU : 0 ≤ U := by dsimp [U,ratioCap]; positivity
  have hu : U ≤ 144*T^3/A^2 := by
    have h1 : 16*T^2*A ≤ 16*T^3 := by nlinarith [mul_le_mul_of_nonneg_left hAT (show 0 ≤ 16*T^2 by positivity)]
    dsimp [U,ratioCap]
    change (4/A+2*T*(4/A)^2)*(2*T)^2 ≤ _
    apply (le_div_iff₀ (by positivity : 0 < A^2)).mpr
    field_simp
    nlinarith
  have hb : sourceCost T M eps j l ≤ U/((((d:ℝ)*A)^2/(48*V*Q))^2) := by
    unfold sourceCost
    apply div_le_div_of_nonneg_left hU (by positivity)
    have hfpos : 0 ≤ ((d:ℝ)*A)^2/(48*V*Q) := by positivity
    nlinarith
  apply hb.trans
  calc
    _ ≤ (144*T^3/A^2)/((((d:ℝ)*A)^2/(48*V*Q))^2) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ = _ := by change _ = 331776*T^3*Q^2*V^2/((d:ℝ)^4*A^6); field_simp; ring

/-- The selected first live row pays the entire spatial family. No
initial-M restriction and no assumed per-row estimate are supplied. -/
theorem spatial_row_bound (N d j l K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V)) :
    (∑ k ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2) ≤
      1769472*T^2*Q^3*V^3*T^(eps+eH)/((d:ℝ)^7*(T^(1-eps))^6) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 < T := by linarith
  rcases first_live N d j l K T M Q V eps eH F1 F2 hd ht hM hQ.le hV.le with hz | ⟨k,hk,hl,hpre,hb⟩
  · rw [hz]; positivity
  · have hc := live_cost N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2 hd hT
      (by positivity) hQ hV heps hs1 hs2 hl
    apply hb.trans
    calc
      _ ≤ (16/15:ℝ)*(331776*T^3*Q^2*V^2/((d:ℝ)^4*(T^(1-eps))^6))*
          (5*T^(eps+eH)*(Q*V/((d:ℝ)^2*T))/d) := by gcongr
      _ = _ := by field_simp; ring

/-- Nonzero cutoff values bound their two original scales by 2N,
including the gcd dilation. Empty configurations need no scale premise. -/
theorem live_cutoff_caps (N d j l : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (hl : live N d j l T M Q V eps eH F1 F2) : Q ≤ 2*N ∧ V ≤ 2*N := by
  obtain ⟨z,hz⟩ := hl
  have h := Finset.mem_filter.mp hz
  have hp := (Finset.mem_filter.mp (Finset.mem_product.mp h.1).1).2
  have hu : (d:ℝ)*z.1.1 ≤ N := by exact_mod_cast hp.2.1
  have hv : (d:ℝ)*z.1.2 ≤ N := by exact_mod_cast hp.2.2
  have hq := (hs1 h.2.1).1
  have hv' := (hs2 h.2.2).1
  constructor <;> linarith

theorem spatial_row_N_bound (N d j l K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V)) :
    (∑ k ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2) ≤
      113246208*T^2*(N:ℝ)^6*T^(eps+eH)/((d:ℝ)^7*(T^(1-eps))^6) := by
  rcases first_live N d j l K T M Q V eps eH F1 F2 hd (by linarith) hM hQ.le hV.le
    with hz | ⟨k,hk,hl,hpre,hb⟩
  · rw [hz]; positivity
  · obtain ⟨hQN,hVN⟩ := live_cutoff_caps N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2 hs1 hs2 hl
    apply (spatial_row_bound N d j l K T M Q V eps eH F1 F2 hd hT hM hQ hV heps hs1 hs2).trans
    calc
      _ ≤ 1769472*T^2*(2*(N:ℝ))^3*(2*(N:ℝ))^3*T^(eps+eH)/
          ((d:ℝ)^7*(T^(1-eps))^6) := by gcongr
      _ = _ := by ring

/-- The gcd sum is genuinely summable; it is not replaced by N. -/
theorem divisor_seventh (N : ℕ) : (∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^7) ≤ 2 := by
  have hb (N : ℕ) : (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)^7) ≤ 2-2/((N:ℝ)+1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hd : 1 ≤ (N:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
      have hd0 : 0 < (N:ℝ)+1 := by positivity
      have hp : ((N:ℝ)+1)^2 ≤ ((N:ℝ)+1)^7 := pow_le_pow_right₀ hd (by omega)
      have ht : 1/((N:ℝ)+1)^7 ≤ 2/(((N:ℝ)+1)*((N:ℝ)+2)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      rw [Finset.sum_range_succ]
      calc
        _ ≤ (2-2/((N:ℝ)+1))+2/(((N:ℝ)+1)*((N:ℝ)+2)) := add_le_add ih ht
        _ = _ := by push_cast; field_simp; ring
  have he : (∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^7) =
      ∑ k ∈ Finset.range N, 1/((k:ℝ)+1)^7 := by
    apply Finset.sum_bij (fun d _ => d-1)
    · intro d hd; have := Finset.mem_Icc.mp hd; exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb h; have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
    · intro k hk; refine ⟨k+1,Finset.mem_Icc.mpr ⟨by omega,?_⟩,by omega⟩
      have := Finset.mem_range.mp hk; omega
    · intro d hd
      have hh : d-1+1=d := by have := Finset.mem_Icc.mp hd; omega
      have hr : ((d-1:ℕ):ℝ)+1 = d := by exact_mod_cast hh
      rw [hr]
  rw [he]
  apply (hb N).trans
  have hh : 0 ≤ 2/((N:ℝ)+1) := by positivity
  linarith

def budget (N K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1),
      ∑ k ∈ Finset.range K, rowCharge N d j l T ((2:ℝ)^k*M) Q V eps eH F1 F2

/-- All d,j,l and spatial scales in the concrete charge are now summed.
The starting M and the truncation K do not occur in the upper bound. -/
theorem budget_bound (N K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V) (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V)) :
    budget N K T M Q V eps eH F1 F2 ≤
      226492416*(Nat.log 2 N+1:ℝ)^2*T^2*(N:ℝ)^6*T^(eps+eH)/(T^(1-eps))^6 := by
  let B := 113246208*(Nat.log 2 N+1:ℝ)^2*T^2*(N:ℝ)^6*T^(eps+eH)/(T^(1-eps))^6
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
        ∑ l ∈ Finset.range (Nat.log 2 N+1),
          113246208*T^2*(N:ℝ)^6*T^(eps+eH)/((d:ℝ)^7*(T^(1-eps))^6) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro l hl
      exact spatial_row_N_bound N d j l K T M Q V eps eH F1 F2
        (by have := (Finset.mem_Icc.mp hd).1; omega) hT hM hQ hV heps hs1 hs2
    _ = B*(∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^7) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      dsimp [B]
      push_cast
      ring
    _ ≤ B*2 := mul_le_mul_of_nonneg_left (divisor_seventh N) hB
    _ = _ := by dsimp [B]; ring

/-- Include the length T of the time interval and audit the full loss
7*eps+eH. The optimized sixth-power term is now a proved budget bound. -/
theorem budget_time_power (N K : ℕ) (T M Q V eps eH : ℝ) (F1 F2 : ℝ → ℂ)
    (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V) (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V)) :
    T*budget N K T M Q V eps eH F1 F2 ≤
      226492416*(Nat.log 2 N+1:ℝ)^2*T^(7*eps+eH)*((N:ℝ)^6/T^3) := by
  have ht : 0 < T := by linarith
  have he : T*T^2*T^(eps+eH)/(T^(1-eps))^6 = T^(7*eps+eH)/T^3 := by
    rw [show T*T^2*T^(eps+eH) = T^3*T^(eps+eH) by ring]
    simp only [← Real.rpow_natCast,← Real.rpow_mul ht.le,
      ← Real.rpow_add ht,← Real.rpow_sub ht]
    congr 1
    norm_num
    ring
  calc
    _ ≤ T*(226492416*(Nat.log 2 N+1:ℝ)^2*T^2*(N:ℝ)^6*T^(eps+eH)/(T^(1-eps))^6) :=
      mul_le_mul_of_nonneg_left (budget_bound N K T M Q V eps eH F1 F2 hT hM hQ hV heps hs1 hs2) ht.le
    _ = (226492416*(Nat.log 2 N+1:ℝ)^2*(N:ℝ)^6)*
        (T*T^2*T^(eps+eH)/(T^(1-eps))^6) := by ring
    _ = _ := by rw [he]; ring

/-- Coefficient logarithms, two dyadic grids and the actual quadratic
shift singularity fit in the declared height slack, uniformly in K,M,Q,V. -/
theorem budget_absorbed (m : ℕ) (eps eH r delta : ℝ) (heps : 0 ≤ eps) (hr : 0 < r)
    (hmargin : 7*eps+eH < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K : ℕ) (T M Q V : ℝ) (F1 F2 : ℝ → ℂ),
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V →
      Function.support F1 ⊆ Icc (Q/2) (3*Q) →
      Function.support F2 ⊆ Icc (V/2) (3*V) →
      (Real.log N)^m*(1+(Real.log T)^2/r^2)*T*budget N K T M Q V eps eH F1 F2 ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨D,hD,hpow⟩ := PRZZOptimalOuter.power_log_absorbed (m+4) (7*eps+eH) delta hmargin
  let c := 1/Real.log 2+1
  have hc : 0 < c := by dsimp [c]; positivity
  let B := 226492416*c^2*(1+1/r^2)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B*D,by positivity,?_⟩
  intro N K T M Q V F1 F2 hN hT hL hscale hM hQ hV hs1 hs2
  have ht : 0 < T := by linarith
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hn
  have hlNT : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hg := PRZZDyadicBudget.cell_count N T hN hNT hL
  change (Nat.log 2 N+1:ℝ) ≤ c*Real.log T at hg
  have hshift : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*(Real.log T)^2 := by
    have hh : 1 ≤ (Real.log T)^2 := by nlinarith
    calc
      _ ≤ (Real.log T)^2+(Real.log T)^2/r^2 := add_le_add hh le_rfl
      _ = _ := by ring
  have hb := budget_time_power N K T M Q V eps eH F1 F2 hT hM hQ hV heps hs1 hs2
  have hlog : (Real.log N)^m*(1+(Real.log T)^2/r^2)*
      (226492416*(Nat.log 2 N+1:ℝ)^2*T^(7*eps+eH)*((N:ℝ)^6/T^3)) ≤
      B*(T^(7*eps+eH)*(Real.log T)^(m+4))*((N:ℝ)^6/T^3) := by
    calc
      _ ≤ (Real.log T)^m*((1+1/r^2)*(Real.log T)^2)*
          (226492416*(c*Real.log T)^2*T^(7*eps+eH)*((N:ℝ)^6/T^3)) := by gcongr
      _ = _ := by dsimp [B]; simp only [pow_add]; ring
  have h1 := (mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (Real.log N)^m*(1+(Real.log T)^2/r^2) by positivity)).trans hlog
  have h2 := mul_le_mul (hpow T hT)
    (sixth_power_target N T hn hT hscale) (by positivity) (by positivity)
  calc
    _ = (Real.log N)^m*(1+(Real.log T)^2/r^2)*(T*budget N K T M Q V eps eH F1 F2) := by ring
    _ ≤ B*(T^(7*eps+eH)*(Real.log T)^(m+4))*((N:ℝ)^6/T^3) := h1
    _ = B*((T^(7*eps+eH)*(Real.log T)^(m+4))*((N:ℝ)^6/T^3)) := by ring
    _ ≤ B*(D*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left h2 hB.le
    _ = _ := by ring

#print axioms first_live
#print axioms live_cost
#print axioms spatial_row_bound
#print axioms live_cutoff_caps
#print axioms spatial_row_N_bound
#print axioms divisor_seventh
#print axioms budget_bound
#print axioms budget_time_power
#print axioms budget_absorbed
end XiPrime8845.PRZZFiniteFreezeBudget
