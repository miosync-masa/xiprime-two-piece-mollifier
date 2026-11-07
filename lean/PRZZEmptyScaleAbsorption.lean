import PRZZEmptyArithmeticMass

/-! Remove the starting spatial scale from the phase-free arithmetic
charge by selecting its first nonempty literal cutoff row. This evaluates
the sourceCost-weighted coefficient mass; the extra analytic M^eta moment
is not silently identified with this charge. -/
noncomputable section
open scoped BigOperators
open Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZEmptyScaleAbsorption
open PRZZPrefactorMass PRZZActiveFreezeBudget PRZZFreezeScales PRZZEmptyArithmeticMass
set_option maxHeartbeats 6000000

theorem live_cost_gap (N d j l : ℕ) (T M Q V eps : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (heps : 0 ≤ eps)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (z : PRZZAStar.Index)
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2) :
    sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps ≤
      331776*T^3*Q^2*V^2/((d:ℝ)^3*(T^(1-eps))^6) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 < T := by linarith
  let A := T^(1-eps)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAT : A ≤ T := by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hT (show 1-eps ≤ (1:ℝ) by linarith)
  have hlo := active_spatial_lower N d j l T M Q eps 2 F1 F2 hd ht z hz
  have hlow : (d:ℝ)*A/Q ≤ M := (div_le_iff₀ hQ).mpr hlo.le
  have hf := active_floor N d j l _ 2 M Q V F1 F2 hd hM hV hs1 hs2 z hz
  have hf0 : M^2*Q/(48*V) ≤ productFloor M j l := by
    apply le_trans _ hf
    gcongr
    exact le_mul_of_one_le_left (sq_nonneg M) (by linarith [Real.pi_gt_three])
  let U := (ratioCap T eps+2*T*(ratioCap T eps)^2)*(2*T)^2
  have hU : 0 ≤ U := by dsimp [U,ratioCap]; positivity
  have hu : U ≤ 144*T^3/A^2 := by
    have h1 : 16*T^2*A ≤ 16*T^3 := by nlinarith [mul_le_mul_of_nonneg_left hAT (show 0 ≤ 16*T^2 by positivity)]
    dsimp [U,ratioCap]
    change (4/A+2*T*(4/A)^2)*(2*T)^2 ≤ _
    apply (le_div_iff₀ (by positivity : 0 < A^2)).mpr
    field_simp
    nlinarith
  have hb : sourceCost T M eps j l ≤ U/(M^2*Q/(48*V))^2 := by
    unfold sourceCost
    apply div_le_div_of_nonneg_left hU (by positivity)
    have hfpos : 0 ≤ M^2*Q/(48*V) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps by unfold PRZZSourceCutoffs.deltaCutoff; positivity)
  have he : U/(M^2*Q/(48*V))^2*PRZZSourceCutoffs.deltaCutoff T M Q eps =
      2304*U*V^2/(M^3*Q*A) := by
    change _*(M*Q/A) = _
    field_simp
    ring
  rw [he] at hh
  apply hh.trans
  calc
    _ ≤ 2304*(144*T^3/A^2)*V^2/(((d:ℝ)*A/Q)^3*Q*A) := by gcongr
    _ = _ := by change _ = 331776*T^3*Q^2*V^2/((d:ℝ)^3*A^6); field_simp; ring

/-- The selected first nonempty row removes the zero prefix before the
coefficient-weighted geometric estimate is used. No initial M lower bound. -/
theorem first_scale_bound (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l K : ℕ) (T M Q V S eps : ℝ)
      (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ T → 0 < Real.log T →
      0 < M → 0 < Q → 0 < V → 0 ≤ S → 0 ≤ eps →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta) ≤
        C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*T^3*(N:ℝ)^4/(T^(1-eps))^6 := by
  classical
  obtain ⟨C,hC,h⟩ := coefficient_spatial F G hF hG hcF hcG
  refine ⟨C*331776*16,by positivity,?_⟩
  intro js N d j l K T M Q V S eps alpha beta hN hd hNT hT hL hM hQ hV hS heps ha hb
  let F1 := PRZZMellinSeparation.scaledCutoff F Q
  let F2 := PRZZMellinSeparation.scaledCutoff G V
  let row := fun i => sourceCost T ((2:ℝ)^i*M) eps j l*
    rowMass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*M) Q eps)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta
  let live := fun i => (active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*M) Q eps) 2 F1 F2).Nonempty
  have hz (i : ℕ) (hi : ¬live i) : row i = 0 := by
    dsimp [row]
    rw [row_mass_eq,mass,prune]
    have he := Finset.not_nonempty_iff_eq_empty.mp hi
    simp only [he,Finset.sum_empty,mul_zero]
  change (∑ i ∈ Finset.range K, row i) ≤ _
  by_cases hex : ∃ i, i < K ∧ live i
  · let k := Nat.find hex
    have hk : k < K ∧ live k := Nat.find_spec hex
    have hpre : (∑ i ∈ Finset.range k, row i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i (fun hh => Nat.find_min hex (Finset.mem_range.mp hi) ⟨lt_trans (Finset.mem_range.mp hi) hk.1,hh⟩)
    have he : (∑ i ∈ Finset.range K, row i) =
        ∑ i ∈ Finset.range (K-k), sourceCost T ((2:ℝ)^i*((2:ℝ)^k*M)) eps j l*
          rowMass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*((2:ℝ)^k*M)) Q eps)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta := by
      nth_rw 1 [show K = k+(K-k) by omega]
      rw [Finset.sum_range_add,hpre,zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [row]
      rw [pow_add,show (2:ℝ)^k*(2:ℝ)^i*M = (2:ℝ)^i*((2:ℝ)^k*M) by ring]
    obtain ⟨z,hz'⟩ := hk.2
    have hd0 : 0 < d := by omega
    have hs1 := scaled_support F Q hQ hsF
    have hs2 := scaled_support G V hV hsG
    have hc := live_cost_gap N d j l T ((2:ℝ)^k*M) Q V eps F1 F2 hd0 hT (by positivity) hQ hV heps hs1 hs2 z hz'
    have hcaps : Q ≤ 2*N ∧ V ≤ 2*N := by
      have hh := Finset.mem_filter.mp hz'
      have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hh.1).1).2
      have hu : (d:ℝ)*z.1.1 ≤ N := by exact_mod_cast hp.2.1
      have hv : (d:ℝ)*z.1.2 ≤ N := by exact_mod_cast hp.2.2
      constructor <;> linarith [(hs1 hh.2.1).1,(hs2 hh.2.2).1]
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hQc := hcaps.1
    have hVc := hcaps.2
    have hc' : sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps/(d:ℝ)^2 ≤
        (331776*16)*T^3*(N:ℝ)^4/(T^(1-eps))^6 := by
      calc
        _ ≤ (331776*T^3*Q^2*V^2/((d:ℝ)^3*(T^(1-eps))^6))/(d:ℝ)^2 := by gcongr
        _ ≤ (331776*T^3*(2*(N:ℝ))^2*(2*(N:ℝ))^2/(1^3*(T^(1-eps))^6))/1^2 := by gcongr
        _ = _ := by ring
    rw [he]
    have hh := h js N d j l (K-k) T ((2:ℝ)^k*M) Q V S eps alpha beta hN hd hNT (by linarith) hL (by positivity) hQ.le hS ha hb
    apply hh.trans
    have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hp := mul_le_mul_of_nonneg_left hc'
      (show 0 ≤ C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js) by positivity)
    convert hp using 1 <;> ring
  · rw [Finset.sum_eq_zero (fun i hi => hz i (fun hh => hex ⟨i,Finset.mem_range.mp hi,hh⟩))]
    positivity

/-- Every outer d,j,l sum is now evaluated. The K and initial M
dependence have disappeared, and no arithmetic coefficient is an input. -/
theorem outer_power (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N K : ℕ) (T M Q V S eps : ℝ) (alpha beta : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ T → 0 < Real.log T → 0 < M → 0 < Q → 0 < V →
      0 ≤ S → 0 ≤ eps → |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      T*outerMass js N K T M Q V eps F G alpha beta ≤
        C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
          (Nat.log 2 N+1:ℝ)^2*T^(6*eps)*((N:ℝ)^5/T^2) := by
  obtain ⟨C,hC,h⟩ := first_scale_bound F G hF hG hcF hcG hsF hsG
  refine ⟨C,hC,?_⟩
  intro js N K T M Q V S eps alpha beta hN hNT hT hL hM hQ hV hS heps ha hb
  have ht : 0 < T := by linarith
  have hm : outerMass js N K T M Q V eps F G alpha beta ≤
      C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
        (Nat.log 2 N+1:ℝ)^2*T^3*(N:ℝ)^5/(T^(1-eps))^6 := by
    unfold outerMass
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
          ∑ l ∈ Finset.range (Nat.log 2 N+1),
            C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*T^3*(N:ℝ)^4/(T^(1-eps))^6 := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro l hl
        exact h js N d j l K T M Q V S eps alpha beta hN (Finset.mem_Icc.mp hd).1 hNT hT hL hM hQ hV hS heps ha hb
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; push_cast; ring
  have he : T*T^3/(T^(1-eps))^6 = T^(6*eps)/T^2 := by
    rw [show T*T^3 = T^4 by ring]
    simp only [← Real.rpow_natCast,← Real.rpow_mul ht.le,← Real.rpow_sub ht]
    congr 1
    norm_num
    ring
  apply (mul_le_mul_of_nonneg_left hm ht.le).trans_eq
  calc
    _ = (C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*(Nat.log 2 N+1:ℝ)^2*(N:ℝ)^5)*
        (T*T^3/(T^(1-eps))^6) := by ring
    _ = _ := by rw [he]; ring

/-- Full native arithmetic charge of the h-free congruence rows fits
the target. This does not discard the separate spatial amplitude moment
v^(1+eta)(3M)^eta of the actual joint freezing error. -/
theorem outer_absorbed (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (hmargin : 6*eps < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K : ℕ) (T M Q V : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V → |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (1+(Real.log T)^2/r^2)*T*outerMass js N K T M Q V eps F G alpha beta ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := outer_power F G hF hG hcF hcG hsF hsG
  let m := 2*PRZZGCoefficient.degree js
  obtain ⟨D,hD,hpow⟩ := PRZZOptimalOuter.power_log_absorbed (m+4) (6*eps) delta hmargin
  let c := 1/Real.log 2+1
  have hc : 0 < c := by dsimp [c]; positivity
  let B := C*Real.exp (2*S)*c^2*(1+1/r^2)
  have hB : 0 < B := by dsimp [B,c]; positivity
  refine ⟨B*D,by positivity,?_⟩
  intro N K T M Q V alpha beta hN hT hL hscale hM hQ hV ha hb
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ht : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hn
  have hlNT : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hg := PRZZDyadicBudget.cell_count N T hN hNT hL
  change (Nat.log 2 N+1:ℝ) ≤ c*Real.log T at hg
  have hs : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*(Real.log T)^2 := by
    have hh : 1 ≤ (Real.log T)^2 := by nlinarith
    calc
      _ ≤ (Real.log T)^2+(Real.log T)^2/r^2 := add_le_add hh le_rfl
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left
    (h js N K T M Q V S eps alpha beta hN hNT hT (by linarith) hM hQ hV hS heps ha hb)
    (show 0 ≤ 1+(Real.log T)^2/r^2 by positivity)
  have hlog : (1+(Real.log T)^2/r^2)*
      (C*Real.exp (2*S)*(Real.log N)^m*(Nat.log 2 N+1:ℝ)^2*T^(6*eps)*((N:ℝ)^5/T^2)) ≤
      B*(T^(6*eps)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2) := by
    calc
      _ ≤ ((1+1/r^2)*(Real.log T)^2)*
          (C*Real.exp (2*S)*(Real.log T)^m*(c*Real.log T)^2*T^(6*eps)*((N:ℝ)^5/T^2)) := by gcongr
      _ = _ := by dsimp [B]; simp only [pow_add]; ring
  have hp := mul_le_mul (hpow T hT) (fifth_power_target N T hn hT hscale) (by positivity) (by positivity)
  calc
    _ = (1+(Real.log T)^2/r^2)*(T*outerMass js N K T M Q V eps F G alpha beta) := by ring
    _ ≤ B*(T^(6*eps)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2) := hh.trans hlog
    _ = B*((T^(6*eps)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2)) := by ring
    _ ≤ B*(D*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left hp hB.le
    _ = _ := by ring

/-- The native h-free arithmetic charge and the literal AFE replacement
defect share one target. This remains a budget inequality: the additional
analytic spatial moment of the full joint Poisson error is separate. -/
theorem replacement_and_empty_budget
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (hdelta : 0 < delta) (hmargin : 6*eps < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N K : ℕ,
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ∀ M Q V : ℝ,
      0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ +
      P*(1+(Real.log T)^2/r^2)*T*
        outerMass js N K T M Q V eps F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨Cr,hCr,hrb⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hdelta
  obtain ⟨Cw,hCw,hwb⟩ := outer_absorbed F G hF hG hcF hcG hsF hsG js S r eps delta hS hr heps hmargin
  refine ⟨Cr+Cw,by positivity,?_⟩
  filter_upwards [hrb,eventually_ge_atTop (Real.exp 1)] with T hre hTe
  have hT : 1 ≤ T := by have hh := Real.add_one_le_exp (1:ℝ); linarith
  have hL : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hTe
    simpa using hh
  intro A B hA hB hsep N K hN hscale M Q V hM hQ hV phi P hphi hP hp
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have h1 := hre A B hA hB hsep N hN hNT phi P hphi hP hp
  have h2 := hwb N K T M Q V _ _ hN hT hL hscale hM hQ hV
    (PRZZFreezeErrorBudget.scaled_real_bound A S (Real.log T) (by linarith) hA)
    (PRZZFreezeErrorBudget.scaled_real_bound B S (Real.log T) (by linarith) hB)
  have h2' := mul_le_mul_of_nonneg_left h2 hP
  calc
    _ ≤ Cr*P*T^delta*PRZZOptimalPowers.target N T+
        P*(Cw*T^delta*PRZZOptimalPowers.target N T) := by
      apply add_le_add h1
      convert h2' using 1 <;> ring
    _ = _ := by ring

#print axioms live_cost_gap
#print axioms first_scale_bound
#print axioms outer_power
#print axioms outer_absorbed
#print axioms replacement_and_empty_budget
end XiPrime8845.PRZZEmptyScaleAbsorption
