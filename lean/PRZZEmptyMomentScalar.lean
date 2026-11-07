import PRZZEmptyScaleAbsorption

/-! Scalar spatial moments for h-free congruence rows. The factor M^eta
is kept before selecting the first nonempty scale. Constants do not depend
on the first scale or on the finite truncation. -/
noncomputable section
open scoped BigOperators
open Set
namespace XiPrime8845.PRZZEmptyMomentScalar
open PRZZPrefactorMass PRZZActiveFreezeBudget PRZZFreezeScales PRZZEmptyArithmeticMass
set_option maxHeartbeats 6000000

theorem moment_decreasing (M L T eta : ℝ) (hL : 0 < L) (hLM : L ≤ M)
    (hT : 0 < T) (hLT : L ≤ 3*T) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (3*M)^eta/M^3 ≤ 9*T^eta/L^3 := by
  have hM : 0 < M := hL.trans_le hLM
  have h3 : (3:ℝ)^eta ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) heta1
  have he (x : ℝ) (hx : 0 < x) : (3*x)^eta/x^3 = (3:ℝ)^eta*x^(eta-3) := by
    have h3x : x^(3:ℝ) = x^3 := by norm_num
    have hm : x^(eta-3)*x^3 = x^eta := by
      rw [← h3x,← Real.rpow_add hx]
      congr 1
      ring
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hx.le]
    apply (div_eq_iff (by positivity : x^3 ≠ 0)).mpr
    calc
      _ = (3:ℝ)^eta*(x^(eta-3)*x^3) := by rw [hm]
      _ = _ := by ring
  rw [he M hM]
  calc
    _ ≤ (3:ℝ)^eta*L^(eta-3) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hL hLM (by linarith)) (by positivity)
    _ = (3:ℝ)^eta*L^eta/L^3 := by rw [← he L hL,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hL.le]
    _ ≤ 3*(3*T)^eta/L^3 := by gcongr
    _ = 3*((3:ℝ)^eta*T^eta)/L^3 := by rw [Real.mul_rpow (by norm_num) hT.le]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul_of_nonneg_right h3 (show 0 ≤ 3*T^eta by positivity)
      convert hh using 1 <;> ring

theorem weighted_gap_sum (T M Q eps eta : ℝ) (j l K : ℕ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 ≤ Q) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (∑ k ∈ Finset.range K, (3*((2:ℝ)^k*M))^eta*sourceCost T ((2:ℝ)^k*M) eps j l*
      PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) ≤
      (4/3:ℝ)*((3*M)^eta*sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps) := by
  let B := (3*M)^eta*sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps
  have hB : 0 ≤ B := by dsimp [B,sourceCost,ratioCap,PRZZSourceCutoffs.deltaCutoff]; positivity
  have hc (k : ℕ) : sourceCost T ((2:ℝ)^k*M) eps j l*
      PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps =
      (sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps)*(1/8:ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,show (2:ℝ)^k*2*M = 2*((2:ℝ)^k*M) by ring,PRZZEmptyArithmeticMass.cost_gap_double,ih,pow_succ]
      ring
  have hp (k : ℕ) : (3*((2:ℝ)^k*M))^eta ≤ (2:ℝ)^k*(3*M)^eta := by
    rw [show 3*((2:ℝ)^k*M) = (2:ℝ)^k*(3*M) by ring,Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) heta1
  have hg : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 4/3 := by
    have he : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) = (4/3:ℝ)*(1-(1/4:ℝ)^K) := by
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
    rw [he]
    nlinarith [show 0 ≤ (1/4:ℝ)^K by positivity]
  calc
    _ ≤ ∑ k ∈ Finset.range K, B*(1/4:ℝ)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := mul_le_mul_of_nonneg_right (hp k)
        (show 0 ≤ sourceCost T ((2:ℝ)^k*M) eps j l*PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps by
          unfold sourceCost ratioCap PRZZSourceCutoffs.deltaCutoff; positivity)
      rw [hc] at hh
      have he : (2:ℝ)^k*(1/8:ℝ)^k = (1/4:ℝ)^k := by rw [← mul_pow]; norm_num
      calc
        _ = (3*((2:ℝ)^k*M))^eta*(sourceCost T ((2:ℝ)^k*M) eps j l*
            PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) := by ring
        _ = (3*((2:ℝ)^k*M))^eta*((sourceCost T M eps j l*
            PRZZSourceCutoffs.deltaCutoff T M Q eps)*(1/8:ℝ)^k) := by rw [hc]
        _ ≤ _ := hh
        _ = B*(1/4:ℝ)^k := by rw [← he]; dsimp [B]; ring
    _ = B*(∑ k ∈ Finset.range K, (1/4:ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*(4/3) := mul_le_mul_of_nonneg_left hg hB
    _ = _ := by dsimp [B]; ring

theorem live_weighted_cost (N d j l : ℕ) (T M Q V eps eta : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (heps : 0 ≤ eps) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (z : PRZZAStar.Index)
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2) :
    (3*M)^eta*sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps ≤
      (9*331776)*T^3*T^eta*Q^2*V^2/((d:ℝ)^3*(T^(1-eps))^6) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 < T := by linarith
  let A := T^(1-eps)
  let L := (d:ℝ)*A/Q
  have hA : 0 < A := by dsimp [A]; positivity
  have hLp : 0 < L := by dsimp [L]; positivity
  have hAT : A ≤ T := by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hT (show 1-eps ≤ (1:ℝ) by linarith)
  have hlo := active_spatial_lower N d j l T M Q eps 2 F1 F2 hd ht z hz
  have hLM : L ≤ M := (div_le_iff₀ hQ).mpr hlo.le
  have hpair := Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  have hu1 : (1:ℝ) ≤ z.1.1 := by
    exact_mod_cast (Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N j z.1.1).mp (Finset.mem_product.mp hpair.1).1).1).1
  have hF := (hs1 (Finset.mem_filter.mp hz).2.1).2
  have hdQ : (d:ℝ) ≤ 3*Q := by nlinarith
  have hLT : L ≤ 3*T := by
    dsimp [L]
    apply (div_le_iff₀ hQ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hAT hd0.le]
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
  have hm := moment_decreasing M L T eta hLp hLM ht hLT heta heta1
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (3*M)^eta by positivity))
    (show 0 ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps by unfold PRZZSourceCutoffs.deltaCutoff; positivity)
  apply hh.trans
  calc
    _ = (2304*U*V^2/(Q*A))*((3*M)^eta/M^3) := by
      change _*(M*Q/A) = _
      field_simp
      ring
    _ ≤ (2304*(144*T^3/A^2)*V^2/(Q*A))*(9*T^eta/L^3) := by gcongr
    _ = _ := by dsimp [L,A]; field_simp; ring

theorem divisor_sixth (N : ℕ) : (∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^6) ≤ 2 := by
  have hb (N : ℕ) : (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)^6) ≤ 2-2/((N:ℝ)+1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hd : 1 ≤ (N:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
      have hp : ((N:ℝ)+1)^2 ≤ ((N:ℝ)+1)^6 := pow_le_pow_right₀ hd (by omega)
      have ht : 1/((N:ℝ)+1)^6 ≤ 2/(((N:ℝ)+1)*((N:ℝ)+2)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      rw [Finset.sum_range_succ]
      calc
        _ ≤ (2-2/((N:ℝ)+1))+2/(((N:ℝ)+1)*((N:ℝ)+2)) := add_le_add ih ht
        _ = _ := by push_cast; field_simp; ring
  have he : (∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^6) = ∑ k ∈ Finset.range N, 1/((k:ℝ)+1)^6 := by
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

#print axioms moment_decreasing
#print axioms weighted_gap_sum
#print axioms live_weighted_cost
#print axioms divisor_sixth
end XiPrime8845.PRZZEmptyMomentScalar
