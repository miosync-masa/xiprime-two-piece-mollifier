import PRZZEmptyMomentMass
import PRZZCappedPrefactor

/-! Weighted freezing arithmetic mass for arbitrary common-cap coefficients.
The spatial v^(1+eta)(3M)^eta factor is retained. The first live spatial
scale is selected before summing the complete d,j,l family. -/
noncomputable section
open scoped BigOperators
open Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZCappedFreezeMoment
open PRZZPrefactorMass PRZZActiveFreezeBudget PRZZFreezeScales
open PRZZEmptyArithmeticMass PRZZEmptyMomentScalar PRZZEmptyMomentMass
set_option maxHeartbeats 8000000

theorem spatial_moment (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (Hcap : ℝ) (N d j l K : ℕ) (T M Q V S eps eta : ℝ) (alpha beta : ℂ),
      0 ≤ Hcap → (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T →
      0 < M → 0 ≤ Q → 0 ≤ S → 0 ≤ eta → eta ≤ 1 →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMoment N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) ((2:ℝ)^k*M) eta
          c
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta) ≤
        C*Real.exp (2*S)*Hcap^2*(N:ℝ)*T^eta/(d:ℝ)^3*
          ((3*M)^eta*sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps) := by
  obtain ⟨C,hC,h⟩ := PRZZCappedPrefactor.coefficient_row F G hF hG hcF hcG
  refine ⟨C*10*(4/3),by positivity,?_⟩
  intro c Hcap N d j l K T M Q V S eps eta alpha beta hHcap hcoef hN hd hNT hT hL hM hQ hS heta heta1 ha hb
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  let A := C*Real.exp (2*S)*Hcap^2*10*(N:ℝ)*T^eta/(d:ℝ)^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ k ∈ Finset.range K, A*((3*((2:ℝ)^k*M))^eta*sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) := by
      apply Finset.sum_le_sum
      intro k hk
      have hm := row_moment_le N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) T ((2:ℝ)^k*M) eta
        c
        (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta hd hNT heta (by positivity)
      have hc := h c Hcap N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) T Q V S alpha beta
        hHcap hcoef hN hd hNT hL (by unfold PRZZSourceCutoffs.deltaCutoff; positivity) hS ha hb
      have he := mul_le_mul_of_nonneg_left
        (hm.trans (mul_le_mul_of_nonneg_left hc (show 0 ≤ ((N:ℝ)/d*T^eta)*(3*((2:ℝ)^k*M))^eta by positivity)))
        (show 0 ≤ sourceCost T ((2:ℝ)^k*M) eps j l by unfold sourceCost ratioCap; positivity)
      exact he.trans_eq (by dsimp [A]; ring)
    _ = A*(∑ k ∈ Finset.range K, (3*((2:ℝ)^k*M))^eta*sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((4/3)*((3*M)^eta*sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps)) :=
      mul_le_mul_of_nonneg_left (weighted_gap_sum T M Q eps eta j l K hT hM hQ heta heta1) hA
    _ = _ := by dsimp [A]; ring

theorem first_moment (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (Hcap : ℝ) (N d j l K : ℕ) (T M Q V S eps eta : ℝ) (alpha beta : ℂ),
      0 ≤ Hcap → (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ T → 0 < Real.log T →
      0 < M → 0 < Q → 0 < V → 0 ≤ S → 0 ≤ eps → 0 ≤ eta → eta ≤ 1 →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMoment N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) ((2:ℝ)^k*M) eta
          c
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta) ≤
        C*Real.exp (2*S)*Hcap^2*T^3*T^eta*T^eta*(N:ℝ)^5/
          ((d:ℝ)^6*(T^(1-eps))^6) := by
  classical
  obtain ⟨C,hC,h⟩ := spatial_moment F G hF hG hcF hcG
  refine ⟨C*(9*331776)*16,by positivity,?_⟩
  intro c Hcap N d j l K T M Q V S eps eta alpha beta hHcap hcoef hN hd hNT hT hL hM hQ hV hS heps heta heta1 ha hb
  let F1 := PRZZMellinSeparation.scaledCutoff F Q
  let F2 := PRZZMellinSeparation.scaledCutoff G V
  let row := fun i => sourceCost T ((2:ℝ)^i*M) eps j l*
    rowMoment N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*M) Q eps) ((2:ℝ)^i*M) eta
      c F1 F2 alpha beta
  let live := fun i => (active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*M) Q eps) 2 F1 F2).Nonempty
  have hz (i : ℕ) (hi : ¬live i) : row i = 0 := by
    have he := Finset.not_nonempty_iff_eq_empty.mp hi
    simp [row,rowMoment,he]
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
          rowMoment N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^i*((2:ℝ)^k*M)) Q eps) ((2:ℝ)^i*((2:ℝ)^k*M)) eta
            c F1 F2 alpha beta := by
      nth_rw 1 [show K = k+(K-k) by omega]
      rw [Finset.sum_range_add,hpre,zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [row]
      rw [pow_add,show (2:ℝ)^k*(2:ℝ)^i*M = (2:ℝ)^i*((2:ℝ)^k*M) by ring]
    obtain ⟨z,hz'⟩ := hk.2
    have hs1 := scaled_support F Q hQ hsF
    have hs2 := scaled_support G V hV hsG
    have hc := live_weighted_cost N d j l T ((2:ℝ)^k*M) Q V eps eta F1 F2
      (by omega) hT (by positivity) hQ hV heps heta heta1 hs1 hs2 z hz'
    have hh := Finset.mem_filter.mp hz'
    have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hh.1).1).2
    have hu : (d:ℝ)*z.1.1 ≤ N := by exact_mod_cast hp.2.1
    have hv : (d:ℝ)*z.1.2 ≤ N := by exact_mod_cast hp.2.2
    have hQc : Q ≤ 2*N := by linarith [(hs1 hh.2.1).1]
    have hVc : V ≤ 2*N := by linarith [(hs2 hh.2.2).1]
    have hc' : (3*((2:ℝ)^k*M))^eta*sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps ≤
        (9*331776*16)*T^3*T^eta*(N:ℝ)^4/((d:ℝ)^3*(T^(1-eps))^6) := by
      apply hc.trans
      calc
        _ ≤ (9*331776)*T^3*T^eta*(2*(N:ℝ))^2*(2*(N:ℝ))^2/((d:ℝ)^3*(T^(1-eps))^6) := by gcongr
        _ = _ := by ring
    rw [he]
    have hb' := h c Hcap N d j l (K-k) T ((2:ℝ)^k*M) Q V S eps eta alpha beta
      hHcap hcoef hN hd hNT (by linarith) hL (by positivity) hQ.le hS heta heta1 ha hb
    apply hb'.trans
    have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hfinal := mul_le_mul_of_nonneg_left hc'
      (show 0 ≤ C*Real.exp (2*S)*Hcap^2*(N:ℝ)*T^eta/(d:ℝ)^3 by positivity)
    convert hfinal using 1; ring
  · rw [Finset.sum_eq_zero (fun i hi => hz i (fun hh => hex ⟨i,Finset.mem_range.mp hi,hh⟩))]
    positivity

def outerMoment (c : ℕ → ℂ) (N K : ℕ) (T M Q V eps eta : ℝ)
    (F G : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMoment N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) ((2:ℝ)^k*M) eta
          c
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta

theorem outer_power (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (Hcap : ℝ) (N K : ℕ) (T M Q V S eps eta : ℝ) (alpha beta : ℂ),
      0 ≤ Hcap → (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 1 ≤ T → 0 < Real.log T → 0 < M → 0 < Q → 0 < V →
      0 ≤ S → 0 ≤ eps → 0 ≤ eta → eta ≤ 1 →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      T*outerMoment c N K T M Q V eps eta F G alpha beta ≤
        C*Real.exp (2*S)*Hcap^2*
          (Nat.log 2 N+1:ℝ)^2*T^(6*eps+2*eta)*((N:ℝ)^5/T^2) := by
  obtain ⟨C,hC,h⟩ := first_moment F G hF hG hcF hcG hsF hsG
  refine ⟨2*C,by positivity,?_⟩
  intro c Hcap N K T M Q V S eps eta alpha beta hHcap hcoef hN hNT hT hL hM hQ hV hS heps heta heta1 ha hb
  have ht : 0 < T := by linarith
  let B := C*Real.exp (2*S)*Hcap^2*
    (Nat.log 2 N+1:ℝ)^2*T^3*T^eta*T^eta*(N:ℝ)^5/(T^(1-eps))^6
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : outerMoment c N K T M Q V eps eta F G alpha beta ≤ B*2 := by
    unfold outerMoment
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
          ∑ l ∈ Finset.range (Nat.log 2 N+1),
            C*Real.exp (2*S)*Hcap^2*T^3*T^eta*T^eta*(N:ℝ)^5/
              ((d:ℝ)^6*(T^(1-eps))^6) := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro l hl
        exact h c Hcap N d j l K T M Q V S eps eta alpha beta hHcap hcoef hN (Finset.mem_Icc.mp hd).1 hNT hT hL hM hQ hV hS heps heta heta1 ha hb
      _ = B*(∑ d ∈ Finset.Icc 1 N, 1/(d:ℝ)^6) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        dsimp [B]
        push_cast
        ring
      _ ≤ B*2 := mul_le_mul_of_nonneg_left (divisor_sixth N) hB
  have he : T*T^3*T^eta*T^eta/(T^(1-eps))^6 = T^(6*eps+2*eta)/T^2 := by
    rw [show T*T^3 = T^4 by ring]
    simp only [← Real.rpow_natCast,← Real.rpow_mul ht.le,← Real.rpow_add ht,← Real.rpow_sub ht]
    congr 1
    norm_num
    ring
  apply (mul_le_mul_of_nonneg_left hm ht.le).trans_eq
  calc
    _ = (2*C*Real.exp (2*S)*Hcap^2*(Nat.log 2 N+1:ℝ)^2*(N:ℝ)^5)*
        (T*T^3*T^eta*T^eta/(T^(1-eps))^6) := by dsimp [B]; ring
    _ = _ := by rw [he]; ring

theorem absorbed (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (N K : ℕ) (T M Q V : ℝ) (alpha beta : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V → |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (1+(Real.log T)^2/r^2)*T*outerMoment a N K T M Q V eps eta F G alpha beta ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := outer_power F G hF hG hcF hcG hsF hsG
  let m : ℕ := 0
  obtain ⟨D,hD,hpow⟩ := PRZZOptimalOuter.power_log_absorbed (m+4) (6*eps+2*eta) delta hmargin
  let c := 1/Real.log 2+1
  have hc : 0 < c := by dsimp [c]; positivity
  let B := C*Real.exp (2*S)*(Hcap^2+1)*c^2*(1+1/r^2)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B*D,by positivity,?_⟩
  intro a N K T M Q V alpha beta hcoef hN hT hL hscale hM hQ hV ha hb
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
    (h a Hcap N K T M Q V S eps eta alpha beta hHcap hcoef hN hNT hT (by linarith) hM hQ hV hS heps heta heta1 ha hb)
    (show 0 ≤ 1+(Real.log T)^2/r^2 by positivity)
  have hlog : (1+(Real.log T)^2/r^2)*
      (C*Real.exp (2*S)*Hcap^2*(Nat.log 2 N+1:ℝ)^2*T^(6*eps+2*eta)*((N:ℝ)^5/T^2)) ≤
      B*(T^(6*eps+2*eta)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2) := by
    calc
      _ ≤ ((1+1/r^2)*(Real.log T)^2)*
          (C*Real.exp (2*S)*(Hcap^2+1)*(c*Real.log T)^2*T^(6*eps+2*eta)*((N:ℝ)^5/T^2)) := by gcongr; nlinarith
      _ = _ := by dsimp [B]; simp only [pow_add]; ring
  have hp := mul_le_mul (hpow T hT) (fifth_power_target N T hn hT hscale) (by positivity) (by positivity)
  calc
    _ = (1+(Real.log T)^2/r^2)*(T*outerMoment a N K T M Q V eps eta F G alpha beta) := by ring
    _ ≤ B*(T^(6*eps+2*eta)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2) := hh.trans hlog
    _ = B*((T^(6*eps+2*eta)*(Real.log T)^(m+4))*((N:ℝ)^5/T^2)) := by ring
    _ ≤ B*(D*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left hp hB.le
    _ = _ := by ring

#print axioms absorbed
#print axioms spatial_moment
#print axioms first_moment
#print axioms outer_power
end XiPrime8845.PRZZCappedFreezeMoment
