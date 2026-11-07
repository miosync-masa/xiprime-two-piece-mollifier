import PRZZPoissonAnalyticMass

/-! The additional spatial amplitude in the actual Poisson defect is
summed before height absorption. Empty positive-frequency rows have zero
charge here; this does not declare the original pre-Poisson row zero. -/
noncomputable section
open scoped BigOperators
open Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZSpatialFreezeBudget
open PRZZFiniteFreezeBudget PRZZActiveFreezeBudget PRZZPrefactorMass
set_option maxHeartbeats 6000000

def spatialMass (js : List ℕ) (N K : ℕ) (T M Q V eps eH eta : ℝ)
    (F G : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      sourceCost T ((2:ℝ)^k*M) eps j l*
        ∑ z ∈ active N d j l
          (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V),
          (z.1.2:ℝ)^(1+eta)*(3*((2:ℝ)^k*M))^eta*
            ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
              (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
              d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖

/-- The actual retained frequencies, not an assumed M envelope, pay for
every extra spatial weight in the entire finite outer sum. -/
theorem spatial_mass_le (js : List ℕ) (N K : ℕ) (T M Q V eps eH eta : ℝ)
    (F G : ℝ → ℂ) (alpha beta : ℂ)
    (hT : 1 ≤ T) (hNT : (N:ℝ) ≤ T) (hM : 0 < M) (hV : 0 < V)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) :
    spatialMass js N K T M Q V eps eH eta F G alpha beta ≤
      (6*(N:ℝ)*T^((2+eH)*eta))*
        PRZZFreezeErrorBudget.weightedMass js N K T M Q V eps eH F G alpha beta := by
  unfold spatialMass PRZZFreezeErrorBudget.weightedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hd1 := (Finset.mem_Icc.mp hd).1
  rw [mass,prune]
  have hb : (∑ z ∈ active N d j l
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
      (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
      (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V),
      (z.1.2:ℝ)^(1+eta)*(3*((2:ℝ)^k*M))^eta*
        ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
      (6*(N:ℝ)*T^((2+eH)*eta))*
        ∑ z ∈ active N d j l
          (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V),
          ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
            d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    exact mul_le_mul_of_nonneg_right
      (PRZZPoissonAnalyticMass.active_spatial_weight N d j l T ((2:ℝ)^k*M) Q V eps eH eta _ _ z
        hd1 hT hNT (by positivity) heta heta1
        (PRZZFreezeScales.scaled_support G V hV hsG) hz) (norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ sourceCost T ((2:ℝ)^k*M) eps j l by
      unfold sourceCost PRZZFreezeScales.ratioCap; positivity)
  exact hh.trans_eq (by ring)

/-- The seventh power, including all dyadic grids and the shift loss,
fits the published target under the actual enlarged exponent margin. -/
theorem enlarged_budget_absorbed (m : ℕ) (eps eH eta r delta : ℝ)
    (heps : 0 ≤ eps) (hr : 0 < r)
    (hmargin : 7*eps+eH+(2+eH)*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K : ℕ) (T M Q V : ℝ) (F1 F2 : ℝ → ℂ),
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V →
      Function.support F1 ⊆ Icc (Q/2) (3*Q) →
      Function.support F2 ⊆ Icc (V/2) (3*V) →
      (Real.log N)^m*(1+(Real.log T)^2/r^2)*T*
        ((6*(N:ℝ)*T^((2+eH)*eta))*budget N K T M Q V eps eH F1 F2) ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨D,hD,hpow⟩ := PRZZOptimalOuter.power_log_absorbed (m+4)
    (7*eps+eH+(2+eH)*eta) delta hmargin
  let c := 1/Real.log 2+1
  have hc : 0 < c := by dsimp [c]; positivity
  let B := (6*226492416)*c^2*(1+1/r^2)
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
  have hp := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (Real.log N)^m*(1+(Real.log T)^2/r^2)*(6*(N:ℝ)*T^((2+eH)*eta)) by positivity)
  have he : T^((2+eH)*eta)*T^(7*eps+eH) = T^(7*eps+eH+(2+eH)*eta) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have hlog : (Real.log N)^m*(1+(Real.log T)^2/r^2)*(6*(N:ℝ)*T^((2+eH)*eta))*
      (226492416*(Nat.log 2 N+1:ℝ)^2*T^(7*eps+eH)*((N:ℝ)^6/T^3)) ≤
      B*(T^(7*eps+eH+(2+eH)*eta)*(Real.log T)^(m+4))*((N:ℝ)^7/T^3) := by
    calc
      _ ≤ (Real.log T)^m*((1+1/r^2)*(Real.log T)^2)*(6*(N:ℝ)*T^((2+eH)*eta))*
          (226492416*(c*Real.log T)^2*T^(7*eps+eH)*((N:ℝ)^6/T^3)) := by gcongr
      _ = _ := by dsimp [B]; rw [show T^(7*eps+eH+(2+eH)*eta) = T^((2+eH)*eta)*T^(7*eps+eH) from he.symm]; simp only [pow_add]; ring
  have h2 := mul_le_mul (hpow T hT)
    (PRZZPoissonAnalyticMass.seventh_power_target N T hn hT hscale) (by positivity) (by positivity)
  calc
    _ = (Real.log N)^m*(1+(Real.log T)^2/r^2)*(6*(N:ℝ)*T^((2+eH)*eta))*(T*budget N K T M Q V eps eH F1 F2) := by ring
    _ ≤ B*(T^(7*eps+eH+(2+eH)*eta)*(Real.log T)^(m+4))*((N:ℝ)^7/T^3) := hp.trans hlog
    _ = B*((T^(7*eps+eH+(2+eH)*eta)*(Real.log T)^(m+4))*((N:ℝ)^7/T^3)) := by ring
    _ ≤ B*(D*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left h2 hB.le
    _ = _ := by ring

theorem spatial_absorbed (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eH eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hmargin : 7*eps+eH+(2+eH)*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K : ℕ) (T M Q V : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (1+(Real.log T)^2/r^2)*T*spatialMass js N K T M Q V eps eH eta F G alpha beta ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hmass⟩ := PRZZFreezeErrorBudget.weighted_mass_le F G hF hG hcF hcG
  obtain ⟨D,hD,hbudget⟩ := enlarged_budget_absorbed (2*PRZZGCoefficient.degree js)
    eps eH eta r delta heps hr hmargin
  refine ⟨C*Real.exp (2*S)*D,by positivity,?_⟩
  intro N K T M Q V alpha beta hN hT hL hscale hM hQ hV ha hb
  have ht : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have hw := spatial_mass_le js N K T M Q V eps eH eta F G alpha beta hT hNT hM hV heta heta1 hsG
  have hm := hmass js N K T M Q V S eps eH alpha beta hN hNT ht (by linarith) hS ha hb
  have hb' := hbudget N K T M Q V _ _ hN hT hL hscale hM hQ hV
    (PRZZFreezeScales.scaled_support F Q hQ hsF) (PRZZFreezeScales.scaled_support G V hV hsG)
  have h1 := mul_le_mul_of_nonneg_left (hw.trans
    (mul_le_mul_of_nonneg_left hm (show 0 ≤ 6*(N:ℝ)*T^((2+eH)*eta) by positivity)))
      (show 0 ≤ (1+(Real.log T)^2/r^2)*T by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb' (show 0 ≤ C*Real.exp (2*S) by positivity)
  apply h1.trans
  convert h2 using 1 <;> ring

/-- Combine the original zeta-to-W error integral with the corrected
spatially weighted charge. This is not a claim that h-empty AFE rows
vanish, nor an identification of all central modes with a single A*. -/
theorem replacement_and_spatial_budget
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eH eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hmargin : 7*eps+eH+(2+eH)*eta < delta) :
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
        spatialMass js N K T M Q V eps eH eta F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨Cr,hCr,hrb⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hdelta
  obtain ⟨Cw,hCw,hwb⟩ := spatial_absorbed F G hF hG hcF hcG hsF hsG js S r eps eH eta delta
    hS hr heps heta heta1 hmargin
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
  have h2' : P*(1+(Real.log T)^2/r^2)*T*
      spatialMass js N K T M Q V eps eH eta F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
      Cw*P*T^delta*PRZZOptimalPowers.target N T := by
    calc
      _ = P*((1+(Real.log T)^2/r^2)*T*
          spatialMass js N K T M Q V eps eH eta F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) := by ring
      _ ≤ P*(Cw*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left h2 hP
      _ = _ := by ring
  calc
    _ ≤ Cr*P*T^delta*PRZZOptimalPowers.target N T+Cw*P*T^delta*PRZZOptimalPowers.target N T :=
      add_le_add h1 h2'
    _ = _ := by ring

#print axioms spatial_mass_le
#print axioms enlarged_budget_absorbed
#print axioms spatial_absorbed
#print axioms replacement_and_spatial_budget
end XiPrime8845.PRZZSpatialFreezeBudget
