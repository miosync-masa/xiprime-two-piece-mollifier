import PRZZZeroGammaBound
import PRZZCappedBodyTail

/-! The actual integrated gammaDefect for a common bounded coefficient
class. Its arithmetic correction mass and Gamma 1/T gain are evaluated
before height and both coefficient slots; no defect bound is a premise. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCappedGammaDefect
open PRZZZeroCross PRZZCoupledAFE PRZZZeroGammaBound
set_option maxHeartbeats 10000000

theorem mass_bound (Hcap S : ℝ) (hHcap : 0 ≤ Hcap) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (N : ℕ) (T : ℝ) (a b : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      1 ≤ N → 1 < T → (N:ℝ) ≤ T →
      |a.re| ≤ S/Real.log T → |b.re| ≤ S/Real.log T →
      PRZZDiagonalAssembly.errorMass N c (fun _ => 1) (fun _ => 1) a b T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^2 := by
  obtain ⟨D,hD,h⟩ := PRZZDiagonalMass.mass_envelope
  refine ⟨D*(Hcap^2*Real.exp (2*S))+1,by positivity,?_⟩
  intro c N T a b hc hN hT hNT ha hb
  apply (h N T (Hcap^2*Real.exp (2*S)) c (fun _ => 1) (fun _ => 1) a b
    hN (by linarith) (by positivity) ?_).trans
  · gcongr
    linarith
  · intro d hd u hu v hv had
    simpa only [one_mul] using PRZZDiagonalMass.coefficient_envelope N d u v c
      (fun _ => 1) (fun _ => 1) a b Hcap 1 1 S T hHcap (by norm_num) (by norm_num)
      hS hT hNT (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hu).1
      (Finset.mem_Icc.mp hv).1 hc (by simp) (by simp) ha hb had.2.1 had.2.2

theorem correction_scaled_bound (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (N : ℕ) (T t : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 < T → (N:ℝ) ≤ T → T ≤ t →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ‖correction N c
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
      C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (1+Real.log N)^(2:ℕ) := by
  obtain ⟨C,hC,h⟩ := PRZZDiagonalAssembly.assembled_error
  obtain ⟨D,hD,hm⟩ := mass_bound Hcap S hHcap hS
  refine ⟨C*D,by positivity,?_⟩
  intro c N T t A B hcoef hN hT hNT ht hA hB hsep hn
  have hL : 0 < Real.log T := Real.log_pos hT
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hLc
  have hn' : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/8 := by rwa [← add_div]
  have ha : |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    gcongr
  have hb : |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    gcongr
  have hm' := hm c N T _ _ hcoef hN hT hNT ha hb
  have hh := h N c
    (fun _ => 1) (fun _ => 1) _ _ T t hs hn' (by linarith) ht
  rw [← correction_eq N _ _ _ hs hn' t (lt_of_lt_of_le (by linarith) ht)] at hh
  have he : 16/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2 =
      16*(Real.log T)^2/‖A+B‖^2 := by
    rw [← add_div,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  calc
    _ ≤ C*(1+16*(Real.log T)^2/r^2)*
      (D*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^(2:ℕ)) := by
      apply hh.trans
      gcongr
      unfold PRZZDiagonalAssembly.errorMass
      positivity
    _ = _ := by ring

/-- Full coefficient sums are evaluated before the 1/T Gamma gain is
spent. The fixed left contour yields N^(1/4) T^(-9/8), explicitly. -/
theorem defect_scaled_bound (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (A B : ℂ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ,
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ∀ t ∈ Icc T (2*T),
      ‖gammaDefect N c
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (1+Real.log N)^(2:ℕ) := by
  obtain ⟨D,hD,hc⟩ := correction_scaled_bound Hcap hHcap S r hS hr
  refine ⟨7*Real.exp (2*S+7)*D*(1+Real.exp (2*S)),by positivity,?_⟩
  filter_upwards [multiplier_scaled_difference S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2*Real.pi),eventually_ge_atTop (2:ℝ)] with T hm hsmall hpi hT
  intro c A B hA hB hsep N hcoef hN hNT t ht
  have hT1 : 1 < T := by linarith
  have hsmallSum : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  have hcd := hc c N T t A B hcoef hN hT1 hNT ht.1 hA hB hsep hsmallSum
  have hcr := hc c N T t (-B) (-A) hcoef hN hT1 hNT ht.1
    (by simpa using hB) (by simpa using hA)
    (by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep)
    (by simpa only [show -B+-A = -(A+B) by ring,neg_div,norm_neg] using hsmallSum)
  simp only [neg_div] at hcr
  have hp := scaled_power_cap S T t A B hS hT1 (hpi.trans ht.1)
    (by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [ht.2,Real.pi_gt_three]) hA hB
  have hmul := hm A B hA hB t ht
  rw [add_div] at hmul hp
  let V := D*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
    (1+Real.log N)^(2:ℕ)
  have hsub : ‖correction N c
      (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t-
      ((t/(2*Real.pi):ℝ):ℂ)^(A/(Real.log T:ℂ)+B/(Real.log T:ℂ))*
      correction N c
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ V+Real.exp (2*S)*V := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add hcr (mul_le_mul hp hcd (norm_nonneg _) (by positivity))
  unfold gammaDefect
  rw [norm_mul]
  have hh := mul_le_mul hmul hsub
    (norm_nonneg _) (by positivity : 0 ≤ (7*Real.exp (2*S+7))/T)
  apply hh.trans_eq
  rw [show -(9/8:ℝ) = -(1/8:ℝ)-1 by norm_num,Real.rpow_sub (by linarith : 0 < T)]
  norm_num only [Real.rpow_one]
  dsimp [V]
  ring

theorem defect_time_bound (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (A B : ℂ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ,
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ∀ phi : ℝ → ℂ, Continuous phi →
      ‖∫ t in Icc T (2*T), phi t*gammaDefect N
        c
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (1+Real.log N)^(2:ℕ)*
            (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := defect_scaled_bound Hcap hHcap S r hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c A B hA hB hsep N hcoef hN hNT phi hp
  let E := C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
    (1+Real.log N)^(2:ℕ)
  have hi : IntegrableOn (fun t : ℝ => E*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hp.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h c A B hA hB hsep N hcoef hN hNT t ht)
      (norm_nonneg _)).trans_eq (by dsimp [E]; ring)


theorem absorbed (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (Hcap S r : ℝ) (hHcap : 0 ≤ Hcap) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖∫ t in Icc T (2*T), PRZZMellinSeparation.scaledCutoff Phi T t*
        gammaDefect N c (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := defect_time_bound Hcap hHcap S r hS hr
  obtain ⟨U,hU,hu⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  obtain ⟨D,hD,hd⟩ := PRZZOptimalOuter.power_log_absorbed 4 (-(1/8)) 0 (by norm_num)
  let K := 4*C*U*(1+16/r^2)*D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro c N A B hc hN hNT hA hB hsep
  have hT0 : 0 < T := by linarith
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hn
  have hlNT : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hp := h c A B hA hB hsep N hc hN hNT (PRZZMellinSeparation.scaledCutoff Phi T)
    (hPhi.comp (continuous_const.mul continuous_id))
  have hlogs : (1+16*(Real.log T)^2/r^2)*(1+Real.log N)^2 ≤
      4*(1+16/r^2)*(Real.log T)^4 := by
    have h1 : 1+16*(Real.log T)^2/r^2 ≤ (1+16/r^2)*(Real.log T)^2 := by
      calc
        _ = 1+(16/r^2)*(Real.log T)^2 := by ring
        _ ≤ (Real.log T)^2+(16/r^2)*(Real.log T)^2 := by nlinarith
        _ = _ := by ring
    have h2 : (1+Real.log N)^2 ≤ 4*(Real.log T)^2 := by nlinarith
    exact (mul_le_mul h1 h2 (by positivity) (by positivity)).trans_eq (by ring)
  have hpow : T^(-(9/8:ℝ))*T = T^(-(1/8:ℝ)) := by
    calc
      _ = T^(-(9/8:ℝ))*T^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hT0]; norm_num
  have htar : (N:ℝ)^(1/4:ℝ) ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1/4:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
        (1+Real.log N)^2*(U*T) := hp.trans (mul_le_mul_of_nonneg_left (hu T hT0).2 (by positivity))
    _ = C*U*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        ((1+16*(Real.log T)^2/r^2)*(1+Real.log N)^2) := by
      calc
        _ = C*U*(N:ℝ)^(1/4:ℝ)*(T^(-(9/8:ℝ))*T)*
            ((1+16*(Real.log T)^2/r^2)*(1+Real.log N)^2) := by ring
        _ = _ := by rw [hpow]
    _ ≤ C*U*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (4*(1+16/r^2)*(Real.log T)^4) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = (4*C*U*(1+16/r^2))*(N:ℝ)^(1/4:ℝ)*
        (T^(-(1/8:ℝ))*(Real.log T)^4) := by ring
    _ ≤ (4*C*U*(1+16/r^2))*(N:ℝ)^(1/4:ℝ)*D :=
      mul_le_mul_of_nonneg_left (by simpa using hd T (by linarith)) (by positivity)
    _ ≤ (K+1)*PRZZOptimalPowers.target N T := by
      calc
        _ = K*(N:ℝ)^(1/4:ℝ) := by dsimp [K]; ring
        _ ≤ K*PRZZOptimalPowers.target N T := mul_le_mul_of_nonneg_left htar hK
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by unfold PRZZOptimalPowers.target; positivity)

theorem mixed_absorbed (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (Hcap S r : ℝ) (hHcap : 0 ≤ Hcap) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c e : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun f => ∫ t in Icc T (2*T),
        PRZZMellinSeparation.scaledCutoff Phi T t*
        gammaDefect N f (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) c e‖ ≤
        C*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := absorbed Phi hPhi hcPhi (2*Hcap) S r (by positivity) hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c e N A B hc he hN hNT hA hB hsep
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact h _ N A B (PRZZClassZeroCorrection.combine_cap N c e Hcap hHcap hc he z hz)
    hN hNT hA hB hsep

#print axioms absorbed
#print axioms mixed_absorbed
#print axioms mass_bound
#print axioms correction_scaled_bound
#print axioms defect_scaled_bound
#print axioms defect_time_bound
end XiPrime8845.PRZZCappedGammaDefect
