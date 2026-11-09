import PRZZLargeResolvedPruning
import PRZZClassZeroCorrection
import PRZZRemainderBudget

/-! Collective large-spatial pruning with a common coefficient cap.
Spatial pieces are summed before estimates, uniformly in L and J. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex Set Filter MeasureTheory
namespace XiPrime8845.PRZZCappedLarge
open PRZZLargeSpatialFamily PRZZLargeSpatialKernel PRZZLargeSpatialHeight PRZZResolvedComplement
set_option maxHeartbeats 9000000
theorem coefficient_mass (c : ℕ → ℂ) (Hcap : ℝ) (N : ℕ)
    (hcap : ∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) (hN : 1 ≤ N) (t : ℝ) :
    mass c N t ≤ 2*Real.sqrt N*Hcap := by
  unfold mass
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Hcap*(1/Real.sqrt n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_div,← Complex.ofReal_natCast n,norm_cpow_eq_rpow_re_of_pos hn0]
      have he : (1/2+(t:ℂ)*I).re = (1/2:ℝ) := by simp
      rw [he,← Real.sqrt_eq_rpow]
      have hc : ‖c n‖ ≤ Hcap := hcap n hn
      exact (div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _)).trans_eq (by ring)
    _ = Hcap*(∑ n ∈ Finset.Icc 1 N, 1/Real.sqrt n) := by rw [mul_sum]
    _ ≤ Hcap*(2*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (PRZZReplacementMass.reciprocal_sqrt_sum N)
        (le_trans (norm_nonneg _) (hcap 1 (mem_Icc.mpr ⟨le_rfl,hN⟩)))
    _ = _ := by ring

theorem retained_uniform (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (Z r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (L N : ℕ) (A B : ℂ) (t X : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      t ∈ Icc T (2*T) → 0 < X →
      ‖PRZZWRowLimit.retained L N (fun y => (S y:ℂ)) (fun s _ => X ≤ (2:ℝ)^s)
        c c
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^6/X^2 := by
  obtain ⟨Cs,hCs,hshift⟩ := constant_scaled r hr
  obtain ⟨Cl,hCl,hlog⟩ := PRZZOptimalOuter.power_log_absorbed (2) 0 1 (by norm_num)
  let D := 16*Hcap^2*Cs*PRZZWeightTail.squareMass^2/Real.pi^4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D*Cl+1,by positivity,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually Z (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hsmall hT
  intro c L N A B t X hcoef hN hNT hA hB hsep ht hX
  have hT0 : 0 < T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have ha := (abs_le.mp ((abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA))).1
  have hb := (abs_le.mp ((abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB))).1
  have hbase := retained_large_bound S hm hlo hhi hleft hright L N
    c c
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hs (by linarith) (by linarith) T t X hT0 ht hX
  rw [← add_div] at hbase
  have hc := hshift (Real.log T) A B hsmall.1 hsep
  have hmass := coefficient_mass c Hcap N hcoef hN t
  have hmassT : mass c N t ≤ 2*Hcap*Real.sqrt N := by nlinarith only [hmass]
  have hm0 : 0 ≤ mass c N t := sum_nonneg (fun n hn => norm_nonneg _)
  have hh := hlog T (by linarith)
  simp only [Real.rpow_zero,one_mul,Real.rpow_one] at hh
  apply hbase.trans
  calc
    _ ≤ (4*(Cs*(Real.log T)^2)*(T/Real.pi)^4/X^2)*PRZZWeightTail.squareMass^2*
        (2*Hcap*Real.sqrt N)*(2*Hcap*Real.sqrt N) := by
      gcongr
    _ = D*T^4*(Real.sqrt N)^2*(Real.log T)^(2)/X^2 := by
      dsimp [D]
      ring
    _ = D*T^4*(N:ℝ)*(Real.log T)^(2)/X^2 := by
      rw [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)]
    _ ≤ D*T^5*(Real.log T)^(2)/X^2 := by
      calc
        _ ≤ D*T^4*T*(Real.log T)^(2)/X^2 := by gcongr
        _ = _ := by ring
    _ = (D*T^5/X^2)*(Real.log T)^(2) := by ring
    _ ≤ (D*T^5/X^2)*(Cl*T) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (D*Cl)*T^6/X^2 := by ring
    _ ≤ _ := by gcongr; linarith


theorem masked_uniform (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (Z r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (L J N : ℕ) (A B : ℂ) (t X : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      t ∈ Icc T (2*T) → 0 < X →
      ‖masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
        c (fun s _ => X ≤ (2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^6/X^2 := by
  obtain ⟨C,hC,h⟩ := retained_uniform S hm hlo hhi hleft hright Hcap hHcap Z r hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro c L J N A B t X hcoef hN hNT hA hB hsep ht hX
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  rw [masked_original L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1) hS
    (by intro y hy; simp [hleft y hy]) (by intro y hy; simp [hright y hy])
    c (fun s _ => X ≤ (2:ℝ)^s)
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hs t (by linarith [ht.1])]
  have hl : PRZZWRowReindex.leftCoefficient c (fun _ => 1) =
      c := by funext n; simp [PRZZWRowReindex.leftCoefficient]
  have hr' : PRZZWRowReindex.rightCoefficient c (fun _ => 1) =
      c := by funext n; simp [PRZZWRowReindex.rightCoefficient]
  rw [hl,hr']
  exact h c L N A B t X hcoef hN hNT hA hB hsep ht hX

/-- Every prescribed power is available for the entire large-M family,
uniformly in the original L,J cutoffs, under a continuous time weight.
The explicit threshold is T^((power+6)/2); the L1 time mass is retained. -/
theorem large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (Z r power : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi →
      ‖∫ t in Icc T (2*T), phi t *
        masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
          c (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := masked_uniform S hm hlo hhi hleft hright hS Hcap hHcap Z r hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro c L J N A B phi hcoef hN hNT hA hB hsep hphi
  have hT0 : 0 < T := by linarith
  have he : T^6/(T^((power+6)/2))^2 = T^(-power) := by
    rw [← Real.rpow_natCast T 6,← Real.rpow_natCast (T^((power+6)/2)) 2,
      ← Real.rpow_mul hT0.le,← Real.rpow_sub hT0]
    congr 1
    ring
  have hi : IntegrableOn (fun t => C*T^(-power)*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    have hh := h c L J N A B t (T^((power+6)/2)) hcoef hN hNT hA hB hsep ht (by positivity)
    have hh' : ‖masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
        c (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^(-power) :=
      hh.trans_eq (by rw [mul_div_assoc,he])
    exact (mul_le_mul_of_nonneg_left hh' (norm_nonneg _)).trans_eq (by ring)

/-- The genuine original Gamma multiplier remains inside the reflected
branch's time integral. Its continuity and uniform cap are supplied. -/
theorem dual_large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (Z r power : ℝ) (hZ : 0 ≤ Z) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi →
      ‖∫ t in Icc T (2*T), (phi t *
        PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) *
        masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
          c (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
          ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ)) t‖ ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := large_time S hm hlo hhi hleft hright hS Hcap hHcap Z r power hr
  refine ⟨C*Real.exp (2*Z+7),by positivity,?_⟩
  filter_upwards [h,PRZZDualError.multiplier_scaled_cap Z hZ,
    PRZZScaledReplacement.shifts_eventually Z (1/4) (by norm_num)] with T h hgam hsmall
  intro c L J N A B phi hcoef hN hNT hA hB hsep hphi
  have hTpos : 0 < T := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  have hcont := (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).continuous
  have hsep' : r ≤ ‖-B+-A‖ := by
    rw [show -B+-A = -(A+B) by ring,norm_neg]
    exact hsep
  have hh := h c L J N (-B) (-A)
    (fun t => phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
    hcoef hN hNT (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA)
    hsep' (hphi.mul hcont)
  have hi : IntegrableOn (fun t : ℝ => Real.exp (2*Z+7)*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  have hmass : (∫ t in Icc T (2*T),
      ‖phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖) ≤
        Real.exp (2*Z+7)*(∫ t in Icc T (2*T), ‖phi t‖) := by
    apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
    · rw [integral_const_mul]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul,mul_comm (Real.exp (2*Z+7))]
      exact mul_le_mul_of_nonneg_left (hgam A B hA hB t ht) (norm_nonneg _)
  exact hh.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring))

theorem paired_mixed_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (Z r : ℝ) (hZ : 0 ≤ Z) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c d : ℕ → ℂ) (L J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun a => PRZZRemainderBudget.paired
        (PRZZRemainderBudget.largeField (fun x => (S x:ℂ)) L J N a T) Phi T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤
        C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  obtain ⟨Cp,hCp,hp⟩ := large_time S hm hlo hhi hleft hright hS
    (2*Hcap) (by positivity) Z r 2 hr
  obtain ⟨Cd,hCd,hd⟩ := dual_large_time S hm hlo hhi hleft hright hS
    (2*Hcap) (by positivity) Z r 2 hZ hr
  refine ⟨Cp+Cd,by positivity,?_⟩
  filter_upwards [hp,hd] with T hp hd
  intro c d L J N A B hc hdcoef hN hNT hA hB hsep
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  have hcoef := PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hdcoef z hz
  have hcont : Continuous (fun t : ℝ => Phi (t/T)) := hPhi.comp (continuous_id.div_const T)
  have h1 := hp _ L J N A B _ hcoef hN hNT hA hB hsep hcont
  have h2 := hd _ L J N A B _ hcoef hN hNT hA hB hsep hcont
  norm_num only [show ((2:ℝ)+6)/2 = 4 by norm_num] at h1 h2
  simp only [neg_div] at h2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

#print axioms paired_mixed_time
#print axioms masked_uniform
#print axioms large_time
#print axioms dual_large_time
#print axioms coefficient_mass
#print axioms retained_uniform
end XiPrime8845.PRZZCappedLarge
