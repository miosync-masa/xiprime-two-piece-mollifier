import PRZZLargeSpatialHeight
import PRZZDualSmooth

/-! Transfer large-spatial decay to the actual fully resolved Poisson
family, including its central/tail/boundary/freezing/complement pieces.
No individual Fourier component is declared small in isolation. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZLargeResolvedPruning
open PRZZGCoefficient PRZZResolvedComplement PRZZLargeSpatialHeight
set_option maxHeartbeats 7000000

theorem masked_uniform (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (js : List ℕ) (Z r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (A B : ℂ) (t X : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      t ∈ Icc T (2*T) → 0 < X →
      ‖masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (coefficient js n:ℂ)) (fun s _ => X ≤ (2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^6/X^2 := by
  obtain ⟨C,hC,h⟩ := retained_uniform S hm hlo hhi hleft hright js Z r hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro L J N A B t X hN hNT hA hB hsep ht hX
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  rw [masked_original L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1) hS
    (by intro y hy; simp [hleft y hy]) (by intro y hy; simp [hright y hy])
    (fun n => (coefficient js n:ℂ)) (fun s _ => X ≤ (2:ℝ)^s)
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) hs t (by linarith [ht.1])]
  have hl : PRZZWRowReindex.leftCoefficient (fun n => (coefficient js n:ℂ)) (fun _ => 1) =
      (fun n => (coefficient js n:ℂ)) := by funext n; simp [PRZZWRowReindex.leftCoefficient]
  have hr' : PRZZWRowReindex.rightCoefficient (fun n => (coefficient js n:ℂ)) (fun _ => 1) =
      (fun n => (coefficient js n:ℂ)) := by funext n; simp [PRZZWRowReindex.rightCoefficient]
  rw [hl,hr']
  exact h L N A B t X hN hNT hA hB hsep ht hX

/-- Every prescribed power is available for the entire large-M family,
uniformly in the original L,J cutoffs, under a continuous time weight.
The explicit threshold is T^((power+6)/2); the L1 time mass is retained. -/
theorem large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (js : List ℕ) (Z r power : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi →
      ‖∫ t in Icc T (2*T), phi t *
        masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
          (fun n => (coefficient js n:ℂ)) (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := masked_uniform S hm hlo hhi hleft hright hS js Z r hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro L J N A B phi hN hNT hA hB hsep hphi
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
    have hh := h L J N A B t (T^((power+6)/2)) hN hNT hA hB hsep ht (by positivity)
    have hh' : ‖masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (coefficient js n:ℂ)) (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^(-power) :=
      hh.trans_eq (by rw [mul_div_assoc,he])
    exact (mul_le_mul_of_nonneg_left hh' (norm_nonneg _)).trans_eq (by ring)

/-- The genuine original Gamma multiplier remains inside the reflected
branch's time integral. Its continuity and uniform cap are supplied. -/
theorem dual_large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun y => (S y:ℂ)))
    (js : List ℕ) (Z r power : ℝ) (hZ : 0 ≤ Z) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi →
      ‖∫ t in Icc T (2*T), (phi t *
        PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) *
        masked L J N (fun y => (S y:ℂ)) (fun _ => 1) (fun _ => 1)
          (fun n => (coefficient js n:ℂ)) (fun s _ => T^((power+6)/2) ≤ (2:ℝ)^s)
          ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ)) t‖ ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := large_time S hm hlo hhi hleft hright hS js Z r power hr
  refine ⟨C*Real.exp (2*Z+7),by positivity,?_⟩
  filter_upwards [h,PRZZDualError.multiplier_scaled_cap Z hZ,
    PRZZScaledReplacement.shifts_eventually Z (1/4) (by norm_num)] with T h hgam hsmall
  intro L J N A B phi hN hNT hA hB hsep hphi
  have hTpos : 0 < T := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  have hcont := (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).continuous
  have hsep' : r ≤ ‖-B+-A‖ := by
    rw [show -B+-A = -(A+B) by ring,norm_neg]
    exact hsep
  have hh := h L J N (-B) (-A)
    (fun t => phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
    hN hNT (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA)
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

theorem family_split (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t X : ℝ) :
    PRZZAllPoissonRows.family L J N F F1 F2 a alpha beta t =
      masked L J N F F1 F2 a (fun s _ => ¬X ≤ (2:ℝ)^s) alpha beta t+
      masked L J N F F1 F2 a (fun s _ => X ≤ (2:ℝ)^s) alpha beta t := by
  rw [exhaustive L J N F F1 F2 a (fun s _ => X ≤ (2:ℝ)^s) alpha beta t]
  exact add_comm _ _

#print axioms masked_uniform
#print axioms large_time
#print axioms dual_large_time
#print axioms family_split
end XiPrime8845.PRZZLargeResolvedPruning
