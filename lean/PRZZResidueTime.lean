import PRZZResidueEnvelope
import PRZZScaledReplacement
import PRZZContourAFE

/-! The actual four noncentral AFE residues, summed and time weighted.
The Gaussian remainder is explicit. This is not a bound for the dual
Gamma multiplier, phase linearization, or Poisson truncation errors. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace XiPrime8845.PRZZResidueTime
open PRZZAFEDual PRZZFiniteContour PRZZContourAFE PRZZNoncentralResidues
set_option maxHeartbeats 3000000

def envelope (sigma : ℂ) (t : ℝ) : ℝ :=
  (1+4*(t+2)^2/‖sigma‖^2)*(228+96*t)*Real.exp (1-t^2/2+2*Real.pi*t)

theorem noncentral_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ t : ℝ, 1 ≤ t →
      ‖noncentralSum a b t‖ ≤ C*envelope (a+b) t := by
  classical
  obtain ⟨L,hL,hl⟩ := PRZZResidueEnvelope.actual_left_residues
  obtain ⟨R,hR,hr⟩ := PRZZResidueEnvelope.actual_right_residues
  refine ⟨5*(L+R),by positivity,?_⟩
  intro a b ha hb hs t ht
  have hE : 0 ≤ envelope (a+b) t := by unfold envelope; positivity
  have hEL : L*(1+4*(t+2)^2/‖a+b‖^2)*(228+96*t)*Real.exp (1-t^2/2+2*Real.pi*t) ≤
      (L+R)*envelope (a+b) t := by
    calc
      _ = L*envelope (a+b) t := by unfold envelope; ring
      _ ≤ _ := by nlinarith
  have hER : R*(1+4*(t+2)^2/‖a+b‖^2)*(228+96*t)*Real.exp (1-t^2/2+2*Real.pi*t) ≤
      (L+R)*envelope (a+b) t := by
    calc
      _ = R*envelope (a+b) t := by unfold envelope; ring
      _ ≤ _ := by nlinarith
  have hleft := small_shift_residues a b t ha hb ht (leftArg a t) (rightArg b t)
    (Or.inl ⟨rfl,rfl⟩)
  have hright := small_shift_residues a b t ha hb ht (rightArg b t) (leftArg a t)
    (Or.inr ⟨rfl,rfl⟩)
  have hres (p : ℂ) (hp : p ∈ (poleSet a b t).erase 0) :
      ‖residue (integrand a b t) p‖ ≤ (L+R)*envelope (a+b) t := by
    have hp0 := (Finset.mem_erase.mp hp).1
    have hp' := (Finset.mem_erase.mp hp).2
    unfold integrand
    simp only [poleSet,Finset.mem_insert,Finset.mem_singleton] at hp'
    rcases hp' with hp' | rfl | rfl | rfl | rfl
    · exact (hp0 hp').elim
    · rw [residue_eq_of_tendsto hleft.1]
      simp only [neg_mul,norm_neg]
      have hh := hl a b ha hb hs t ht (-leftArg a t) (Or.inl rfl)
      simpa only [sub_eq_add_neg] using hh.trans hEL
    · rw [residue_eq_of_tendsto hleft.2]
      exact (hl a b ha hb hs t ht (1-leftArg a t) (Or.inr rfl)).trans hEL
    · rw [residue_eq_of_tendsto hright.1]
      simp only [neg_mul,norm_neg]
      have hh := hr a b ha hb hs t ht (-rightArg b t) (Or.inl rfl)
      simpa only [sub_eq_add_neg] using hh.trans hER
    · rw [residue_eq_of_tendsto hright.2]
      exact (hr a b ha hb hs t ht (1-rightArg b t) (Or.inr rfl)).trans hER
  have hc : ((poleSet a b t).erase 0).card ≤ 5 := by
    apply (Finset.card_erase_le).trans
    unfold poleSet
    exact (Finset.card_insert_le _ _).trans (by
      have h1 := Finset.card_insert_le (-leftArg a t) {1-leftArg a t,-rightArg b t,1-rightArg b t}
      have h2 := Finset.card_insert_le (1-leftArg a t) {-rightArg b t,1-rightArg b t}
      have h3 := Finset.card_insert_le (-rightArg b t) {1-rightArg b t}
      simp only [Finset.card_singleton] at h3
      omega)
  unfold noncentralSum
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hres).trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hcr : (((poleSet a b t).erase 0).card:ℝ) ≤ 5 := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hcr (mul_nonneg (by positivity : 0 ≤ L+R) hE)]

/-- Gaussian envelope integrated with the literal finite mollifier.
Neither a residue estimate nor a coefficient mass is assumed. -/
theorem weighted_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T : ℝ, 1 ≤ T →
    ∀ js : List ℕ, ∀ N : ℕ, 1 ≤ N → ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t*noncentralSum a b t‖ ≤
      C*(4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js))*
        ∫ t in Icc T (2*T), ‖phi t‖*envelope (a+b) t := by
  obtain ⟨C,hC,h⟩ := noncentral_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T hT js N hN phi hphi
  let M := 4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hc : Continuous (fun t : ℝ => (C*M)*(‖phi t‖*envelope (a+b) t)) := by
    unfold envelope; fun_prop
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t in Icc T (2*T), (C*M)*(‖phi t‖*envelope (a+b) t) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hc.integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul]
      exact (mul_le_mul (PRZZReplacementMass.source_weight_bound js N hN phi t)
        (h a b ha hb hs t (hT.trans ht.1)) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [M]; ring)
    _ = _ := by rw [integral_const_mul]

def timeCost (sigma : ℂ) (T : ℝ) : ℝ :=
  (1+64*T^2/‖sigma‖^2)*420*T^2*Real.exp (-T^2/4)

theorem window_envelope (sigma : ℂ) (T t : ℝ) (hT : 16*Real.pi+4 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    envelope sigma t ≤ (1+64*T^2/‖sigma‖^2)*(420*T)*Real.exp (-T^2/4) := by
  have hT1 : 1 ≤ T := by linarith [Real.pi_pos]
  have ht0 : 0 ≤ t := by linarith
  have he : 1-t^2/2+2*Real.pi*t ≤ -T^2/4 := by
    have hh := mul_nonneg ht0 (show 0 ≤ t-16*Real.pi by linarith)
    have hsq : T^2 ≤ t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ t+T by linarith)]
    have ht4 : 4 ≤ t := by linarith [Real.pi_pos]
    nlinarith [sq_nonneg (t-4)]
  have hp : 4*(t+2)^2 ≤ 64*T^2 := by nlinarith
  have hlin : 228+96*t ≤ 420*T := by linarith
  unfold envelope
  apply mul_le_mul _ (Real.exp_le_exp.mpr he) (by positivity) (by positivity)
  apply mul_le_mul _ hlin (by positivity) (by positivity)
  exact add_le_add_right (div_le_div_of_nonneg_right hp (sq_nonneg _)) 1

/-- Evaluates the remaining outer mass using the actual time interval. -/
theorem envelope_integral (sigma : ℂ) (T P : ℝ) (hT : 16*Real.pi+4 ≤ T)
    (hP : 0 ≤ P) (phi : ℝ → ℂ)
    (hp : ∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) :
    (∫ t in Icc T (2*T), ‖phi t‖*envelope sigma t) ≤ P*timeCost sigma T := by
  have hT0 : 0 ≤ T := by linarith [Real.pi_pos]
  let B := (1+64*T^2/‖sigma‖^2)*(420*T)*Real.exp (-T^2/4)
  have hi : IntegrableOn (fun _ : ℝ => P*B) (Icc T (2*T)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh : (∫ t in Icc T (2*T), ‖phi t‖*envelope sigma t) ≤
      ∫ _t in Icc T (2*T), P*B := by
    have hnon : 0 ≤ᵐ[volume.restrict (Icc T (2*T))]
        (fun t => ‖phi t‖*envelope sigma t) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : 0 ≤ t := hT0.trans ht.1
      change 0 ≤ ‖phi t‖*envelope sigma t
      unfold envelope; positivity
    apply integral_mono_of_nonneg hnon hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul (hp t ht) (window_envelope sigma T t hT ht.1 ht.2)
      (by have ht0 := hT0.trans ht.1; unfold envelope; positivity) hP
  apply hh.trans_eq
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ 2*T-T by linarith),smul_eq_mul]
  dsimp [B,timeCost]
  ring

/-- Exact pointwise bookkeeping in the proved series AFE. The dual
Gamma series is retained, so it is not silently replaced by its W model. -/
theorem direct_afe_defect (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) :
    riemannZeta (leftArg a t)*riemannZeta (rightArg b t) -
      ((∑' p : ℕ × ℕ, PRZZL1Finite.directTerm a b (PRZZActualDirectSum.mainWeight a b)
        t (p.1+1) (p.2+1)) + dualMultiplier a b t*PRZZIntegratedAFE.series (-b) (-a) t) =
      PRZZReplacementIntegral.difference a b t - noncentralSum a b t := by
  rw [PRZZSeriesAFE.series_afe a b t ha hb hs ht]
  unfold PRZZReplacementIntegral.difference PRZZIntegratedAFE.series
  ring

/-- Aggregate the two actual error integrals. The residue Gaussian mass
is retained explicitly; this does not identify the full post-Poisson error. -/
theorem scaled_combined (js : List ℕ) (S r delta : ℝ) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      let a := A/(Real.log T:ℂ)
      let b := B/(Real.log T:ℂ)
      let w := PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N
      ‖(∫ t in Icc T (2*T), w t*PRZZReplacementIntegral.difference a b t) -
        (∫ t in Icc T (2*T), w t*noncentralSum a b t)‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T +
          R*(4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js))*
            ∫ t in Icc T (2*T), ‖phi t‖*envelope (a+b) t := by
  obtain ⟨C,hC,hc⟩ := PRZZScaledReplacement.scaled_target js S r delta hr hd
  obtain ⟨R,hR,hrb⟩ := weighted_bound
  refine ⟨C,R,hC,hR,?_⟩
  filter_upwards [hc,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Filter.eventually_ge_atTop (1:ℝ)] with T hc hsmall hT
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hab (by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1]))
  exact (norm_sub_le _ _).trans (add_le_add
    (hc A B hA hB hsep N hN hNT phi P hphi hP hp)
    (hrb _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs T hT js N hN phi hphi))

/-- The combined bound with the residue time integral evaluated. The
dual Gamma series and the subsequent phase/Poisson errors remain separate. -/
theorem scaled_combined_explicit (js : List ℕ) (S r delta : ℝ)
    (hr : 0 < r) (hd : 0 < delta) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      let a := A/(Real.log T:ℂ)
      let b := B/(Real.log T:ℂ)
      let w := PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N
      ‖(∫ t in Icc T (2*T), w t*PRZZReplacementIntegral.difference a b t) -
        (∫ t in Icc T (2*T), w t*noncentralSum a b t)‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T +
          R*(4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js))*
            (P*timeCost (a+b) T) := by
  obtain ⟨C,R,hC,hR,h⟩ := scaled_combined js S r delta hr hd
  refine ⟨C,R,hC,hR,?_⟩
  filter_upwards [h,Filter.eventually_ge_atTop (16*Real.pi+4)] with T h hT
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have hn : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact (h A B hA hB hsep N hN hNT phi P hphi hP hp).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (envelope_integral _ T P hT hP phi hp) (by positivity)) _)

#print axioms scaled_combined_explicit
#print axioms noncentral_bound
#print axioms weighted_bound
#print axioms direct_afe_defect
#print axioms scaled_combined
#print axioms window_envelope
#print axioms envelope_integral
end XiPrime8845.PRZZResidueTime
