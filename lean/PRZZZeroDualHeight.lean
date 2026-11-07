import PRZZDualJetMass
import PRZZZeroNativeTail
import PRZZKeptLiteral

/-! The TRUE Gamma dual profile in the zero-frequency time kernel.
All-order derivative masses are selected before height; smoothness alone
is not used to claim uniformity. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroDualHeight
open PRZZTimeAmplitude PRZZZeroGap PRZZFullWeightJets
set_option maxHeartbeats 8000000

theorem amplitude_eq (Phi : ℝ → ℂ) (T k : ℝ) (a b sigma : ℂ) (hT : 0 < T) :
    amplitude (PRZZKeptLiteral.dualProfile Phi T a b) T k sigma =
      PRZZDualTimeIBP.weight Phi T k a b sigma := by
  funext t
  unfold PRZZDualTimeIBP.weight amplitude PRZZMellinSeparation.scaledCutoff PRZZKeptLiteral.dualProfile
  rw [show T*(T⁻¹*t) = t by field_simp]
  ring

theorem convolution_linear (C D E : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    PRZZFullWeightJets.convolution C (fun j => D j+E j/s) n = PRZZFullWeightJets.convolution C D n+PRZZFullWeightJets.convolution C E n/s := by
  unfold PRZZFullWeightJets.convolution
  rw [Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The complete dual profile, including all Gamma derivatives, has the
same explicit quadratic shift singularity as the source amplitude. -/
theorem mass_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S rate : ℝ) (hS : 0 ≤ S) (hrate : 0 < rate) :
    ∃ U V : ℕ → ℝ, (∀ n, 0 ≤ U n ∧ 0 ≤ V n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        ∀ (n : ℕ) (k : ℝ) (sigma : ℂ), 0 < k → sigma ≠ 0 →
        (∫ t : ℝ, ‖iteratedDeriv n
          (amplitude (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
            T k sigma) t‖) ≤
          (U n+V n/‖sigma‖^2)*(k/(2*T))^(-rate)*T/T^n := by
  obtain ⟨C,D,E,hpos,hm⟩ := PRZZDualJetMass.all_mass Phi hPhi hcPhi hsPhi S rate hS hrate
  let U := fun n => Real.exp (2*S+7)*PRZZFullWeightJets.convolution PRZZDualJetTransfer.constant (PRZZFullWeightJets.convolution C D) n
  let V := fun n => Real.exp (2*S+7)*PRZZFullWeightJets.convolution PRZZDualJetTransfer.constant (PRZZFullWeightJets.convolution C E) n
  have hc (F G : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n) (n : ℕ) :
      0 ≤ PRZZFullWeightJets.convolution F G n := by
    unfold PRZZFullWeightJets.convolution
    exact Finset.sum_nonneg (fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hF i)) (hG (n-i)))
  have hU (n : ℕ) : 0 ≤ U n := mul_nonneg (Real.exp_pos _).le
    (hc _ _ PRZZDualJetTransfer.constant_nonneg
      (hc C D (fun n => (hpos n).1) (fun n => (hpos n).2.1)) n)
  have hV (n : ℕ) : 0 ≤ V n := mul_nonneg (Real.exp_pos _).le
    (hc _ _ PRZZDualJetTransfer.constant_nonneg
      (hc C E (fun n => (hpos n).1) (fun n => (hpos n).2.2)) n)
  refine ⟨U,V,fun n => ⟨hU n,hV n⟩,?_⟩
  filter_upwards [hm,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hm hsmall hT
  intro A B hA hB n k sigma hk hs
  rw [amplitude_eq Phi T k _ _ sigma (by linarith)]
  have hb := PRZZDualTimeIBP.leibniz_mass Phi hPhi hsPhi T k
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) sigma (by linarith) hk
    (hsmall.2 A hA) (hsmall.2 B hB) hs n
  have hh := hm A B hA hB n k sigma hk hs
  simp_rw [convolution_linear] at hh
  exact (hb.trans hh).trans_eq (by dsimp [U,V]; ring)

/-- Actual dual core, before any spatial cutoffs are discarded. -/
theorem core_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S rate : ℝ) (hS : 0 ≤ S) (hrate : 0 < rate) :
    ∃ U V : ℕ → ℝ, (∀ n, 0 ≤ U n ∧ 0 ≤ V n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        ∀ (n : ℕ) (p delta x : ℝ) (sigma : ℂ),
        0 < p → delta ≠ 0 → 0 < x → sigma ≠ 0 →
        ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
          T p sigma delta x‖ ≤
          x^(-(sigma.re+1))*(U n+V n/‖sigma‖^2)*((2*Real.pi*p*x^2)/(2*T))^(-rate)*
            T/T^n*(p*x)^n/|delta|^n := by
  obtain ⟨U,V,hpos,hm⟩ := mass_uniform Phi hPhi hcPhi hsPhi S rate hS hrate
  refine ⟨U,V,hpos,?_⟩
  filter_upwards [hm,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T hm hsmall hT
  intro A B hA hB n p delta x sigma hp hd hx hs
  have hT0 : 0 < T := by linarith
  have hk : 0 < 2*Real.pi*p*x^2 := by positivity
  have hf := PRZZDualTimeIBP.smooth Phi hPhi hsPhi T (2*Real.pi*p*x^2)
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) sigma hT0 hk (hsmall.2 A hA) (hsmall.2 B hB) hs
  have hc := PRZZDualTimeIBP.compact Phi hsPhi T (2*Real.pi*p*x^2)
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) sigma hT0
  rw [← amplitude_eq Phi T (2*Real.pi*p*x^2) _ _ sigma hT0] at hf hc
  have hb := PRZZDeltaDecay.oscillatory_bound _ hf hc n (delta/(p*x)) (div_ne_zero hd (by positivity))
  have hm' := hm A B hA hB n (2*Real.pi*p*x^2) sigma hk hs
  have hh := hb.trans (div_le_div_of_nonneg_right hm' (by positivity))
  rw [core,norm_mul,power_norm sigma x hx]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
  rw [abs_div,abs_of_pos (mul_pos hp hx),div_pow]
  field_simp

/-- The reflected source shift is the ACTUAL negative sum, while the
Gamma multiplier keeps the original A,B.  Both dependences are uniform. -/
theorem core_scaled_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hrate : 0 < rate) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
        ∀ (n : ℕ) (p delta x : ℝ), 0 < p → delta ≠ 0 → 0 < x →
        let sigma := -(A+B)/(Real.log T:ℂ)
        ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
          T p sigma delta x‖ ≤
          x^(-(sigma.re+1))*(C n*(1+(Real.log T)^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-rate)*
            T/T^n*(p*x)^n/|delta|^n := by
  obtain ⟨U,V,hpos,hb⟩ := core_uniform Phi hPhi hcPhi hsPhi S rate hS hrate
  refine ⟨fun n => U n+V n,fun n => add_nonneg (hpos n).1 (hpos n).2,?_⟩
  filter_upwards [hb,eventually_ge_atTop (2:ℝ)] with T hb hT
  intro A B hA hB hsep n p delta x hp hd hx
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : -(A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hab)
    (by exact_mod_cast hL.ne')
  have hh := hb A B hA hB n p delta x _ hp hd hx hs
  have he : V n/‖-(A+B)/(Real.log T:ℂ)‖^2 = V n*(Real.log T)^2/‖A+B‖^2 := by
    rw [norm_div,norm_neg,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  have hUn := (hpos n).1
  have hVn := (hpos n).2
  have hcoef : U n+V n*(Real.log T)^2/‖A+B‖^2 ≤
      (U n+V n)*(1+(Real.log T)^2/r^2) := by
    have hm : V n*(Real.log T)^2/‖A+B‖^2 ≤ V n*(Real.log T)^2/r^2 := by gcongr
    have hq : 0 ≤ (Real.log T)^2/r^2 := by positivity
    have hm' : V n*(Real.log T)^2/‖A+B‖^2 ≤ V n*((Real.log T)^2/r^2) := hm.trans_eq (by ring)
    nlinarith [mul_nonneg hUn hq]
  apply hh.trans
  gcongr

#print axioms core_scaled_uniform
#print axioms amplitude_eq
#print axioms convolution_linear
#print axioms mass_uniform
#print axioms core_uniform
end XiPrime8845.PRZZZeroDualHeight
