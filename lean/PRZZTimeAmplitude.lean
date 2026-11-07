import PRZZTimeJets
import PRZZFullWeightJets
import PRZZArithmeticMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Time-cutoff assembly for sourceW(sigma,k/t). Constants precede T,k
and sigma. The local product ratio is retained in the derivative mass. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology
namespace XiPrime8845.PRZZTimeAmplitude
open PRZZFullWeightJets PRZZMellinSeparation
set_option maxHeartbeats 3000000

def amplitude (F : ℝ → ℂ) (T k : ℝ) (sigma : ℂ) (t : ℝ) : ℂ :=
  scaledCutoff F T t * PRZZTimeJets.reciprocal sigma k t

theorem uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (T k t : ℝ) (sigma : ℂ),
      0 < k → 0 < t → sigma ≠ 0 →
      ‖iteratedDeriv n (amplitude F T k sigma) t‖ ≤
        PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*(k/t)^(-a)/t^n := by
  choose C hC hcut using PRZZCutoffJets.scaled_uniform F hF hsF
  choose D E hD hE htime using (fun n => PRZZTimeJets.scaled_bound n a ha)
  refine ⟨C,D,E,fun n => ⟨hC n,hD n,hE n⟩,?_⟩
  intro n T k t sigma hk ht hs
  have hf : ContDiffAt ℝ ∞ (scaledCutoff F T) t :=
    (hF.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hg : ContDiffAt ℝ ∞ (PRZZTimeJets.reciprocal sigma k) t := by
    apply (PRZZFullWeightSmooth.source_smooth sigma hs).contDiffAt
      (Ioi_mem_nhds (div_pos hk ht)) |>.comp t
    exact contDiffAt_const.div contDiffAt_id ht.ne'
  have low : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hh := product_bound (scaledCutoff F T) (PRZZTimeJets.reciprocal sigma k) n t
    (hf.of_le low) (hg.of_le low) C
    (fun i => (D i+E i/‖sigma‖^2)*(k/t)^(-a))
    (fun i _ => hcut i T t) (fun i _ => htime i sigma hs k t hk ht)
  have he : PRZZFullWeightJets.convolution C (fun i => (D i+E i/‖sigma‖^2)*(k/t)^(-a)) n =
      PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*(k/t)^(-a) := by
    unfold PRZZFullWeightJets.convolution
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hh
  change t^n * ‖iteratedDeriv n (amplitude F T k sigma) t‖ ≤ _ at hh
  exact (le_div_iff₀ (pow_pos ht n)).mpr (by simpa only [mul_comm] using hh)

/-- On the actual time window the local ratio is frozen at its worst
endpoint. No supremum depending on height is introduced. -/
theorem window_bound (a k T t B : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hk : 0 < k) (hT : 0 < T) (ht : t ∈ Icc T (2*T)) (hB : 0 ≤ B) :
    B*(k/t)^(-a)/t^n ≤ B*(k/(2*T))^(-a)/T^n := by
  have ht0 : 0 < t := hT.trans_le ht.1
  have hrat : k/(2*T) ≤ k/t := by gcongr; exact ht.2
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < k/(2*T)) hrat (by linarith : -a ≤ 0)
  exact div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
    (mul_le_mul_of_nonneg_left hp hB) (pow_pos hT n) (pow_le_pow_left₀ hT.le ht.1 n)

/-- L1 mass on [T,2T], with every derivative constant supplied by the
fixed cutoff and the reciprocal source kernel. -/
theorem mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (T k : ℝ) (sigma : ℂ), 0 < T → 0 < k → sigma ≠ 0 →
      (∫ t in Icc T (2*T), ‖iteratedDeriv n (amplitude F T k sigma) t‖) ≤
        PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*(k/(2*T))^(-a)*T/T^n := by
  obtain ⟨C,D,E,hpos,h⟩ := uniform F hF hsF a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n T k sigma hT hk hs
  let B := PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n
  have hB : 0 ≤ B := by
    unfold B PRZZFullWeightJets.convolution
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
      (add_nonneg (hpos (n-i)).2.1 (div_nonneg (hpos (n-i)).2.2 (sq_nonneg _)))
  have hb : ∀ t ∈ Icc T (2*T), ‖iteratedDeriv n (amplitude F T k sigma) t‖ ≤
      B*(k/(2*T))^(-a)/T^n := by
    intro t ht
    exact (h n T k t sigma hk (hT.trans_le ht.1) hs).trans
      (window_bound a k T t B n ha.le hk hT ht hB)
  have hi : IntegrableOn (fun _ : ℝ => B*(k/(2*T))^(-a)/T^n) (Icc T (2*T)) :=
    continuous_const.integrableOn_Icc
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hb t ht)).trans_eq
  simp [integral_const,Measure.real,Real.volume_Icc,show 0 ≤ 2*T-T by linarith,B]
  <;> ring

theorem jet_support (F : ℝ → ℂ) (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (sigma : ℂ) (hT : 0 < T) (n : ℕ) :
    tsupport (iteratedDeriv n (amplitude F T k sigma)) ⊆ Icc T (2*T) := by
  induction n with
  | zero =>
    apply closure_minimal _ isClosed_Icc
    intro t ht
    have hf : F (T⁻¹*t) ≠ 0 := by
      intro hz
      exact ht (by simp [amplitude,scaledCutoff,hz])
    have hh := hF hf
    have he : T*(T⁻¹*t) = t := by field_simp
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hT.le,
      mul_le_mul_of_nonneg_left hh.2 hT.le]
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- The cutoff removes the apparent singularity at time zero. -/
theorem smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (sigma : ℂ) (hT : 0 < T) (hk : 0 < k) (hs : sigma ≠ 0) :
    ContDiff ℝ ∞ (amplitude F T k sigma) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hf : ContDiffAt ℝ ∞ (scaledCutoff F T) t :=
      (hF.comp (contDiff_const.mul contDiff_id)).contDiffAt
    have hg : ContDiffAt ℝ ∞ (PRZZTimeJets.reciprocal sigma k) t := by
      apply (PRZZFullWeightSmooth.source_smooth sigma hs).contDiffAt
        (Ioi_mem_nhds (div_pos hk ht)) |>.comp t
      exact contDiffAt_const.div contDiffAt_id ht.ne'
    exact hf.mul hg
  · have htT : t < T := by linarith
    have he : amplitude F T k sigma =ᶠ[nhds t] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds htT] with y hy
      by_contra hh
      have hh' := jet_support F hsupp T k sigma hT 0 (subset_closure hh)
      exact (not_le.mpr hy) hh'.1
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem compact (F : ℝ → ℂ) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (sigma : ℂ) (hT : 0 < T) :
    HasCompactSupport (amplitude F T k sigma) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro t ht
  by_contra hh
  exact ht (jet_support F hsupp T k sigma hT 0 (subset_closure hh))

theorem jet_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (sigma : ℂ) (hT : 0 < T) (hk : 0 < k) (hs : sigma ≠ 0) (n : ℕ) :
    Integrable (iteratedDeriv n (amplitude F T k sigma)) := by
  exact ((smooth F hF hsupp T k sigma hT hk hs).continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ (compact F hsupp T k sigma hT) n)

theorem mass_window (F : ℝ → ℂ) (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (sigma : ℂ) (hT : 0 < T) (n : ℕ) :
    (∫ t, ‖iteratedDeriv n (amplitude F T k sigma) t‖) =
      ∫ t in Icc T (2*T), ‖iteratedDeriv n (amplitude F T k sigma) t‖ := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : iteratedDeriv n (amplitude F T k sigma) t = 0 := by
    by_contra hh
    exact ht (jet_support F hF T k sigma hT n (subset_closure hh))
  rw [hz,norm_zero]

/-- Coefficients and local product scales are retained term by term.
The constants are selected before the finite arithmetic set and height. -/
theorem coefficient_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (T : ℝ) (sigma : ℂ), 0 < T → sigma ≠ 0 →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (R : ℕ × ℕ → ℝ),
      (∀ p ∈ s, 0 < R p) →
      (∑ p ∈ s, ‖c p‖*(∫ t, ‖iteratedDeriv n
        (amplitude F T (2*Real.pi*R p) sigma) t‖)) ≤
      ∑ p ∈ s, ‖c p‖*PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*
        (2*Real.pi*R p/(2*T))^(-a)*T/T^n := by
  obtain ⟨C,D,E,hpos,h⟩ := mass F hF hsF a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n T sigma hT hs s c R hR
  apply Finset.sum_le_sum
  intro p hp
  have hRp := hR p hp
  rw [mass_window F hsupp T (2*Real.pi*R p) sigma hT n]
  exact (mul_le_mul_of_nonneg_left
    (h n T (2*Real.pi*R p) sigma hT (by positivity) hs)
    (norm_nonneg _)).trans_eq (by ring)

/-- Actual convolution coefficients, preserving each local R and every
mask in s. No cardinality replacement or coefficient-bound premise. -/
theorem arithmetic_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n N : ℕ) (js : List ℕ) (T : ℝ) (sigma : ℂ),
      1 ≤ N → 0 < T → sigma ≠ 0 →
      ∀ (s : Finset (ℕ × ℕ)) (R : ℕ × ℕ → ℝ),
      (∀ p ∈ s, p.1 ∈ Finset.Icc 1 N ∧ p.2 ∈ Finset.Icc 1 N) →
      (∀ p ∈ s, 0 < R p) →
      (∑ p ∈ s, ‖(PRZZGCoefficient.coefficient js p.1:ℂ)*
        star (PRZZGCoefficient.coefficient js p.2:ℂ)‖*(∫ t, ‖iteratedDeriv n
        (amplitude F T (2*Real.pi*R p) sigma) t‖)) ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*
        ∑ p ∈ s, PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*
          (2*Real.pi*R p/(2*T))^(-a)*T/T^n := by
  obtain ⟨C,D,E,hpos,h⟩ := coefficient_mass F hF hsF hsupp a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n N js T sigma hN hT hs s R hidx hR
  apply (h n T sigma hT hs s _ R hR).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hm := Finset.mem_Icc.mp (hidx p hp).1
  have hn := Finset.mem_Icc.mp (hidx p hp).2
  have hb := PRZZArithmeticMass.pair_bound js N p.1 p.2 hN hm.1 hm.2 hn.1 hn.2
  have hRp := hR p hp
  have hc : 0 ≤ PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n := by
    unfold PRZZFullWeightJets.convolution
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
      (add_nonneg (hpos (n-i)).2.1 (div_nonneg (hpos (n-i)).2.2 (sq_nonneg _)))
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n*
      (2*Real.pi*R p/(2*T))^(-a)*T/T^n by positivity)
  convert hh using 1 <;> ring

#print axioms arithmetic_mass
#print axioms smooth
#print axioms compact
#print axioms jet_integrable
#print axioms coefficient_mass
#print axioms jet_support
#print axioms mass_window
#print axioms mass
#print axioms uniform
#print axioms window_bound
end XiPrime8845.PRZZTimeAmplitude
