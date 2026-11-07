import PRZZWeightTail
import PRZZCutoffPhase
import PRZZDyadicArithmeticMass

/-! Source substitutions for the spatial derivative mass. The original
[M/2,3M] support and Delta cutoff supply the reciprocal phase radius.
The explicit envelope integral is retained, not replaced by an asserted
optimized PRZZ power. -/
noncomputable section
open scoped ContDiff BigOperators
open MeasureTheory Set
namespace XiPrime8845.PRZZSourceTailBudget
open PRZZSourceCutoffs PRZZFullWeightSmooth

theorem phase_radius (T M Q d eps delta u t x : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hx : M/2 ≤ x) (hu : Q/2 ≤ d*u) (ht : |t| ≤ 2*T)
    (hdelta : |delta| ≤ deltaCutoff T M Q eps/d) :
    |(delta*t/u)/x| ≤ 8*T^eps := by
  have hh := PRZZCutoffPhase.ratio_bound T M Q d eps delta x u hT hM hQ hd hx hu hdelta
  have he : (delta*t/u)/x = (delta/(x*u))*t := by ring
  rw [he,abs_mul]
  apply (mul_le_mul hh ht (abs_nonneg _) (by positivity)).trans_eq
  rw [Real.rpow_sub hT,Real.rpow_one]
  field_simp
  norm_num

/-- All derivative orders for the actual W argument 2*pi*u*x^2/(t*v).
No reciprocal-radius or derivative-bound hypothesis is supplied. -/
theorem source_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (T M Q d eps delta u v t : ℝ) (z sigma : ℂ),
      0 < T → 0 < M → 0 < Q → 0 < d → 0 < v → 0 < t →
      Q/2 ≤ d*u → |t| ≤ 2*T → |delta| ≤ deltaCutoff T M Q eps/d → sigma ≠ 0 →
      (∫ x, ‖iteratedDeriv n (weight F M (2*Real.pi*u/(t*v)) (delta*t/u) z sigma) x‖) ≤
        ∫ x in Icc (M/2) (3*M), PRZZFullWeightJets.envelope C D E a
          (2*Real.pi*u/(t*v)) x (8*T^eps) z sigma n/x^n := by
  obtain ⟨C,D,E,hpos,h⟩ := PRZZWeightFourier.mass_uniform (1/2) 3 (by norm_num) F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n T M Q d eps delta u v t z sigma hT hM hQ hd hv ht hu htt hdelta hsigma
  have hu0 : 0 < u := by nlinarith
  have hh := h n M (2*Real.pi*u/(t*v)) (delta*t/u) (8*T^eps) z sigma
    hM (by positivity) hsigma (by
      intro x hx
      exact phase_radius T M Q d eps delta u t x hT hM hQ hd
        (by linarith [hx.1]) hu htt hdelta)
  simpa only [show (1/2:ℝ)*M = M/2 by ring] using hh

/-- Finite arithmetic aggregation keeps each labelled coefficient, including
duplicates and masks. This is a norm inequality, not cancellation. -/
theorem finite_norm_bound {ι : Type*} (s : Finset ι) (c f : ι → ℂ) (B : ι → ℝ)
    (hb : ∀ i ∈ s, ‖f i‖ ≤ B i) :
    ‖∑ i ∈ s, c i*f i‖ ≤ ∑ i ∈ s, ‖c i‖*B i := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _)

/-- Weighted time integration of a finite arithmetic bound. Integrability
of the explicit budget is retained here; it is not an AFE exchange premise. -/
theorem weighted_time_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ℝ → ℂ) (B : ι → ℝ → ℝ) (Phi : ℝ → ℂ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (hb : ∀ t ∈ S, ∀ i ∈ s, ‖f i t‖ ≤ B i t)
    (hi : IntegrableOn (fun t => ‖Phi t‖*(∑ i ∈ s, ‖c i‖*B i t)) S) :
    ‖∫ t in S, Phi t*(∑ i ∈ s, c i*f i t)‖ ≤
      ∫ t in S, ‖Phi t‖*(∑ i ∈ s, ‖c i‖*B i t) := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
  filter_upwards [ae_restrict_mem hS] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (finite_norm_bound s c (fun i => f i t)
    (fun i => B i t) (hb t ht)) (norm_nonneg _)

/-- Arithmetic pair masks survive the time integration. The coefficient
mass is supplied, not left as sum |c| or bounded by a pair cardinality.
The common analytic budget B and its time integrability remain explicit. -/
theorem arithmetic_time (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l))
    (u : ℕ × ℕ → ℝ → ℂ) (B : ℝ → ℝ) (Phi : ℝ → ℂ) (S : Set ℝ)
    (hS : MeasurableSet S) (hB : ∀ t ∈ S, 0 ≤ B t)
    (hu : ∀ t ∈ S, ∀ p ∈ s, ‖u p t‖ ≤ B t)
    (hi : IntegrableOn (fun t => ‖Phi t‖*B t) S) :
    ‖∫ t in S, Phi t*(∑ p ∈ s,
      (((PRZZGCoefficient.coefficient js p.1:ℂ)*star (PRZZGCoefficient.coefficient js p.2:ℂ))*u p t)/
        ((p.1:ℂ)*(p.2:ℂ)))‖ ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*(∫ t in S, ‖Phi t‖*B t) := by
  rw [← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (hi.const_mul _)
  filter_upwards [ae_restrict_mem hS] with t ht
  rw [norm_mul]
  have hh := (norm_sum_le _ _).trans
    (PRZZDyadicArithmeticMass.weighted_pair_mass js N j l hN s hs
      (fun p => u p t) (B t) (hB t ht) (hu t ht))
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

/-- Compact source time window: a common scalar analytic bound needs no
additional time-integrability premise. The analytic scalar is still explicit. -/
theorem arithmetic_time_compact (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l))
    (u : ℕ × ℕ → ℝ → ℂ) (B T : ℝ) (hB : 0 ≤ B)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hu : ∀ t ∈ Icc T (2*T), ∀ p ∈ s, ‖u p t‖ ≤ B) :
    ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ p ∈ s,
      (((PRZZGCoefficient.coefficient js p.1:ℂ)*star (PRZZGCoefficient.coefficient js p.2:ℂ))*u p t)/
        ((p.1:ℂ)*(p.2:ℂ)))‖ ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*B*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  have hc : Continuous (fun t : ℝ => ‖Phi (t/T)‖*B) := by fun_prop
  have hh := arithmetic_time js N j l hN s hs u (fun _ => B) (fun t => Phi (t/T))
    (Icc T (2*T)) measurableSet_Icc (fun _ _ => hB) hu
    (hc.continuousOn.integrableOn_compact isCompact_Icc)
  exact hh.trans_eq (by rw [integral_mul_const]; ring)

#print axioms arithmetic_time_compact
#print axioms arithmetic_time
#print axioms phase_radius
#print axioms source_mass
#print axioms finite_norm_bound
#print axioms weighted_time_bound
end XiPrime8845.PRZZSourceTailBudget
