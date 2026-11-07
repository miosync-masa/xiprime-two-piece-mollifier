import PRZZSourceTailMass
import PRZZExplicitDomain

/-! Exact finite AFE partition and explicit outer-label cost. The label
includes d, signed Delta, j and l; the spatial scale has a separate index.
The coarse count below is suitable for arbitrary-power tails, not for the
main DI estimate. Its L dependence must not be suppressed in cutoff removal. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory Set
namespace XiPrime8845.PRZZAFEOuterAssembly
open PRZZAFEIndices PRZZQuotientMass
set_option maxHeartbeats 3000000

theorem partition_explicit (L N K : ℕ) (F : ℝ → ℂ) (M : ℝ)
    (hM : 0 < M) (hM1 : M ≤ 1) (hcover : (L:ℝ) ≤ (2:ℝ)^K*M/2)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (f : PRZZAFEIndices.Index → ℂ) :
    (∑ i ∈ indices L N, f i) =
      ∑ k ∈ range K, ∑ z ∈ labels L N, ∑ p ∈ PRZZExplicitDomain.domain L N z,
        PRZZAFEProgression.piece F ((2:ℝ)^k*M) p.1 * f (restore z p) := by
  rw [grouped, PRZZGroupedTime.partition_grouped L N K F M hM hM1 hcover hlo hhi]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro z hz
  simpa only [restore] using PRZZExplicitDomain.fibre_explicit L N z
    (fun i => PRZZAFEProgression.piece F ((2:ℝ)^k*M) i.1.1*f i)

/-- The original finite mollified AFE, with its literal analytic weight.
Both sharp AFE cutoffs survive in the explicit congruence domain. -/
theorem literal_partition (L N K : ℕ) (F : ℝ → ℂ) (M : ℝ)
    (hM : 0 < M) (hM1 : M ≤ 1) (hcover : (L:ℝ) ≤ (2:ℝ)^K*M/2)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (a b : ℕ → ℂ) (alpha beta : ℂ) (V : ℕ → ℝ → ℂ) (t : ℝ) :
    PRZZL1Finite.directSum L alpha beta V t *
      PRZZ.dirichletPolynomial a N (1/2+t*Complex.I) *
      star (PRZZ.dirichletPolynomial b N (1/2+t*Complex.I)) =
      ∑ k ∈ range K, ∑ z ∈ labels L N, ∑ p ∈ PRZZExplicitDomain.domain L N z,
        PRZZAFEProgression.piece F ((2:ℝ)^k*M) p.1 *
          PRZZL1Finite.term a b alpha beta V t
            (restore z p).1.1 (restore z p).1.2 (restore z p).2.1 (restore z p).2.2 := by
  rw [direct_grouped, ← grouped]
  exact partition_explicit L N K F M hM hM1 hcover hlo hhi _

theorem label_count (L N : ℕ) : (labels L N).card ≤ L^2*N^2 := by
  have hh := card_image_le (s := indices L N) (f := label)
  simpa [labels,indices,card_product,Nat.card_Icc,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

/-- All four outer labels and the spatial partition are charged once.
This is a coarse finite tail count, not a claim about an infinite L limit. -/
theorem outer_sum (L N K : ℕ) (E : ℕ → Label → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ k ∈ range K, ∀ z ∈ labels L N, ‖E k z‖ ≤ B) :
    ‖∑ k ∈ range K, ∑ z ∈ labels L N, E k z‖ ≤ (K:ℝ)*L^2*N^2*B := by
  have hh : ‖∑ k ∈ range K, ∑ z ∈ labels L N, E k z‖ ≤
      (K:ℝ)*(labels L N).card*B := by
    calc
      _ ≤ ∑ k ∈ range K, ∑ z ∈ labels L N, ‖E k z‖ :=
        (norm_sum_le _ _).trans (sum_le_sum (fun k hk => norm_sum_le _ _))
      _ ≤ ∑ k ∈ range K, ∑ z ∈ labels L N, B := by
        exact sum_le_sum (fun k hk => sum_le_sum (fun z hz => hE k hk z hz))
      _ = _ := by simp; ring
  apply hh.trans
  have hc : ((labels L N).card:ℝ) ≤ (L:ℝ)^2*N^2 := by exact_mod_cast label_count L N
  nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ (K:ℝ)*B by positivity)]

/-- Polynomially bounded cutoffs consume an explicit part of the chosen
tail order. No height-dependent constant or L-uniform estimate is asserted. -/
theorem outer_absorbed (L N K : ℕ) (T lambda kappa A C : ℝ)
    (E : ℕ → Label → ℂ) (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hL : (L:ℝ) ≤ T^lambda) (hK : (K:ℝ) ≤ T^kappa) (hN : (N:ℝ) ≤ T)
    (hE : ∀ k ∈ range K, ∀ z ∈ labels L N,
      ‖E k z‖ ≤ C*T^(-(A+kappa+2*lambda+2))) :
    ‖∑ k ∈ range K, ∑ z ∈ labels L N, E k z‖ ≤ C*T^(-A) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  apply (outer_sum L N K E _ (by positivity) hE).trans
  calc
    _ ≤ T^kappa*(T^lambda)^2*T^2*(C*T^(-(A+kappa+2*lambda+2))) := by gcongr
    _ = _ := by
      rw [← Real.rpow_natCast (T^lambda) 2, ← Real.rpow_mul hT0.le,
        ← Real.rpow_natCast T 2]
      norm_num only [Nat.cast_ofNat]
      rw [show T^kappa*T^(lambda*(2:ℝ))*T^(2:ℝ)*(C*T^(-(A+kappa+2*lambda+2))) =
        C*((T^kappa*T^(lambda*(2:ℝ))*T^(2:ℝ))*T^(-(A+kappa+2*lambda+2))) by ring]
      simp only [← Real.rpow_add hT0]
      congr 2
      ring

/-- The complete finite outer sum is kept inside the time integral. -/
theorem outer_time_absorbed (L N K : ℕ) (T lambda kappa A C : ℝ)
    (E : ℕ → Label → ℝ → ℂ) (w : ℝ → ℂ) (hw : Continuous w)
    (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hL : (L:ℝ) ≤ T^lambda) (hK : (K:ℝ) ≤ T^kappa) (hN : (N:ℝ) ≤ T)
    (hE : ∀ t ∈ Icc T (2*T), ∀ k ∈ range K, ∀ z ∈ labels L N,
      ‖E k z t‖ ≤ C*T^(-(A+kappa+2*lambda+2))) :
    ‖∫ t in Icc T (2*T), w t * ∑ k ∈ range K, ∑ z ∈ labels L N, E k z t‖ ≤
      C*T^(-A)*(∫ t in Icc T (2*T), ‖w t‖) := by
  have hc : Continuous (fun t => C*T^(-A)*‖w t‖) := continuous_const.mul hw.norm
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    hc.integrableOn_Icc ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (outer_absorbed L N K T lambda kappa A C (fun k z => E k z t)
        hT hC hL hK hN (hE t ht)) (norm_nonneg _)).trans_eq (mul_comm _ _)

#print axioms outer_time_absorbed
#print axioms partition_explicit
#print axioms literal_partition
#print axioms label_count
#print axioms outer_sum
#print axioms outer_absorbed
end XiPrime8845.PRZZAFEOuterAssembly
