import FengResidual
import FengLogEndpoint

/-! Endpoint-safe shared-block bounds for growing g. The Euler envelope is
not a claim that the shared block is negligible or has a limiting profile. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSharedBounds
open FengAtG FengSharedBlock FengResidual CoprimeShift ShiftWeights
open ShiftedEndpoint WeightedMobius SupportTail SupportProductTail CoprimeEndpoint
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem euler_mono_support (h g : ℕ) (hh : h ≠ 0) (hg : g ≠ 0)
    (hd : ∀ p : ℕ, p.Prime → p ∣ h → p ∣ g) :
    eulerMass h 0 ≤ eulerMass g 0 := by
  apply le_of_tendsto_of_tendsto (EulerHead.mass_tendsto h hh) (EulerHead.mass_tendsto g hg)
  apply Filter.Eventually.of_forall
  intro Q
  unfold EulerHead.mass supportedSum
  apply sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨hr,hs⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨hr,fun p hp hpr => hd p hp (hs p hp hpr)⟩
  · intros; positivity

theorem residual_modulus_euler (g p : ℕ) (hg : g ≠ 0) (hp : p ∈ g.primeFactors) :
    eulerMass ((g/p^(g.factorization p))*p) 0 ≤ eulerMass g 0 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  apply euler_mono_support _ g (mul_ne_zero (Nat.ordCompl_pos p hg).ne' hprime.ne_zero) hg
  intro q hq hqd
  rcases hq.dvd_mul.mp hqd with h | h
  · exact h.trans (Nat.ordCompl_dvd g p)
  · exact h.trans (Nat.dvd_of_mem_primeFactors hp)

theorem prime_log_square_sum (g : ℕ) (hg : g ≠ 0) :
    (∑ p ∈ g.primeFactors, (Real.log p)^2) ≤ (Real.log g)^2 := by
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hg)
  calc
    _ ≤ ∑ p ∈ g.primeFactors, Real.log g*Real.log p := by
      apply sum_le_sum
      intro p hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
      have hpg : (p:ℝ) ≤ g := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mem_primeFactors hp)
      have hl := Real.log_le_log hp0 hpg
      have hn := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      nlinarith
    _ = Real.log g*(∑ p ∈ g.primeFactors, Real.log p) := (mul_sum ..).symm
    _ ≤ (Real.log g)^2 := by
      have := mul_le_mul_of_nonneg_left (ShiftedEulerUniform.prime_log_sum_le g hg) hlogg
      nlinarith

theorem reciprocal_power_sum (p M : ℕ) (hp : p.Prime) :
    (∑ a ∈ range M, 1/((p^a:ℕ):ℝ)) ≤ 2 := by
  have hhalf : ∀ M : ℕ, (∑ a ∈ range M, (1/2:ℝ)^a) = 2-2*(1/2:ℝ)^M := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ,ih,pow_succ]; ring
  calc
    _ ≤ ∑ a ∈ range M, (1/2:ℝ)^a := by
      apply sum_le_sum
      intro a ha
      have h : (2:ℝ)^a ≤ (p:ℝ)^a := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp.two_le) a
      have hd := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^a) h
      simpa only [Nat.cast_pow,div_pow,one_pow] using hd
    _ ≤ 2 := by rw [hhalf]; nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) M]

theorem power_cutoff_mem (p a : ℕ) (hp : p.Prime) (L u : ℝ)
    (hL : 0 < L) (hu : 0 ≤ u) (ha : a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1)) :
    p^a ∈ Icc 1 ⌊Real.exp (L*u)⌋₊ := by
  have hN : 1 ≤ ⌊Real.exp (L*u)⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    simpa using Real.one_le_exp (mul_nonneg hL.le hu)
  exact mem_Icc.mpr ⟨pow_pos hp.pos _,Nat.pow_le_of_le_log (by omega) (by simpa using ha)⟩

theorem power_support_sum (p : ℕ) (hp : p.Prime) (L u C U : ℝ) (A : ℂ)
    (hL : 0 < L) (hu : u ∈ Set.Icc 0 U) (_hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    (∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1), ‖supportFactor (p^a) L A‖) ≤
      2*Real.exp (C*U) := by
  calc
    _ ≤ ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1), Real.exp (C*U)*(1/((p^a:ℕ):ℝ)) := by
      apply sum_le_sum
      intro a ha
      have hr := power_cutoff_mem p a hp L u hL hu.1 ha
      have hr1 : (1:ℝ) ≤ (p^a:ℕ) := by exact_mod_cast (mem_Icc.mp hr).1
      have hlog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(p^a:ℕ))).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2)
      have ht := normalized_log_mem ((p^a:ℕ):ℝ) L u hr1 hL hlog
      have hb := exp_weight_bound A (Real.log (p^a:ℕ)/L) C U hA
        (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hu.2)
      rw [supportFactor,norm_div,Complex.norm_natCast]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (p^a))
    _ = Real.exp (C*U)*∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1), 1/((p^a:ℕ):ℝ) := (mul_sum ..).symm
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (reciprocal_power_sum p (Nat.log p ⌊Real.exp (L*u)⌋₊+1) hp) (Real.exp_pos (C*U)).le]

/-- Uniform in every nonzero modulus h, prime p, and u including zero. -/
theorem residual_euler_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ p h : ℕ, p.Prime → h ≠ 0 →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖(L:ℂ)*residualInner ⌊Real.exp (L*u)⌋₊ p h L u θ P A‖ ≤ D*eulerMass (h*p) 0 := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let B := coprimeCap P θ C U K
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg P θ C U K hθ hC hU hK)
  refine ⟨2*Real.exp (C*U)*B,by positivity,?_⟩
  intro L hL p h hp hh u hu A hA
  have hhp := mul_ne_zero hh hp.ne_zero
  have hE := euler_nonneg (h*p) hhp
  rw [residual_scaled_cutoff p h hp L u θ P A hL.ne']
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1),
        ‖supportFactor (p^a) L A‖*(B*eulerMass (h*p) 0) := by
      apply sum_le_sum
      intro a ha
      have hr := power_cutoff_mem p a hp L u hL hu.1 ha
      have hr1 : (1:ℝ) ≤ (p^a:ℕ) := by exact_mod_cast (mem_Icc.mp hr).1
      have hlog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(p^a:ℕ))).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2)
      have ht := normalized_log_mem ((p^a:ℕ):ℝ) L u hr1 hL hlog
      have hv : u-Real.log (p^a)/L ∈ Set.Icc 0 U := by
        simp only [Nat.cast_pow] at ht
        exact ⟨by linarith [ht.2],by linarith [ht.1,hu.2]⟩
      have hb := (scaled_coprime_common_bound P hP A (h*p) L _ θ C U K hL hθ hA hv hK hbound).trans
        (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ (h*p) hhp) hB)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = (∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1), ‖supportFactor (p^a) L A‖)*(B*eulerMass (h*p) 0) := (sum_mul ..).symm
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right (power_support_sum p hp L u C U A hL hu hC hA) (mul_nonneg hB hE)
      simpa only [mul_assoc] using hb

/-- log(g)/L may vary in a bounded interval; no fixed-g hypothesis. -/
theorem sharedBlock_euler_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ D*eulerMass g 0 := by
  obtain ⟨D,hD,hbound⟩ := residual_euler_bound P hP θ C U hθ hC hU
  refine ⟨V^2*D,by positivity,?_⟩
  intro L hL g hg ht u hu A hA
  have hE := euler_nonneg g hg
  have hs : ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤
      ((∑ p ∈ g.primeFactors, (Real.log p)^2)/L^2)*(D*eulerMass g 0) := by
    rw [sharedBlock_residual _ g L u θ P A hg]
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_div,Finset.sum_mul]
    apply sum_le_sum
    intro p hp
    have hb := (hbound L hL p _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.ordCompl_pos p hg).ne' u hu A hA).trans
      (mul_le_mul_of_nonneg_left (residual_modulus_euler g p hg hp) hD)
    have hm : ‖(ArithmeticFunction.moebius (g/p^(g.factorization p)):ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using (show |(ArithmeticFunction.moebius (g/p^(g.factorization p)):ℝ)| ≤ 1 by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g/p^(g.factorization p)))
    rw [norm_mul,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,sq_abs]
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(Real.log p)^2/L^2)
    simp only [mul_one] at hm'
    exact mul_le_mul hm' hb (norm_nonneg _) (by positivity : 0≤(Real.log p)^2/L^2)
  apply hs.trans
  have ht2 : (Real.log g/L)^2 ≤ V^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Real.log g/L)) ht 2
  have hh := div_le_div_of_nonneg_right (prime_log_square_sum g hg) (sq_nonneg L)
  rw [← div_pow] at hh
  have hb := mul_le_mul_of_nonneg_right (hh.trans ht2) (mul_nonneg hD hE)
  convert hb using 1
  ring

theorem sharedBlock_twoBidiscs (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ U V : ℝ) (hθ : 0 < θ) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ p ∈ ElementaryGcd.twoBidiscs,
        ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.1‖ ≤ D*eulerMass g 0 ∧
        ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.2‖ ≤ D*eulerMass g 0 := by
  obtain ⟨D,hD,h⟩ := sharedBlock_euler_bound P hP θ (5*PRZZAsymptotic.R/4) U V hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hU
  refine ⟨D,hD,?_⟩
  intro L hL g hg ht u hu p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact ⟨h L hL g hg ht u hu p.1 hs.1,h L hL g hg ht u hu p.2 hs.2⟩

#print axioms euler_mono_support
#print axioms residual_modulus_euler
#print axioms prime_log_square_sum
#print axioms reciprocal_power_sum
#print axioms power_cutoff_mem
#print axioms power_support_sum
#print axioms residual_euler_bound
#print axioms sharedBlock_euler_bound
#print axioms sharedBlock_twoBidiscs
end XiPrime8845.FengSharedBounds
