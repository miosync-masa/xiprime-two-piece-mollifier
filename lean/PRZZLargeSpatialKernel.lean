import PRZZPartitionDiscrepancy
import PRZZWArithmeticCutoff
import PRZZWeightTail

/-! Large original spatial scales are removed before splitting Fourier
modes. Fourth-power sourceW decay and partition mass pay the entire
growing spatial family without a count of its dyadic pieces. -/
noncomputable section
open scoped BigOperators
open Finset Complex Set
namespace XiPrime8845.PRZZLargeSpatialKernel
open PRZZAFEProgression PRZZPartitionMass PRZZL1Finite
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

def constant (sigma : ℂ) : ℝ :=
  Real.exp (16:ℝ)/(8*Real.sqrt Real.pi)+
    10*Real.exp (16:ℝ)/(Real.sqrt Real.pi*‖sigma‖^2)

theorem kernel_four (sigma : ℂ) (hs : sigma ≠ 0) (T t x : ℝ)
    (hT : 0 < T) (ht : t ∈ Icc T (2*T)) (hx : 0 < x) :
    ‖PRZZDyadicEnvelope.sourceW sigma (x/(t/(2*Real.pi)))‖ ≤
      constant sigma*(T/Real.pi)^4/x^4 := by
  have ht0 : 0 < t := hT.trans_le ht.1
  have hh := PRZZSourceDecay.sourceW_decay sigma hs 4 (x/(t/(2*Real.pi)))
    (by norm_num) (by positivity)
  have he : ((x/(t/(2*Real.pi)))^4)⁻¹ = (t/(2*Real.pi))^4/x^4 := by
    field_simp
  norm_num at hh
  have hcEq : Real.exp (16:ℝ)/(2*Real.sqrt Real.pi*4)+
      10*Real.exp (16:ℝ)/(Real.sqrt Real.pi*‖sigma‖^2) = constant sigma := by
    unfold constant
    ring
  rw [hcEq] at hh
  rw [he] at hh
  have hq : t/(2*Real.pi) ≤ T/Real.pi := by
    apply (div_le_div_iff₀ (by positivity) Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht.2 Real.pi_pos.le]
  apply hh.trans
  have hc : 0 ≤ constant sigma := by unfold constant; positivity
  calc
    _ ≤ constant sigma*((T/Real.pi)^4/x^4) := by gcongr
    _ = _ := by ring

theorem direct_four (a b : ℂ) (hs : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (T t : ℝ) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ‖directTerm a b (PRZZWArithmeticCutoff.kernel (a+b)) t m k‖ ≤
      constant (a+b)*(T/Real.pi)^4/((m:ℝ)^4*(k:ℝ)^4) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd := PRZZProductMass.direct_coefficient a b 0 m k hm hk ha hb
  rw [← PRZZProductSummation.coefficient_time a b t m k hm hk] at hd
  simp only [Real.rpow_zero,div_one] at hd
  have hw := kernel_four (a+b) hs T t ((m:ℝ)*k) hT ht (mul_pos hm0 hk0)
  have he : ‖directTerm a b (PRZZWArithmeticCutoff.kernel (a+b)) t m k‖ =
      ‖PRZZDyadicEnvelope.sourceW (a+b) (((m:ℝ)*k)/(t/(2*Real.pi)))‖ *
        ‖directTerm a b (fun _ _ => 1) t m k‖ := by
    simp only [directTerm,PRZZWArithmeticCutoff.kernel,norm_div,norm_one,Nat.cast_mul]
    ring
  rw [he]
  exact (mul_le_mul hw hd (norm_nonneg _) (by unfold constant; positivity)).trans_eq
    (by rw [mul_one,mul_pow])

def largeMass (S : ℝ → ℝ) (K : ℕ) (X x : ℝ) : ℝ :=
  ∑ s ∈ range K, if X ≤ (2:ℝ)^s then ‖piece (fun y => (S y:ℂ)) ((2:ℝ)^s) x‖ else 0

theorem large_mass_le (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1) (K : ℕ) (X x : ℝ) (hx : 0 ≤ x) :
    largeMass S K X x ≤ 1 := by
  apply le_trans _ (piece_mass S hm hlo hhi 1 x K (by norm_num) hx)
  unfold largeMass
  apply sum_le_sum
  intro s hs
  simp only [mul_one]
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _

theorem large_mass_zero (S : ℝ → ℝ)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1) (hright : ∀ y, 1 ≤ y → S y = 0)
    (K : ℕ) (X x : ℝ) (hx : 2*x < X) : largeMass S K X x = 0 := by
  apply sum_eq_zero
  intro s hs
  split_ifs with hlarge
  · have he : piece (fun y => (S y:ℂ)) ((2:ℝ)^s) x = 0 := by
      by_contra hn
      have hp := piece_support (fun y => (S y:ℂ)) ((2:ℝ)^s) (by positivity)
        (by intro y hy; simp [hleft y hy]) (by intro y hy; simp [hright y hy]) hn
      linarith [hp.1]
    rw [he,norm_zero]
  · rfl

/-- Actual W row bound after summing every selected spatial piece. The
only loss from large scales is X^-2, never their growing cardinality. -/
theorem large_direct (S : ℝ → ℝ) (hmono : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1) (hright : ∀ y, 1 ≤ y → S y = 0)
    (a b : ℂ) (hs : a+b ≠ 0) (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (T t X : ℝ) (K m k : ℕ) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hX : 0 < X) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    largeMass S K X m*‖directTerm a b (PRZZWArithmeticCutoff.kernel (a+b)) t m k‖ ≤
      (4*constant (a+b)*(T/Real.pi)^4/X^2)*(1/(m:ℝ)^2)*(1/(k:ℝ)^2) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hC : 0 ≤ constant (a+b) := by unfold constant; positivity
  by_cases hlarge : X ≤ 2*(m:ℝ)
  · have hp := direct_four a b hs ha hb T t hT ht m k hm hk
    apply ((mul_le_mul_of_nonneg_right
      (large_mass_le S hmono hlo hhi K X m hm0.le) (norm_nonneg _)).trans_eq (one_mul _)).trans
    apply hp.trans
    have hmX : X^2 ≤ 4*(m:ℝ)^2 := by nlinarith
    have hk2 : (k:ℝ)^2 ≤ (k:ℝ)^4 := by nlinarith [sq_nonneg ((k:ℝ)^2-1)]
    have hden : X^2*(m:ℝ)^2*(k:ℝ)^2 ≤ 4*(m:ℝ)^4*(k:ℝ)^4 := by
      calc
        _ ≤ (4*(m:ℝ)^2)*(m:ℝ)^2*(k:ℝ)^4 := by gcongr
        _ = _ := by ring
    calc
      _ = (4*constant (a+b)*(T/Real.pi)^4)/(4*(m:ℝ)^4*(k:ℝ)^4) := by ring
      _ ≤ (4*constant (a+b)*(T/Real.pi)^4)/(X^2*(m:ℝ)^2*(k:ℝ)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by ring
  · rw [large_mass_zero S hleft hright K X m (lt_of_not_ge hlarge),zero_mul]
    positivity

theorem square_sum (L : ℕ) :
    (∑ m ∈ Icc 1 L, 1/(m:ℝ)^2) ≤ PRZZWeightTail.squareMass := by
  have he : (∑ m ∈ Icc 1 L, 1/(m:ℝ)^2) = ∑ m ∈ range L, 1/((m:ℝ)+1)^2 := by
    induction L with
    | zero => simp
    | succ L ih => rw [sum_Icc_succ_top (by omega),sum_range_succ,ih]; norm_cast
  rw [he]
  exact PRZZWeightTail.square_summable.sum_le_tsum _ (fun m hm => by positivity)

#print axioms kernel_four
#print axioms direct_four
#print axioms large_mass_le
#print axioms large_mass_zero
#print axioms large_direct
#print axioms square_sum
end XiPrime8845.PRZZLargeSpatialKernel
