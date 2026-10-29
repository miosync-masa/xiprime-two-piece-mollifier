import FengPrimeExclusion
import FengPrimeMass

/-! Short logarithmic windows for the full prime-power mass. Endpoints move
with L and u; no restriction to primes or fixed cutoff is made. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengPrimeWindow
open FengPrimeExclusion Zeta23.XiPrime
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem mass_Icc (N : ℕ) : (∑ n ∈ Icc 1 N, mass n) = FengPrimeMass.mass N := by
  unfold FengPrimeMass.mass mass
  apply sum_congr rfl
  intros; ring

theorem cumulative_error (x : ℝ) (hx : 0 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊Real.exp x⌋₊, mass n)-x^2/2| ≤ 2*KM*(1+x) := by
  have h := mertens_monomial 1 hx
  norm_num [mass] at h ⊢
  exact h

theorem window_bound (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊, mass n) ≤
      (b^2-a^2)/2+4*KM*(1+b) := by
  have hmn := Nat.floor_mono (Real.exp_le_exp.mpr hab)
  have hd : Disjoint (Ioc 0 ⌊Real.exp a⌋₊) (Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊) := by
    apply disjoint_left.mpr
    intro n hn hm
    have := mem_Ioc.mp hn
    have := mem_Ioc.mp hm
    omega
  have he : Ioc 0 ⌊Real.exp a⌋₊ ∪ Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊ = Ioc 0 ⌊Real.exp b⌋₊ := by
    ext n; simp only [mem_union,mem_Ioc]; omega
  have hsplit := sum_union (f:=mass) hd
  rw [he] at hsplit
  have h1 := (abs_le.mp (cumulative_error a ha)).1
  have h2 := (abs_le.mp (cumulative_error b (ha.trans hab))).2
  have hK := KM_nonneg
  nlinarith

def windowError (L U : ℝ) : ℝ := 4*KM*(1+L*U)/L^2

theorem windowError_nonneg (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    0 ≤ windowError L U := by unfold windowError; have := KM_nonneg; positivity

theorem windowError_tendsto (U : ℝ) :
    Tendsto (fun L => windowError L U) atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero (𝕜:=ℝ)
  have h : Tendsto (fun L : ℝ => 4*KM*((L⁻¹)^2+U*L⁻¹)) atTop (nhds 0) := by
    simpa using ((hi.pow 2).add (hi.const_mul U)).const_mul (4*KM)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  unfold windowError
  field_simp

/-- The mass where the translated inner cutoff is below delta. This includes
the case u<delta and the exact finite cutoff exp(L*u). -/
theorem endpoint_mass (L u U δ : ℝ) (hL : 0 < L) (hu : u ∈ Set.Icc 0 U)
    (hδ : 0 ≤ δ) :
    (∑ n ∈ (Icc 1 ⌊Real.exp (L*u)⌋₊).filter (fun n : ℕ => u-Real.log n/L < δ), mass n)/L^2 ≤
      2*U*δ+windowError L U := by
  have hU : 0 ≤ U := hu.1.trans hu.2
  by_cases hud : u < δ
  · have hsub : (∑ n ∈ (Icc 1 ⌊Real.exp (L*u)⌋₊).filter (fun n : ℕ => u-Real.log n/L < δ), mass n) ≤
        FengPrimeMass.mass ⌊Real.exp (L*u)⌋₊ := by
      rw [← mass_Icc]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => mass_nonneg n)
    have hh := (div_le_div_of_nonneg_right hsub (sq_nonneg L)).trans
      (FengPrimeMass.scaled_mass_bound L u hL hu.1)
    have hp := mul_le_mul hu.2 hud.le hu.1 hU
    have he := windowError_nonneg L U hL.le hU
    nlinarith
  · have hdu : δ ≤ u := le_of_not_gt hud
    have heq : (Icc 1 ⌊Real.exp (L*u)⌋₊).filter (fun n : ℕ => u-Real.log n/L < δ) =
        Ioc ⌊Real.exp (L*(u-δ))⌋₊ ⌊Real.exp (L*u)⌋₊ := by
      ext n
      simp only [mem_filter,mem_Icc,mem_Ioc]
      constructor
      · rintro ⟨⟨hn,hnN⟩,ht⟩
        have hn0 : (0:ℝ)<n := by exact_mod_cast hn
        refine ⟨?_,hnN⟩
        apply (Nat.floor_lt (by positivity : (0:ℝ)≤Real.exp (L*(u-δ)))).mpr
        rw [← Real.exp_log hn0,Real.exp_lt_exp]
        have hh := (lt_div_iff₀ hL).mp (show u-δ<Real.log n/L by linarith)
        nlinarith
      · rintro ⟨hn,hnN⟩
        have hn1 : 1 ≤ n := by omega
        refine ⟨⟨hn1,hnN⟩,?_⟩
        have hn0 : (0:ℝ)<n := by exact_mod_cast hn1
        have ht := (Nat.floor_lt (by positivity : (0:ℝ)≤Real.exp (L*(u-δ)))).mp hn
        rw [← Real.exp_log hn0,Real.exp_lt_exp] at ht
        have hh : u-δ < Real.log n/L := (lt_div_iff₀ hL).mpr (by nlinarith)
        linarith
    rw [heq]
    have hw := window_bound (L*(u-δ)) (L*u) (mul_nonneg hL.le (sub_nonneg.mpr hdu))
      (mul_le_mul_of_nonneg_left (by linarith) hL.le)
    apply (div_le_iff₀ (pow_pos hL 2)).mpr
    have hK : 0 ≤ KM := KM_nonneg
    have he : windowError L U*L^2 = 4*KM*(1+L*U) := by
      unfold windowError; field_simp
    rw [add_mul,he]
    have hp := mul_le_mul_of_nonneg_left hu.2 (mul_nonneg (sq_nonneg L) hδ)
    have hq := mul_le_mul_of_nonneg_left hu.2 (mul_nonneg hK hL.le)
    have hpos : 0 ≤ L^2*δ*U := by positivity
    nlinarith only [hw,hp,hq,hpos,sq_nonneg (L*δ)]

#print axioms cumulative_error
#print axioms window_bound
#print axioms windowError_tendsto
#print axioms endpoint_mass
end XiPrime8845.FengPrimeWindow
