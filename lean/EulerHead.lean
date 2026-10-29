import CoprimeHead
import TotientWeight

/-! Complete the supported reciprocal head to its zero-shift Euler mass.
The product tail estimate is uniform in the outer arithmetic cutoff. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.EulerHead
set_option maxHeartbeats 1000000
open SupportTail SupportProductTail SmoothMobius
attribute [local instance] Classical.propDecidable

def mass (Q g : ℕ) : ℝ := supportedSum g (Icc 1 Q) (fun r => 1/(r:ℝ))

theorem mass_nonneg (Q g : ℕ) : 0 ≤ mass Q g := by
  unfold mass supportedSum; positivity

theorem mass_le (Q g : ℕ) (hg : g ≠ 0) : mass Q g ≤ eulerMass g 0 := by
  simpa only [mass, supportedSum, sub_zero, zero_sub, Real.rpow_neg_one, one_div] using
    supported_mass_le g hg ((Icc 1 Q).filter (supported g)) 0 (by norm_num)
      (fun r hr => (mem_filter.mp hr).2)

theorem mass_tendsto (g : ℕ) (hg : g ≠ 0) :
    Tendsto (fun Q => mass Q g) atTop (nhds (eulerMass g 0)) := by
  have hh : HasSum ((Nat.factoredNumbers g.primeFactors).indicator
      (fun r : ℕ => (r:ℝ)^(0-1:ℝ))) (eulerMass g 0) :=
    hasSum_subtype_iff_indicator.mp (supported_hasSum g 0 (by norm_num))
  have he : (Nat.factoredNumbers g.primeFactors).indicator
      (fun r : ℕ => (r:ℝ)^(0-1:ℝ)) = fun r => if supported g r then 1/(r:ℝ) else 0 := by
    funext r
    simp only [Set.indicator_apply, ← supported_factored g r hg,
      zero_sub, Real.rpow_neg_one, one_div]
  rw [he] at hh
  have h := hh.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext Q
  simp only [Function.comp_apply]
  rw [Nat.range_succ_eq_Icc_zero, Icc_eq_cons_Ioc (Nat.zero_le Q), sum_cons]
  simp only [Nat.cast_zero, div_zero, ite_self, zero_add]
  have hi : Ioc 0 Q = Icc 1 Q := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  simp only [hi, mass, supportedSum, sum_filter]

theorem mass_product_bound (N K J : ℕ) :
    (∑ g ∈ Icc 1 N, (1/(g:ℝ))*mass K g*mass J g) ≤
      SupportTail.harmonic N*productConstant := by
  have h := tail_times_mass_bound N (Icc 1 K) (Icc 1 J) 1 (by norm_num)
    (fun r hr => by exact_mod_cast (mem_Icc.mp hr).1)
    (fun r hr => Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1))
  simpa only [Real.one_rpow, one_mul, mass] using h

theorem mass_sub_head (K Q g : ℕ) (hQK : Q ≤ K) :
    mass K g-mass Q g =
      supportedSum g ((Icc 1 K).filter (fun r => Q < r)) (fun r => 1/(r:ℝ)) := by
  have he : ((Icc 1 K).filter (supported g)).filter (fun r => r ≤ Q) =
      (Icc 1 Q).filter (supported g) := by
    ext r
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1,hK⟩,hs⟩,hQ⟩
      exact ⟨⟨h1,hQ⟩,hs⟩
    · rintro ⟨⟨h1,hQ⟩,hs⟩
      exact ⟨⟨⟨h1,hQ.trans hQK⟩,hs⟩,hQ⟩
  have h := Finset.sum_filter_add_sum_filter_not ((Icc 1 K).filter (supported g))
    (fun r => r ≤ Q) (fun r => 1/(r:ℝ))
  rw [he] at h
  have ht : ((Icc 1 K).filter (supported g)).filter (fun r => ¬ r ≤ Q) =
      ((Icc 1 K).filter (fun r => Q < r)).filter (supported g) := by
    ext r; simp only [mem_filter, not_le]; tauto
  rw [ht] at h
  change mass Q g + supportedSum g ((Icc 1 K).filter (fun r => Q < r))
    (fun r => 1/(r:ℝ)) = mass K g at h
  linarith

/-- Finite product tail, with one full mass factor, before taking its limit. -/
theorem finite_tail_product (N K Q : ℕ) (hQ : 0 < Q) (hQK : Q ≤ K) :
    (∑ g ∈ Icc 1 N, (1/(g:ℝ))*(mass K g-mass Q g)*mass K g) ≤
      SupportTail.harmonic N*((Q:ℝ)^(-1/4:ℝ)*productConstant) := by
  simp_rw [mass_sub_head K Q _ hQK]
  exact tail_times_mass_bound N ((Icc 1 K).filter (fun r => Q < r)) (Icc 1 K) Q
    (by exact_mod_cast hQ)
    (fun r hr => by exact_mod_cast (mem_filter.mp hr).2.le)
    (fun r hr => Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1))

/-- The limit is taken AFTER the product-safe average bound. The constant is
independent of N; this is not merely fixed-g convergence of Euler factors. -/
theorem full_tail_product (N Q : ℕ) (hQ : 0 < Q) :
    (∑ g ∈ Icc 1 N, (1/(g:ℝ))*(eulerMass g 0-mass Q g)*eulerMass g 0) ≤
      SupportTail.harmonic N*((Q:ℝ)^(-1/4:ℝ)*productConstant) := by
  have hlim : Tendsto (fun K => ∑ g ∈ Icc 1 N, (1/(g:ℝ))*(mass K g-mass Q g)*mass K g)
      atTop (nhds (∑ g ∈ Icc 1 N, (1/(g:ℝ))*(eulerMass g 0-mass Q g)*eulerMass g 0)) := by
    apply tendsto_finsetSum
    intro g hg
    have hm := mass_tendsto g (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hg).1))
    exact ((hm.sub_const (mass Q g)).const_mul (1/(g:ℝ))).mul hm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop Q] with K hK
  exact finite_tail_product N K Q hQ hK

#print axioms mass_tendsto
#print axioms mass_product_bound
#print axioms full_tail_product
end XiPrime8845.EulerHead
