import PRZZTypeICoprime

/-! Exact Type I inverse-product phase transport. Both factors are units
modulo q; the new frequency and sharp scaled weight are retained. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.PRZZInversePhase
open PRZZKloostermanInputs PRZZTypeI PRZZTypeICoprime
set_option maxHeartbeats 2000000

theorem e_add_int (x : ℝ) (m : ℤ) : e (x+m) = e x := by
  unfold e
  push_cast
  rw [mul_add,Complex.exp_add]
  have hm : Complex.exp (2*Real.pi*Complex.I*(m:ℂ)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I m using 1 <;> ring
  rw [hm,mul_one]

theorem phase_mod (q n : ℕ) (hq : 0 < q) (a : ℤ) :
    e ((a:ℝ)*(n%q:ℕ)/q) = e ((a:ℝ)*n/q) := by
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hn : (n:ℝ) = (n%q:ℕ)+(q:ℝ)*(n/q:ℕ) := by
    exact_mod_cast (Nat.mod_add_div n q).symm
  have he : (a:ℝ)*n/q = (a:ℝ)*(n%q:ℕ)/q+(a*((n/q:ℕ):ℤ):ℤ) := by
    simp only [Int.cast_mul,Int.cast_natCast]
    conv_lhs => rw [hn]
    field_simp
    <;> ring
  rw [he,e_add_int]

theorem inverse_product (q ell k : ℕ) (he : ell.Coprime q) (hk : k.Coprime q) :
    inverseResidue q (ell*k) = (inverseResidue q ell*inverseResidue q k)%q := by
  have hi : ((ell*k:ℕ):ZMod q)⁻¹ = (ell:ZMod q)⁻¹*(k:ZMod q)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    push_cast
    calc
      _ = ((ell:ZMod q)*(ell:ZMod q)⁻¹)*((k:ZMod q)*(k:ZMod q)⁻¹) := by ring
      _ = 1 := by rw [ZMod.coe_mul_inv_eq_one ell he,ZMod.coe_mul_inv_eq_one k hk,one_mul]
  unfold inverseResidue
  rw [hi,ZMod.val_mul]

theorem phase_product (q ell k : ℕ) (hq : 0 < q)
    (he : ell.Coprime q) (hk : k.Coprime q) (a : ℤ) :
    e ((a:ℝ)*inverseResidue q (ell*k)/q) =
      e (((a*(inverseResidue q ell:ℤ):ℤ):ℝ)*inverseResidue q k/q) := by
  rw [inverse_product q ell k he hk,phase_mod q _ hq a]
  congr 1
  push_cast
  ring

/-- Each Mobius divisor row is now a literal standard Weil row. -/
theorem restricted_eq (d q N : ℕ) (hd : d ≠ 0) (hq : 0 < q)
    (a : ℤ) (w : ℕ → ℂ) :
    restrictedSum d q N a w =
      ∑ ell ∈ d.divisors.filter (fun ell => ell.Coprime q), (μ ell:ℂ)*
        weightedSum q (a*(inverseResidue q ell:ℤ)) 0 (N/ell) (fun j => w (ell*(j+1))) := by
  classical
  rw [coprime_divisor_rows d q N hd a w]
  apply sum_congr rfl; intro ell hell
  congr 1
  have he := (mem_filter.mp hell).2
  have hs : Icc 1 (N/ell) = Ico 1 (N/ell+1) := by ext n; simp <;> omega
  rw [hs,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,weightedSum,term,zero_add]
  apply sum_congr rfl; intro j hj
  rw [show 1+j=j+1 by omega]
  by_cases hk : (j+1).Coprime q
  · rw [if_pos hk,if_pos hk,phase_product q ell (j+1) hq he hk a]
  · rw [if_neg hk,if_neg hk,mul_zero]

#print axioms e_add_int
#print axioms phase_mod
#print axioms inverse_product
#print axioms phase_product
#print axioms restricted_eq

/-- Weil is applied only after exact arithmetic transport. The divisor
sum, transformed gcd, sharp length and scaled variation are explicit. -/
theorem restricted_bound (hWeil : WeilIncomplete) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q N : ℕ, d ≠ 0 → 1 ≤ q → ∀ a : ℤ, ∀ w : ℕ → ℂ,
      ‖restrictedSum d q N a w‖ ≤ C*Real.rpow q (1/2+eps)*
        ∑ ell ∈ d.divisors.filter (fun ell => ell.Coprime q),
          ‖(μ ell:ℂ)‖*((a*(inverseResidue q ell:ℤ)).natAbs.gcd q:ℝ)*
            (1+(N/ell:ℕ)/(q:ℝ))*variation (fun j => w (ell*(j+1))) (N/ell) := by
  obtain ⟨C,hC,h⟩ := weighted_bound hWeil eps heps
  refine ⟨C,hC,?_⟩
  intro d q N hd hq a w
  rw [restricted_eq d q N hd (by omega) a w,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro ell hell
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (h q hq (a*(inverseResidue q ell:ℤ)) 0 (N/ell) (fun j => w (ell*(j+1))))
      (norm_nonneg _)).trans_eq (by ring)

#print axioms restricted_bound
end XiPrime8845.PRZZInversePhase
