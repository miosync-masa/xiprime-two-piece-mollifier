import FengAtG

/-! Exact local cancellation of the shared-prime correction.
This evaluates a full local prime-power string, not the global sharedBlock. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.FengPrimeCancellation
open FengAtG ArithmeticFunction
set_option maxHeartbeats 1000000

theorem mark_prime_pow (p k : ℕ) (hp : p.Prime) :
    mark (p^k) = (k:ℂ)*(Real.log p:ℂ)^2 := by
  cases k with
  | zero => simp [mark]
  | succ k =>
    simp only [mark,vonMangoldt_apply_pow (Nat.succ_ne_zero k),vonMangoldt_apply_prime hp,
      Nat.cast_pow,Real.log_pow,Complex.ofReal_mul,Complex.ofReal_natCast]
    ring

theorem moebius_prime_pow_ge_two (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    μ (p^k) = 0 := by
  rw [moebius_apply_prime_pow hp (by omega),if_neg (by omega)]

/-- The last two nonzero Mobius coefficients cancel their exponent dependence. -/
theorem prime_power_telescope (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    (∑ k ∈ Finset.range (e+1), (k:ℂ)*(μ (p^(e-k)):ℂ)) = 1 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  have hz : (∑ k ∈ Finset.range a, (k:ℂ)*(μ (p^(a+1-k)):ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [moebius_prime_pow_ge_two p _ hp (by have := Finset.mem_range.mp hk; omega)]
    simp
  rw [hz]
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel_left,Nat.sub_self,pow_zero,pow_one,
    moebius_apply_one,moebius_apply_prime hp,Int.cast_neg,Int.cast_one,zero_add,Nat.cast_add,Nat.cast_one]
  ring

/-- All prime powers from 1 through p^e are retained before cancellation. -/
theorem marked_prime_power_telescope (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    (∑ k ∈ Finset.range (e+1), mark (p^k)*(μ (p^(e-k)):ℂ)) = (Real.log p:ℂ)^2 := by
  simp_rw [mark_prime_pow p _ hp]
  have h := congrArg (fun z : ℂ => z*(Real.log p:ℂ)^2) (prime_power_telescope p e hp he)
  rw [Finset.sum_mul,one_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intros
  ring

/-- A coprime residue factors out; no squarefreeness hypothesis on it is needed. -/
theorem shared_local_cancellation (p e m : ℕ) (hp : p.Prime) (he : 0 < e)
    (hm : p.Coprime m) :
    (∑ k ∈ Finset.range (e+1), mark (p^k)*(μ (p^(e-k)*m):ℂ)) =
      (μ m:ℂ)*(Real.log p:ℂ)^2 := by
  simp_rw [isMultiplicative_moebius.map_mul_of_coprime (hm.pow_left _),Int.cast_mul,← mul_assoc]
  rw [← Finset.sum_mul,marked_prime_power_telescope p e hp he]
  ring

/-- Splitting the total exponent between g and n introduces no extra factor. -/
theorem shared_local_at_gn (p b a h m : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hh : p.Coprime h) (hm : p.Coprime m) :
    (∑ k ∈ Finset.range (b+a+1), mark (p^k)*(μ (p^(b+a-k)*(h*m)):ℂ)) =
      (μ (h*m):ℂ)*(Real.log p:ℂ)^2 :=
  shared_local_cancellation p (b+a) (h*m) hp (by omega) (hh.mul_right hm)

/-- The shared coefficient still depends on the residue, but not the local exponent. -/
theorem shared_local_norm_le (p e m : ℕ) (hp : p.Prime) (he : 0 < e)
    (hm : p.Coprime m) :
    ‖∑ k ∈ Finset.range (e+1), mark (p^k)*(μ (p^(e-k)*m):ℂ)‖ ≤ (Real.log p)^2 := by
  rw [shared_local_cancellation p e m hp he hm,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hμ : ‖(μ m:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using (show |(μ m:ℝ)| ≤ 1 by
      exact_mod_cast abs_moebius_le_one (n:=m))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (sq_nonneg (Real.log p))

#print axioms mark_prime_pow
#print axioms moebius_prime_pow_ge_two
#print axioms prime_power_telescope
#print axioms marked_prime_power_telescope
#print axioms shared_local_cancellation
#print axioms shared_local_at_gn
#print axioms shared_local_norm_le
end XiPrime8845.FengPrimeCancellation
