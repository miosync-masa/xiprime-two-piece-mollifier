import PRZZDyadic
import PRZZGcdAverage

/-! Dyadic restrictions of actual Dirichlet-convolution coefficients.
Every endpoint and outer coprimality condition is retained. This is an exact
finite identity, not a coefficient growth estimate or an A-star estimate.
Cells use PRZZDyadic's [2^k,2^(k+1)) convention. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZDyadicArithmetic
open PRZZDyadic
set_option maxHeartbeats 1000000

private theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp only [sum_insert ha,ArithmeticFunction.add_apply,ih]

def restrict (N k : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ cell N k then f n else 0, by simp [cell]⟩

theorem sum_restrict (N n : ℕ) (hn : n ≤ N) (f : ArithmeticFunction ℂ) :
    (∑ k ∈ range (Nat.log 2 N+1), restrict N k f) n = f n := by
  rw [eval_sum]
  by_cases h0 : n = 0
  · subst n; simp
  have hn' : n ∈ Icc 1 N := mem_Icc.mpr ⟨by omega,hn⟩
  have hk : Nat.log 2 n ∈ range (Nat.log 2 N+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hn))
  rw [sum_eq_single (Nat.log 2 n)]
  · change (if n ∈ cell N (Nat.log 2 n) then f n else 0) = f n
    apply if_pos
    change n ∈ (Icc 1 N).filter (fun m => Nat.log 2 m = Nat.log 2 n)
    exact mem_filter.mpr ⟨hn',rfl⟩
  · intro k _ hne
    simp [restrict,cell,Ne.symm hne]
  · exact fun hh => (hh hk).elim

/-- Both factors of every divisor pair are at most n; no artificial
extension of a coefficient beyond the original cutoff is introduced. -/
theorem convolution_dyadic (N n : ℕ) (hn : n ≤ N) (f g : ArithmeticFunction ℂ) :
    (f*g) n = ∑ k ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      (restrict N k f * restrict N l g) n := by
  have he : (f*g) n =
      ((∑ k ∈ range (Nat.log 2 N+1), restrict N k f)*
       (∑ l ∈ range (Nat.log 2 N+1), restrict N l g)) n := by
    rw [mul_apply,mul_apply]
    apply sum_congr rfl
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have h1 : d.1 ≤ n := by
      rw [← he]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd))
    have h2 : d.2 ≤ n := by
      rw [← he,mul_comm]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd))
    rw [sum_restrict N d.1 (h1.trans hn),sum_restrict N d.2 (h2.trans hn)]
  rw [he,sum_mul]
  simp only [mul_sum,eval_sum]

/-- Weighted outer sums keep their original coprimality filter. -/
theorem weighted_coprime_convolution (N q : ℕ) (f g : ArithmeticFunction ℂ)
    (w : ℕ → ℂ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q), w n*(f*g) n) =
      ∑ k ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q),
          w n*(restrict N k f * restrict N l g) n := by
  calc
    _ = ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q),
        ∑ k ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
          w n*(restrict N k f * restrict N l g) n := by
      apply sum_congr rfl
      intro n hn
      rw [convolution_dyadic N n (mem_Icc.mp (mem_filter.mp hn).1).2 f g]
      simp only [mul_sum]
    _ = _ := by rw [sum_comm]; apply sum_congr rfl; intros; rw [sum_comm]

#print axioms sum_restrict
#print axioms convolution_dyadic
#print axioms weighted_coprime_convolution
end XiPrime8845.PRZZDyadicArithmetic
