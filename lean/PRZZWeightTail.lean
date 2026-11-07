import PRZZWeightFourier
import Mathlib.Analysis.PSeries

/-! Absolute two-sided Poisson frequency tails for the actual spatial weight.
The original derivative L1 mass is retained, with arbitrary inverse powers
of the frequency cutoff. No arithmetic or time integration cost is hidden. -/
noncomputable section
open scoped FourierTransform ContDiff
open MeasureTheory Set
namespace XiPrime8845.PRZZWeightTail
open PRZZFullWeightSmooth PRZZWeightFourier

def squareMass : ℝ := ∑' j : ℕ, 1/((j:ℝ)+1)^2

theorem square_summable : Summable (fun j : ℕ => 1/((j:ℝ)+1)^2) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr h

theorem tail_majorant (B : ℝ) (hB : 0 ≤ B) (n H j : ℕ) :
    B/((H+j:ℝ)+1)^(n+2) ≤ B/((H:ℝ)+1)^n * (1/((j:ℝ)+1)^2) := by
  have hh : (0:ℝ) < (H:ℝ)+j+1 := by positivity
  calc
    _ = B/(((H:ℝ)+j+1)^n*((H:ℝ)+j+1)^2) := by rw [pow_add]
    _ ≤ B/(((H:ℝ)+1)^n*((j:ℝ)+1)^2) := by
      apply div_le_div_of_nonneg_left hB (by positivity)
      gcongr <;> linarith [show (0:ℝ) ≤ H from Nat.cast_nonneg H,
        show (0:ℝ) ≤ j from Nat.cast_nonneg j]
    _ = _ := by rw [div_mul_eq_div_div]; ring

theorem tail_of_bound (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (B : ℝ) (hB : 0 ≤ B) (n H : ℕ)
    (hb : ∀ j, f j ≤ B/((H+j:ℝ)+1)^(n+2)) :
    Summable f ∧ (∑' j, f j) ≤ B/((H:ℝ)+1)^n*squareMass := by
  have hs := square_summable.mul_left (B/((H:ℝ)+1)^n)
  have he : ∀ j, f j ≤ B/((H:ℝ)+1)^n*(1/((j:ℝ)+1)^2) :=
    fun j => (hb j).trans (tail_majorant B hB n H j)
  have hf' := hs.of_nonneg_of_le hf he
  refine ⟨hf',?_⟩
  simpa [squareMass,tsum_mul_left] using hf'.tsum_le_tsum he hs

/-- Frequencies are +(H+j+1)/q and -(H+j+1)/q, with the modulus q
retained exactly. The n+2 derivative supplies an H^-n summable tail. -/
theorem actual_tail (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hN : 0 < N) (hk : 0 < k)
    (hsigma : sigma ≠ 0) (hs : Function.support F ⊆ Icc lo hi)
    (n H : ℕ) (q : ℝ) (hq : 0 < q) :
    let f := weight F N k omega z sigma
    let M := ∫ x in Icc (lo*N) (hi*N), ‖iteratedDeriv (n+2) f x‖
    let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
    Summable tail ∧ (∑' j, tail j) ≤
      (2*M*(q/(2*Real.pi))^(n+2))/((H:ℝ)+1)^n*squareMass := by
  dsimp only
  let M := ∫ x in Icc (lo*N) (hi*N), ‖iteratedDeriv (n+2) (weight F N k omega z sigma) x‖
  have hM : 0 ≤ M := integral_nonneg (fun x => norm_nonneg _)
  apply tail_of_bound _ (fun j => add_nonneg (norm_nonneg _) (norm_nonneg _))
    (2*M*(q/(2*Real.pi))^(n+2)) (by positivity) n H
  intro j
  have ht : 0 < ((H+j:ℝ)+1)/q := by positivity
  have h1 := fourier_bound lo hi hlo F hF N k omega z sigma hN hk hsigma hs (n+2) _ ht.ne'
  have h2 := fourier_bound lo hi hlo F hF N k omega z sigma hN hk hsigma hs (n+2) _ (neg_ne_zero.mpr ht.ne')
  rw [abs_of_pos ht] at h1
  rw [abs_neg,abs_of_pos ht] at h2
  apply (add_le_add h1 h2).trans_eq
  dsimp [M]
  simp only [mul_pow,div_pow,div_eq_mul_inv,mul_inv_rev,inv_pow,inv_inv]
  ring

/-- The reciprocal-phase radius is supplied by the actual support, and
the derivative L1 mass is replaced by the proved explicit envelope. -/
theorem uniform_tail (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc lo hi) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (N k omega q : ℝ) (z sigma : ℂ),
      0 < N → 0 < k → 0 < q → sigma ≠ 0 →
      let f := weight F N k omega z sigma
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
      Summable tail ∧ (∑' j, tail j) ≤
        (2*(∫ x in Icc (lo*N) (hi*N),
          PRZZFullWeightJets.envelope C D E a k x (|omega|/(lo*N)) z sigma (n+2)/x^(n+2))*
          (q/(2*Real.pi))^(n+2))/((H:ℝ)+1)^n*squareMass := by
  obtain ⟨C,D,E,hpos,hm⟩ := mass_uniform lo hi hlo F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H N k omega q z sigma hN hk hq hsigma
  have ht := actual_tail lo hi hlo F hF N k omega z sigma hN hk hsigma hs n H q hq
  refine ⟨ht.1,ht.2.trans ?_⟩
  have hm' := hm (n+2) N k omega (|omega|/(lo*N)) z sigma hN hk hsigma (by
    intro x hx
    rw [abs_div,abs_of_pos ((mul_pos hlo hN).trans_le hx.1)]
    exact div_le_div_of_nonneg_left (abs_nonneg omega) (mul_pos hlo hN) hx.1)
  rw [mass_on_support lo hi hlo F N k omega z sigma hN hs (n+2)] at hm'
  have hz : 0 ≤ squareMass := tsum_nonneg (fun j => by positivity)
  dsimp only at *
  gcongr

#print axioms uniform_tail
#print axioms square_summable
#print axioms tail_majorant
#print axioms tail_of_bound
#print axioms actual_tail
end XiPrime8845.PRZZWeightTail
