import PRZZAStarFrequency

/-! The signed h*Delta frequency coefficient is independent of n1,n2.
This exact finite rearrangement precedes Type I/II coefficient estimates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZNuCoefficient
open PRZZKloostermanInputs

def freq (q : ℤ × ℕ) : ℤ := (q.2:ℤ)*q.1
def oscillation (x y : ℝ) (q : ℤ × ℕ) : ℂ :=
  e (-(q.2:ℝ)*x)*e ((q.1:ℝ)*y/(2*Real.pi))
def nu (s : Finset (ℤ × ℕ)) (x y : ℝ) (k : ℤ) : ℂ :=
  ∑ q ∈ s.filter (fun q => freq q = k), oscillation x y q

theorem oscillation_norm (x y : ℝ) (q : ℤ × ℕ) : ‖oscillation x y q‖ = 1 := by
  have he (t : ℝ) : ‖e t‖ = 1 := by simp [e,Complex.norm_exp]
  simp only [oscillation,norm_mul,he,mul_one]

theorem nu_norm_le_card (s : Finset (ℤ × ℕ)) (x y : ℝ) (k : ℤ) :
    ‖nu s x y k‖ ≤ ((s.filter (fun q => freq q = k)).card:ℝ) := by
  apply (norm_sum_le _ _).trans_eq
  simp [oscillation_norm]

/-- Nonzero signed frequencies have at most one Delta for each positive
h dividing |k|. The bound is uniform in both real integration variables. -/
theorem fiber_card_le_divisors (s : Finset (ℤ × ℕ)) (k : ℤ) (hk : k ≠ 0)
    (hs : ∀ q ∈ s, 0 < q.2) :
    (s.filter (fun q => freq q = k)).card ≤ k.natAbs.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro q hq
    obtain ⟨hqs,hqk⟩ := mem_filter.mp hq
    apply Nat.mem_divisors.mpr
    refine ⟨?_,Int.natAbs_ne_zero.mpr hk⟩
    have he : k.natAbs = q.2*q.1.natAbs := by
      rw [← hqk,freq,Int.natAbs_mul,Int.natAbs_natCast]
    rw [he]
    exact dvd_mul_right _ _
  · intro q hq r hr he
    apply Prod.ext _ he
    have hqk := (mem_filter.mp hq).2
    have hrk := (mem_filter.mp hr).2
    have hn : (q.2:ℤ) ≠ 0 := by exact_mod_cast (hs q (mem_filter.mp hq).1).ne'
    apply mul_left_cancel₀ hn
    simpa only [freq,← he] using hqk.trans hrk.symm

theorem nu_norm_le_divisors (s : Finset (ℤ × ℕ)) (x y : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hs : ∀ q ∈ s, 0 < q.2) :
    ‖nu s x y k‖ ≤ (k.natAbs.divisors.card:ℝ) :=
  (nu_norm_le_card s x y k).trans (by exact_mod_cast fiber_card_le_divisors s k hk hs)

theorem separate {ι : Type*} (s : Finset (ℤ × ℕ)) (n : Finset ι)
    (x y : ℝ) (c : ι → ℂ) (phase : ι → ℤ → ℂ) :
    (∑ i ∈ n, ∑ q ∈ s, c i*oscillation x y q*phase i (freq q)) =
      ∑ k ∈ s.image freq, nu s x y k * ∑ i ∈ n, c i*phase i k := by
  classical
  rw [sum_comm]
  rw [← sum_fiberwise_of_maps_to (fun q hq => mem_image_of_mem freq hq)
    (fun q => ∑ i ∈ n, c i*oscillation x y q*phase i (freq q))]
  apply sum_congr rfl
  intro k hk
  unfold nu
  rw [sum_mul]
  apply sum_congr rfl
  intro q hq
  rw [(mem_filter.mp hq).2,mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

#print axioms separate
#print axioms oscillation_norm
#print axioms nu_norm_le_card
#print axioms fiber_card_le_divisors
#print axioms nu_norm_le_divisors
end XiPrime8845.PRZZNuCoefficient
