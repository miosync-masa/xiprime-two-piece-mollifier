import Mathlib

/-! Exact finite dyadic partition and the greedy product dichotomy behind
PRZZ p.20 / Pratt--Robles [58], p.17. The half-open convention is [2^k,2^(k+1));
1 is retained. This proves numerical factor classification, not yet the
arithmetic-function regrouping or the O(U^epsilon) coefficient budget. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZDyadic
set_option maxHeartbeats 1000000

def cell (N k : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => Nat.log 2 n = k)

theorem mem_cell (N k n : ℕ) : n ∈ cell N k ↔
    n ∈ Icc 1 N ∧ 2^k ≤ n ∧ n < 2^(k+1) := by
  simp only [cell,mem_filter]
  constructor
  · rintro ⟨hn,hk⟩
    subst k
    exact ⟨hn,Nat.pow_log_le_self 2 (by have := (mem_Icc.mp hn).1; omega),
      Nat.lt_pow_succ_log_self (by norm_num) n⟩
  · rintro ⟨hn,hlo,hhi⟩
    exact ⟨hn,Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩

theorem sum_partition (N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, f n) = ∑ k ∈ range (Nat.log 2 N+1), ∑ n ∈ cell N k, f n := by
  symm
  apply sum_fiberwise_of_maps_to
  intro n hn
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hn).2))

/-- A minimal crossing of W overshoots by at most a factor W. -/
theorem crossing {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) (W : ℝ)
    (hW : 1 < W) (hx : ∀ i ∈ s, 1 ≤ x i ∧ x i ≤ W) (hp : W ≤ ∏ i ∈ s, x i) :
    ∃ t ⊆ s, W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ W^2 := by
  induction s using Finset.induction_on with
  | empty => simp at hp; linarith
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 1 ≤ x i ∧ x i ≤ W := fun i hi => hx i (mem_insert_of_mem hi)
    by_cases ht : W ≤ ∏ i ∈ s, x i
    · obtain ⟨t,hts,hlo,hhi⟩ := ih hs ht
      exact ⟨t,hts.trans (subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert a s,Subset.rfl,hp,?_⟩
      rw [prod_insert ha]
      have hxa := hx a (mem_insert_self _ _)
      have hprod : (∏ i ∈ s, x i) ≤ W := (lt_of_not_ge ht).le
      have hm := mul_le_mul hxa.2 hprod (prod_nonneg (fun i hi => (hs i hi).1.trans' zero_le_one))
        (by linarith : 0 ≤ W)
      nlinarith

/-- Exact-scale form of the large-factor / balanced-subset dichotomy.
The first case needs a separate proof that the large factor is a free
log-power factor, rather than a truncated Mobius factor. -/
theorem classify {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) (U W : ℝ)
    (hW : 1 < W) (hx : ∀ i ∈ s, 1 ≤ x i) (hprod : ∏ i ∈ s, x i = U) (hscale : W^3 ≤ U) :
    (∃ i ∈ s, U/W < x i ∧ (∏ j ∈ s.erase i, x j) < W) ∨
    (∃ t ⊆ s, W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ U/W ∧
      W ≤ ∏ i ∈ s \ t, x i ∧ (∏ i ∈ s \ t, x i) ≤ U/W) := by
  have hW0 : 0 < W := by linarith
  have hWU : W ≤ U := by nlinarith [sq_nonneg (W-1)]
  have hW2 : W^2 ≤ U/W := (le_div_iff₀ hW0).mpr (by nlinarith)
  by_cases hlarge : ∃ i ∈ s, U/W < x i
  · obtain ⟨i,hi,hbig⟩ := hlarge
    left
    refine ⟨i,hi,hbig,?_⟩
    have he : x i*(∏ j ∈ s.erase i, x j) = U := (mul_prod_erase s x hi).trans hprod
    have hh := (div_lt_iff₀ hW0).mp hbig
    have hxi := hx i hi
    nlinarith
  · right
    have hupper : ∀ i ∈ s, x i ≤ U/W := by
      intro i hi
      exact le_of_not_gt (fun hh => hlarge ⟨i,hi,hh⟩)
    have hex : ∃ t ⊆ s, W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ U/W := by
      by_cases hm : ∃ i ∈ s, W ≤ x i
      · obtain ⟨i,hi,hm⟩ := hm
        exact ⟨{i},singleton_subset_iff.mpr hi,by simpa,by simpa using hupper i hi⟩
      · obtain ⟨t,ht,hl,hh⟩ := crossing s x W hW (by
          intro i hi
          exact ⟨hx i hi,(lt_of_not_ge (fun hh => hm ⟨i,hi,hh⟩)).le⟩) (by rwa [hprod])
        exact ⟨t,ht,hl,hh.trans hW2⟩
    obtain ⟨t,ht,hl,hh⟩ := hex
    have he : (∏ i ∈ t, x i)*(∏ i ∈ s \ t, x i) = U := by
      rw [mul_comm,prod_sdiff ht,hprod]
    have hc : 0 ≤ ∏ i ∈ s \ t, x i := prod_nonneg (fun i hi => by linarith [hx i (mem_sdiff.mp hi).1])
    refine ⟨t,ht,hl,hh,?_,?_⟩
    · have hp := (le_div_iff₀ hW0).mp hh
      nlinarith
    · apply (le_div_iff₀ hW0).mpr
      nlinarith

/-- Exact box-count aggregation before absorbing logarithms in U^epsilon. -/
theorem box_sum_bound (N r : ℕ) (B : ℝ)
    (S : (Fin r → Fin (Nat.log 2 N+1)) → ℂ) (hS : ∀ k, ‖S k‖ ≤ B) :
    ‖∑ k, S k‖ ≤ ((Nat.log 2 N+1:ℕ):ℝ)^r*B := by
  apply (norm_sum_le _ _).trans
  have h := sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin r → Fin (Nat.log 2 N+1)))) => hS k)
  simpa using h

#print axioms mem_cell
#print axioms sum_partition
#print axioms crossing
#print axioms classify
#print axioms box_sum_bound
end XiPrime8845.PRZZDyadic
