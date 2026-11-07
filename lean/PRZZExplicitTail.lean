import PRZZExplicitDomain

/-! Supply the actual source-tail domain from explicit AFE triples.
Original support and source-scale conditions remain visible. This is the
arbitrary-power Fourier tail, not the main Weil/DI cancellation estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex
namespace XiPrime8845.PRZZExplicitTail
open PRZZAFEIndices PRZZTailTimeSum
set_option maxHeartbeats 3000000

def reduced (p : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  (p.2.1/Nat.gcd p.2.1 p.2.2,p.2.2/Nat.gcd p.2.1 p.2.2)

theorem retained_rows (L N : ℕ) (z : Label) (p : ℕ × ℕ × ℕ)
    (hp : p ∈ PRZZExplicitDomain.domain L N z) (F1 F2 : ℝ → ℂ)
    (hf : F1 p.2.1 ≠ 0) (hg : F2 p.2.2 ≠ 0) :
    reduced p ∈ PRZZSourceRows.rows N z.1 z.2.2.1 z.2.2.2 F1 F2 := by
  classical
  obtain ⟨hmem,hd,hj,hl,hdiv,hlo,hhi⟩ := Finset.mem_filter.mp hp
  have hn := (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).1
  have hr := (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
  have hh := reduced_rows N p.2.1 p.2.2 hn hr F1 F2 hf hg
  simpa only [← hd,← hj,← hl,reduced] using hh

theorem source_domain (L N : ℕ) (z : Label) (p : ℕ × ℕ × ℕ)
    (hp : p ∈ PRZZExplicitDomain.domain L N z)
    (F1 F2 FM : ℝ → ℂ) (s : Finset ℕ) (T M Q1 Q2 b eD eH : ℝ)
    (hf : F1 p.2.1 ≠ 0) (hg : F2 p.2.2 ≠ 0)
    (hNT : (N:ℝ) ≤ T) (hM : M ≤ T^b) (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hs1 : Function.support F1 ⊆ Icc (Q1/2) (3*Q1))
    (hs2 : Function.support F2 ⊆ Icc (Q2/2) (3*Q2))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs : ∀ m ∈ s, 1 ≤ m) (ha : PRZZPrunedTailRows.Active s FM)
    (hdelta : |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/z.1) :
    Domain z.1 T b eD eH (PRZZSourceRows.data z.1 T M Q1 Q2 eH z.2.1 (reduced p)) := by
  classical
  have hm := (Finset.mem_filter.mp hp).1
  have hn := (Finset.mem_product.mp (Finset.mem_product.mp hm).2).1
  have hd := (Finset.mem_filter.mp hp).2.1
  have hdpos : 1 ≤ z.1 := by
    rw [← hd]
    exact Nat.gcd_pos_of_pos_left p.2.2 (Finset.mem_Icc.mp hn).1
  exact PRZZSourceRows.domain N z.1 z.2.2.1 z.2.2.2 F1 F2 FM s T M Q1 Q2 b eD eH z.2.1
    (reduced p) hdpos hNT hM hQ1 hQ2 hs1 hs2 hsM hs ha
    (retained_rows L N z p hp F1 F2 hf hg) hdelta

theorem infinite_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L N : ℕ) (z : Label) (p : ℕ × ℕ × ℕ),
    p ∈ PRZZExplicitDomain.domain L N z → ∀ (F1 F2 FM : ℝ → ℂ) (s : Finset ℕ)
      (T t M Q1 Q2 : ℝ) (alpha beta : ℂ) (plus minus : ℕ → ℂ),
    F1 p.2.1 ≠ 0 → F2 p.2.2 ≠ 0 → (N:ℝ) ≤ T → M ≤ T^b → 0 < Q1 → 0 < Q2 →
    Function.support F1 ⊆ Icc (Q1/2) (3*Q1) →
    Function.support F2 ⊆ Icc (Q2/2) (3*Q2) →
    Function.support FM ⊆ Icc (M/2) (3*M) → (∀ m ∈ s, 1 ≤ m) →
    PRZZPrunedTailRows.Active s FM →
    |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/z.1 →
    36 ≤ T → 1 ≤ Real.log T → t ∈ Icc T (2*T) → ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
    (∀ j, ‖plus j‖ ≤ 1) → (∀ j, ‖minus j‖ ≤ 1) →
    let row := PRZZSourceRows.data z.1 T M Q1 Q2 eH z.2.1 (reduced p)
    let f := fun j => PRZZFourierTime.term F row.M row.u row.q row.delta
      (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) row.H j plus minus t
    Summable f ∧ ‖∑' j, f j‖ ≤ K*T^(-A) := by
  obtain ⟨K,hK,h⟩ := PRZZInfiniteTail.source_bound F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro L N z p hp F1 F2 FM s T t M Q1 Q2 alpha beta plus minus hf hg hNT hM hQ1 hQ2
    hs1 hs2 hsM hs hactive hdelta hT hlog ht halpha hsep hplus hminus
  have hz := source_domain L N z p hp F1 F2 FM s T M Q1 Q2 b eD eH hf hg
    hNT hM hQ1 hQ2 hs1 hs2 hsM hs hactive hdelta
  have hdpos : (0:ℝ) < z.1 := by
    classical
    have hm := (Finset.mem_filter.mp hp).1
    have hn := (Finset.mem_product.mp (Finset.mem_product.mp hm).2).1
    have hd := (Finset.mem_filter.mp hp).2.1
    rw [← hd]
    exact_mod_cast Nat.gcd_pos_of_pos_left p.2.2 (Finset.mem_Icc.mp hn).1
  exact h z.1 T t _ alpha beta plus minus hdpos hT hlog ht hz halpha hsep hplus hminus

#print axioms retained_rows
#print axioms source_domain
#print axioms infinite_tail
end XiPrime8845.PRZZExplicitTail
