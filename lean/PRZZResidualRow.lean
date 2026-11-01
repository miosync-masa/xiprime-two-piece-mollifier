import PRZZResidualWeighted

/-! The actual analytic row is transported without deleting its masks.
Negative original frequencies k=-a give the positive DI phase. The
remaining product-dependent weight is explicitly charged by variation. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZResidualRow
open PRZZSupportedBranches PRZZMellinSeparation PRZZAStarRectangles
open PRZZResidualWeighted
set_option maxHeartbeats 3000000

def weight (N d j h : ℕ) (F1 : ℝ → ℂ) (α : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if h*n ∈ PRZZDyadic.cell N j ∧ d*(h*n) ≤ N then
    F1 (d*(h*n))/((h*n:ℕ):ℂ)^α*twist (h*n) t else 0

/-- All c, n and frequency sums are rearranged before taking norms.
The scalar h remains inside the inverse residue and the original weight. -/
theorem row_eq (N d j l h : ℕ) (A : ℝ) (b nu : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (f g : ArithmeticFunction ℂ) :
    (∑ a ∈ Icc 1 ⌊A⌋₊, nu a * ∑ n ∈ Icc 1 N,
      if d.Coprime n ∧ d*(h*n) ≤ N then
        (f*g) n*row N d j l (fun _ => 1) b F1 F2 FM α β x t (-(a:ℤ)) (h*n) else 0) =
      grouped N d N A h (secondCoeff N d l b F2 FM β x t) nu f g (weight N d j h F1 α t) := by
  have ifsum (p : Prop) [Decidable p] (s : Finset ℕ) (v : ℕ → ℂ) :
      (if p then ∑ c ∈ s, v c else 0) = ∑ c ∈ s, if p then v c else 0 := by
    by_cases hp : p <;> simp [hp]
  unfold row grouped secondCoeff weight
  simp only [Nat.floor_natCast,PRZZDyadic.cell,sum_filter,mem_filter]
  simp only [mul_sum,ite_mul,mul_ite,zero_mul,mul_zero,ifsum]
  conv_lhs => enter [2,a]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro n hn
  have hc1 := (mem_Icc.mp hc).1
  have hn1 := (mem_Icc.mp hn).1
  simp only [hc,true_and,Nat.coprime_mul_iff_left,
    Int.cast_neg,Int.cast_natCast,neg_neg,one_mul]
  by_cases hhc : h.Coprime c <;> by_cases hnc : n.Coprime c <;>
    by_cases hdn : d.Coprime n <;> by_cases hcut : d*(h*n) ≤ N <;>
    by_cases hdc : d*c ≤ N <;> by_cases hj : h*n ∈ Icc 1 N ∧ Nat.log 2 (h*n)=j <;>
    by_cases hl : Nat.log 2 c=l <;>
    simp [hhc,hnc,hdn,hcut,hdc,hj,hl,Nat.coprime_comm,mul_assoc] <;> ring_nf
  all_goals split_ifs <;> simp_all [Nat.coprime_comm]

/-- The DI constant is chosen before the source parameters. The original
product weight is retained; its actual variation is an explicit cost, not
an assumed height-uniform envelope. Group supports and coefficient bounds
remain hypotheses to be supplied by the selected Heath--Brown branch. -/
theorem row_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N d j l h E F : ℕ,
      1 ≤ E → E ≤ N → 1 ≤ F → F ≤ N → 1 ≤ h →
      ∀ A : ℝ, 1 ≤ A → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ (b nu : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ)
        (f g : ArithmeticFunction ℂ),
      (∀ n, E < n → f n = 0) → (∀ n, F < n → g n = 0) →
      (∀ c ∈ Icc 1 N, ‖secondCoeff N d l b F2 FM β x t c‖ ≤ R) →
      (∀ n ∈ Icc 1 F, ‖g n‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) → (∀ n ∈ Icc 1 E, ‖f n‖ ≤ Q) →
      ‖∑ a ∈ Icc 1 ⌊A⌋₊, nu a * ∑ n ∈ Icc 1 N,
        if d.Coprime n ∧ d*(h*n) ≤ N then
          (f*g) n*row N d j l (fun _ => 1) b F1 F2 FM α β x t (-(a:ℤ)) (h*n) else 0‖ ≤
        ((1+2*Real.log ((F:ℝ)+1))*(R*S*(P*Q)*K*
          (((N:ℝ)*F*A*E)^eps*PRZZDISeven.seven h E A ((E:ℝ)*F) N)))*
            PRZZTypeI.variation (fun k => weight N d j h F1 α t (k+1)) N := by
  obtain ⟨K,hK,hb⟩ := grouped_seven hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N d j l h E F hE hEN hF hFN hh A hA R S P Q hR hS hP hQ
    b nu F1 F2 FM α β x t f g hsf hsg hr hg hn hf
  rw [row_eq]
  exact hb N d E F hE hEN hF hFN N A (by exact_mod_cast hE.trans hEN) hA h hh
    R S P Q hR hS hP hQ _ nu _ f g hsf hsg
    (by simpa only [Nat.floor_natCast] using hr) hg hn hf

#print axioms row_eq
#print axioms row_seven
end XiPrime8845.PRZZResidualRow
