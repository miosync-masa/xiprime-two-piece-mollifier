import PRZZExtendedTailDomain
import PRZZL1Finite

/-! Pruning of finite pre-Poisson lattice rows and simultaneous substitution
of the source cap bound. The weights retain arithmetic masks. This sums
the analytic budgets, not an unidentified Fourier tail or literal A*. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZPrunedTailRows
set_option maxHeartbeats 2000000

def Active (s : Finset ℕ) (F : ℝ → ℂ) : Prop := ∃ m ∈ s, F m ≠ 0

local instance (s : Finset ℕ) (F : ℝ → ℂ) : Decidable (Active s F) :=
  Classical.propDecidable _

theorem prune {ι : Type*} (rows : Finset ι) (s : ι → Finset ℕ)
    (F : ι → ℝ → ℂ) (c : ι → ℕ → ℂ) :
    (∑ i ∈ rows, ∑ m ∈ s i, F i m*c i m) =
      ∑ i ∈ rows, if Active (s i) (F i) then ∑ m ∈ s i, F i m*c i m else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : Active (s i) (F i)
  · simp [h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m hm
    have hf : F i m = 0 := by
      by_contra hf
      exact h ⟨m,hm,hf⟩
    simp [hf]

/-- Literal finite AFE terms, before Poisson; the other indices remain. -/
theorem afe_prune {ι : Type*} (rows : Finset ι) (F : ι → ℝ → ℂ)
    (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ) (V : ℕ → ℝ → ℂ) (t : ℝ) :
    (∑ i ∈ rows, ∑ m ∈ Finset.Icc 1 L, F i m *
      (∑ k ∈ Finset.Icc 1 L, ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
        PRZZL1Finite.term a b alpha beta V t m k n r)) =
      ∑ i ∈ rows, if Active (Finset.Icc 1 L) (F i) then
        ∑ m ∈ Finset.Icc 1 L, F i m *
          (∑ k ∈ Finset.Icc 1 L, ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
            PRZZL1Finite.term a b alpha beta V t m k n r) else 0 :=
  prune rows (fun _ => Finset.Icc 1 L) F _

theorem active_scale (s : Finset ℕ) (F : ℝ → ℂ) (M : ℝ)
    (hs : ∀ m ∈ s, 1 ≤ m)
    (hF : Function.support F ⊆ Set.Icc (M/2) (3*M))
    (h : Active s F) : 1 ≤ 3*M := by
  obtain ⟨m,hm,hf⟩ := h
  exact PRZZExtendedTailDomain.nonempty_scale F M m hF (hs m hm) hf

def budget (C D E : ℕ → ℝ) (a T M q h u t eD : ℝ)
    (alpha beta : ℂ) (n : ℕ) : ℝ :=
  PRZZEnvelopeMass.cap C D E a (2*Real.pi*u/(t*q)) M 0
    (|Real.log (M/2)|+|Real.log (3*M)|)
    (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) (n+2)*
    (1+8*T^eD)^2*(q/M)*((1+8*T^eD)*q/(M*h))^n

/-- One order and constant for every finite row family. No count of rows
is silently absorbed: the retained nonnegative weight mass is explicit.
The original positive gcd indices and time cutoff supply the domain. -/
theorem all_rows (C D E : ℕ → ℝ) (a b S r eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ (ι : Type) (rows : Finset ι)
      (s : ι → Finset ℕ) (F : ι → ℝ → ℂ) (M Q h w : ι → ℝ)
      (u v : ι → ℕ) (d N : ℕ) (T t : ℝ) (alpha beta : ℂ) (Phi : ℝ → ℂ),
      1 ≤ d → (N:ℝ) ≤ T → 36 ≤ T → 1 ≤ Real.log T →
      ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      Function.support Phi ⊆ Set.Icc (1:ℝ) 2 → Phi (t/T) ≠ 0 →
      (∀ i ∈ rows, 0 ≤ w i ∧ (∀ m ∈ s i, 1 ≤ m) ∧
        Function.support (F i) ⊆ Set.Icc (M i/2) (3*M i) ∧
        M i ≤ T^b ∧ 0 < Q i ∧ 1 ≤ u i ∧ 1 ≤ v i ∧ d*v i ≤ N ∧
        (v i:ℝ) ≤ 3*Q i/d ∧
        PRZZSourceCutoffs.poissonCutoff d T (M i) (Q i) eH ≤ h i) →
      (∑ i ∈ rows, if Active (s i) (F i) then
        w i*budget C D E a T (M i) (v i) (h i) (u i) t eD alpha beta n else 0) ≤
        K*T^(-A)*(∑ i ∈ rows, w i) := by
  classical
  obtain ⟨n,K,hK,hbound⟩ := PRZZExtendedTailDomain.source_absorbed
    C D E a b S r eD eH A hc ha hb hS hr heD he
  refine ⟨n,K,hK,?_⟩
  intro ι rows s F M Q h w u v d N T t alpha beta Phi hd hNT hT hlog halpha hsep hPhi htime hrows
  have hd0 : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hT0 : 0 < T := by linarith
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hw,hs,hF,hM,hQ,hu,hv,hvN,hbox,hcut⟩ := hrows i hi
  by_cases hactive : Active (s i) (F i)
  · rw [if_pos hactive]
    obtain ⟨hu1,hv0,hvT,ht0,ht2⟩ := PRZZExtendedTailDomain.index_time
      d N (u i) (v i) T t Phi hd hu hv hvN hNT hT0 hPhi htime
    have hm := active_scale (s i) (F i) (M i) hs hF hactive
    have hh := hbound d T (M i) (Q i) (v i) (h i) (u i) (v i) t alpha beta
      hd0 hT hlog hm hM hQ hv0.le hvT hbox hu1 hv0 hvT ht0 ht2 halpha hsep hcut
    exact (mul_le_mul_of_nonneg_left hh hw).trans_eq (mul_comm _ _)
  · rw [if_neg hactive]
    positivity

#print axioms prune
#print axioms afe_prune
#print axioms active_scale
#print axioms all_rows
end XiPrime8845.PRZZPrunedTailRows
