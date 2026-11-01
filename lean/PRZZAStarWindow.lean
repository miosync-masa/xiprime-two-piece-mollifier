import PRZZAStarFubini
import PRZZWindowWeight

/-! An index-independent positive window, inserted before Mellin inversion.
The window depends on the original cutoff N, not on an individual summand. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace XiPrime8845.PRZZAStarWindow
open PRZZAStar
set_option maxHeartbeats 2000000

def window (N : ℕ) (T A B : ℝ) : Set (ℝ × ℝ) :=
  Icc (A/N) B ×ˢ Icc (T/(B*N)) (2*T/A)

theorem support_window (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hn1 : z.1.1 ∈ Finset.Icc 1 N) (hn2 : z.1.2 ∈ Finset.Icc 1 N) :
    Function.support (fun p : ℝ × ℝ =>
      kernel d T a F1 F2 FM W Phi α β z p.1 p.2) ⊆ window N T A B := by
  have h1 : (1:ℝ) ≤ z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn1).1
  have h2 : (1:ℝ) ≤ z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn2).1
  have h1N : (z.1.1:ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn1).2
  have h2N : (z.1.2:ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn2).2
  have hN : (0:ℝ) < N := by linarith
  intro p hp
  have hm : FM (p.1*z.1.2) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,outerKernel,hz])
  have hph : Phi (p.1*p.2*z.1.1*z.1.2/T) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,innerKernel,hz])
  have hm' := hsM hm
  have hp' := hsP hph
  have hlo := (le_div_iff₀ hT).mp hp'.1
  have hhi := (div_le_iff₀ hT).mp hp'.2
  have hx : 0 < p.1 := by nlinarith [hm'.1]
  have hy : 0 < p.2 := by
    by_contra hh
    have hh' := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hx.le (le_of_not_gt hh)) (by linarith : (0:ℝ)≤z.1.1))
        (by linarith : (0:ℝ)≤z.1.2)
    linarith
  have hlo' : T ≤ p.2 * (B*(N:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hm'.2 (show 0 ≤ p.2*z.1.1 by positivity)
    have hh' := mul_le_mul_of_nonneg_left h1N (mul_pos hy hB).le
    nlinarith
  have hhi' : p.2*A ≤ 2*T := by
    have hh := mul_le_mul_of_nonneg_right hm'.1 (show 0 ≤ p.2*z.1.1 by positivity)
    have hh' := mul_le_mul_of_nonneg_left h1 (mul_pos hy hA).le
    nlinarith
  exact ⟨⟨(div_le_iff₀ hN).mpr (hm'.1.trans (mul_le_mul_of_nonneg_left h2N hx.le)),
    by nlinarith [hm'.2]⟩,
    ⟨(div_le_iff₀ (mul_pos hB hN)).mpr hlo', (le_div_iff₀ hA).mpr hhi'⟩⟩

theorem indicator_kernel (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T) (hz : z ∈ indices N d D H) :
    (window N T A B).indicator
      (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) =
      (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) := by
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact Set.indicator_eq_self.mpr (support_window N d T A B a F1 F2 FM W Phi α β z
    hsM hsP hA hB hT hn.1 hn.2)

#print axioms support_window
#print axioms indicator_kernel

theorem literal_window (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Ioi (0:ℝ), ∫ y, (window N T A B).indicator
        (fun p : ℝ × ℝ => ∑ z ∈ indices N d D H,
          kernel d T a F1 F2 FM W Phi α β z p.1 p.2) (x,y) := by
  rw [PRZZAStarFubini.literal_eq_integral_sum N d D H T A B a
    F1 F2 FM W Phi α β hFM hW hPhi hsM hsP hA hB hT]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  by_cases hp : (x,y) ∈ window N T A B
  · simp [hp]
  · rw [Set.indicator_of_notMem hp]
    apply Finset.sum_eq_zero
    intro z hz
    have hh := congrFun (indicator_kernel N d D H T A B a
      F1 F2 FM W Phi α β z hsM hsP hA hB hT hz) (x,y)
    simpa only [Set.indicator_of_notMem hp] using hh.symm

#print axioms literal_window
end XiPrime8845.PRZZAStarWindow
