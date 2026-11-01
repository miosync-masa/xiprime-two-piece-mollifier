import PRZZAStarIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact positive cutoffs supply joint integrability of the literal
source kernel. This exchanges x and y, not the Mellin integral. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZAStarFubini
open PRZZAStar PRZZKloostermanInputs
set_option maxHeartbeats 2000000

theorem kernel_integrable (d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) := by
  have h1 : (0:ℝ) < z.1.1 := by exact_mod_cast hn1
  have h2 : (0:ℝ) < z.1.2 := by exact_mod_cast hn2
  let s := Icc (A/z.1.2) (B/z.1.2) ×ˢ Icc (T/(B*z.1.1)) (2*T/(A*z.1.1))
  have hs : Function.support (fun p : ℝ × ℝ =>
      kernel d T a F1 F2 FM W Phi α β z p.1 p.2) ⊆ s := by
    intro p hp
    have hm : FM (p.1*z.1.2) ≠ 0 := by
      intro hz; exact hp (by simp [kernel,outerKernel,hz])
    have hph : Phi (p.1*p.2*z.1.1*z.1.2/T) ≠ 0 := by
      intro hz; exact hp (by simp [kernel,innerKernel,hz])
    have hm' := hsM hm
    have hp' := hsP hph
    have hx : 0 < p.1 := by nlinarith [hm'.1]
    have hy : 0 < p.2 := by
      have hh := (le_div_iff₀ hT).mp hp'.1
      have : 0 < p.1*p.2*z.1.1*z.1.2 := by linarith
      by_contra hn
      have hh' := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hx.le (le_of_not_gt hn)) h1.le) h2.le
      linarith
    refine ⟨⟨(div_le_iff₀ h2).mpr hm'.1,(le_div_iff₀ h2).mpr hm'.2⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ (mul_pos hB h1)).mpr
      have hh := (le_div_iff₀ hT).mp hp'.1
      have hb := mul_le_mul_of_nonneg_right hm'.2 (mul_pos hy h1).le
      nlinarith
    · apply (le_div_iff₀ (mul_pos hA h1)).mpr
      have hh := (div_le_iff₀ hT).mp hp'.2
      have ha := mul_le_mul_of_nonneg_right hm'.1 (mul_pos hy h1).le
      nlinarith
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hx : ∀ p ∈ s, 0 < p.1 := fun p hp => (div_pos hA h2).trans_le hp.1.1
  have hy : ∀ p ∈ s, 0 < p.2 := fun p hp => (div_pos hT (mul_pos hB h1)).trans_le hp.2.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)^(α+β)) s :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.cpow_const
      (fun p hp => by simpa using (hx p hp))
  have hn : ∀ p ∈ s, (p.1:ℂ)^(α+β) ≠ 0 := fun p hp =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne'))
  unfold kernel outerKernel innerKernel
  apply ContinuousOn.mul
  · apply continuousOn_const.mul
    apply ContinuousOn.div _ hc hn
    unfold e
    fun_prop
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · unfold e; fun_prop
      · apply hW.comp_continuousOn
        exact (continuousOn_const.mul continuous_fst.continuousOn).div
          continuous_snd.continuousOn (fun p hp => (hy p hp).ne')
    · fun_prop

theorem outer_integrable (d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    IntegrableOn (fun x => ∫ y, kernel d T a F1 F2 FM W Phi α β z x y) (Ioi (0:ℝ)) :=
  (kernel_integrable d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hsM hsP hA hB hT hn1 hn2).integral_prod_left.integrableOn

theorem kernel_integral_swap (d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    (∫ x, ∫ y, kernel d T a F1 F2 FM W Phi α β z x y) =
      ∫ y, ∫ x, kernel d T a F1 F2 FM W Phi α β z x y :=
  integral_integral_swap (kernel_integrable d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hsM hsP hA hB hT hn1 hn2)

/-- Both integrability obligations in the literal finite-sum exchange
are supplied by continuous cutoffs supported away from zero. -/
theorem literal_eq_integral_sum (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Ioi (0:ℝ), ∫ y, ∑ z ∈ indices N d D H,
        kernel d T a F1 F2 FM W Phi α β z x y := by
  apply PRZZAStarIntegrability.literal_eq_integral_sum_of_cutoff
    N d D H T a F1 F2 FM W Phi α β hW hPhi hsP hT
  intro z hz
  have hn := Finset.mem_product.mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact outer_integrable d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hsM hsP hA hB hT
    (by have := (Finset.mem_Icc.mp hn.1).1; omega)
    (by have := (Finset.mem_Icc.mp hn.2).1; omega)

#print axioms kernel_integrable
#print axioms outer_integrable
#print axioms kernel_integral_swap
#print axioms literal_eq_integral_sum
end XiPrime8845.PRZZAStarFubini
