import PRZZActualMellin

/-! Exact composition from the literal source A* to its localized Mellin
transform. No asymptotic estimate or DI supplier is assumed here. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex Finset
namespace XiPrime8845.PRZZAStarTransform
open PRZZAStar PRZZAStarWindow PRZZAStarMellin PRZZActualMellin PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem kernel_inversion (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hz : z ∈ indices N d D H) (p : ℝ × ℝ) :
    kernel d T a F1 F2 FM W Phi α β z p.1 p.2 =
      (1/(2*Real.pi):ℂ)*∫ t, localized N d T A B a F1 F2 FM W Phi α β z p t := by
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  by_cases hp : p ∈ window N T A B
  · have hx : 0 < p.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
    have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hp.2.1
    have h1 : (0:ℝ) < z.1.1 := by exact_mod_cast (show 0 < z.1.1 by have := (mem_Icc.mp hn.1).1; omega)
    have h2 : (0:ℝ) < z.1.2 := by exact_mod_cast (show 0 < z.1.2 by have := (mem_Icc.mp hn.2).1; omega)
    rw [kernel_amplitude]
    rw [PRZZMellinSeparation.separate Phi
      (PRZZSmoothMellin.mellin_convergent Phi 1 2 (by norm_num) hsP hPhi.continuous)
      (PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hsP hPhi)
      (p.1*p.2/T) z.1.1 z.1.2 (by positivity) h1 h2 hPhi.continuous.continuousAt]
    simp only [localized,Set.indicator_of_mem hp]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  · have hh := congrFun (indicator_kernel N d D H T A B a F1 F2 FM W Phi α β z
      hsM hsP hA hB hT hz) p
    have hk : kernel d T a F1 F2 FM W Phi α β z p.1 p.2 = 0 := by
      simpa only [Set.indicator_of_notMem hp] using hh.symm
    simp [hk,localized,hp]

theorem literal_mellin (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t, ∫ p : ℝ × ℝ,
        ∑ z ∈ indices N d D H, localized N d T A B a F1 F2 FM W Phi α β z p t := by
  have hi (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) := by
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact PRZZAStarFubini.kernel_integrable d T A B a F1 F2 FM W Phi α β z
      hFM hW hPhi.continuous hsM hsP hA hB hT
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hz0 (z : Index) (hz : z ∈ indices N d D H) (x : ℝ) (hx : x ∉ Set.Ioi (0:ℝ)) :
      (∫ y, kernel d T a F1 F2 FM W Phi α β z x y) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change kernel d T a F1 F2 FM W Phi α β z x y = 0
    have hp : (x,y) ∉ window N T A B := by
      intro hh
      exact hx ((div_pos hA (by exact_mod_cast hN)).trans_le hh.1.1)
    have hh := congrFun (indicator_kernel N d D H T A B a F1 F2 FM W Phi α β z
      hsM hsP hA hB hT hz) (x,y)
    simpa only [Set.indicator_of_notMem hp] using hh.symm
  have he : literal N d D H T a F1 F2 FM W Phi α β =
      ∫ p : ℝ × ℝ, ∑ z ∈ indices N d D H, kernel d T a F1 F2 FM W Phi α β z p.1 p.2 := by
    rw [literal_eq_sum_integrals,integral_finsetSum _ hi]
    apply sum_congr rfl
    intro z hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hz0 z hz)]
    exact (integral_prod _ (hi z hz)).symm
  rw [he,← finite_swap N d D H T A B a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hN hT hA hB,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [integral_finsetSum]
  · rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    exact kernel_inversion N d D H T A B a F1 F2 FM W Phi α β z hPhi hsP hsM hN hT hA hB hz p
  · intro z hz
    unfold localized
    by_cases hp : p ∈ window N T A B
    · have hx : 0 < p.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
      have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hp.2.1
      have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
      have h1 : (0:ℝ) < z.1.1 := by exact_mod_cast (show 0 < z.1.1 by have := (mem_Icc.mp hn.1).1; omega)
      have h2 : (0:ℝ) < z.1.2 := by exact_mod_cast (show 0 < z.1.2 by have := (mem_Icc.mp hn.2).1; omega)
      have hh := (PRZZMellinSeparation.kernel_integrable Phi
        (PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hsP hPhi)
        (p.1*p.2/T*z.1.1*z.1.2) (by positivity)).const_mul
        (amplitude d a F1 F2 FM W α β p.1 p.2 z)
      have ht (t : ℝ) : twist (p.1*p.2/T*z.1.1*z.1.2) t =
          twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t := by
        rw [twist_mul _ _ _ (by positivity) h2.le,
          twist_mul _ _ _ (by positivity) h1.le]
      simp_rw [ht] at hh
      simpa only [Set.indicator_of_mem hp,mul_assoc] using hh
    · simp only [Set.indicator_of_notMem hp,zero_mul]
      exact integrable_zero _ _ _

#print axioms kernel_inversion
#print axioms literal_mellin
end XiPrime8845.PRZZAStarTransform
