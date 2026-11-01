import PRZZAStarFubini

/-! Exact signed-frequency fibers of the literal source kernel.
The h and Delta dependent weights stay inside each fiber. This is not
an assertion that those weights factor into DI coefficient sequences. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZAStarFrequency
open PRZZAStar PRZZKloostermanInputs

def frequency (z : Index) : ℤ := (z.2.2:ℤ)*z.2.1
def key (z : Index) : (ℕ × ℕ) × ℤ := (z.1,frequency z)

def phase (k : (ℕ × ℕ) × ℤ) : ℂ :=
  e (-(k.2:ℝ)*inverseResidue k.1.2 k.1.1/k.1.2)

def residual (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (x y : ℝ) (z : Index) : ℂ :=
  a (d*z.1.1)*star (a (d*z.1.2))*F1 (d*z.1.1)*F2 (d*z.1.2) /
    ((d:ℂ)*(z.1.1:ℂ)^α*(z.1.2:ℂ)^β) *
    outerKernel FM α β z x * innerKernel W Phi T z x y

theorem kernel_phase (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (x y : ℝ) (z : Index) :
    kernel d T a F1 F2 FM W Phi α β z x y =
      phase (key z)*residual d T a F1 F2 FM W Phi α β x y z := by
  simp only [kernel,prefactor,phase,key,frequency,residual,Int.cast_mul,Int.cast_natCast]
  ring

/-- No enlarged rectangular summation domain and no discarded cutoff. -/
theorem regroup (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (x y : ℝ) :
    (∑ z ∈ indices N d D H, kernel d T a F1 F2 FM W Phi α β z x y) =
      ∑ k ∈ (indices N d D H).image key, phase k *
        ∑ z ∈ (indices N d D H).filter (fun z => key z = k),
          residual d T a F1 F2 FM W Phi α β x y z := by
  rw [← sum_fiberwise_of_maps_to
    (fun z hz => mem_image_of_mem key hz)
    (fun z => kernel d T a F1 F2 FM W Phi α β z x y)]
  apply sum_congr rfl
  intro k hk
  rw [mul_sum]
  apply sum_congr rfl
  intro z hz
  rw [kernel_phase, (mem_filter.mp hz).2]

#print axioms kernel_phase
#print axioms regroup

theorem literal_regroup (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Set.Ioi (0:ℝ), ∫ y,
        ∑ k ∈ (indices N d D H).image key, phase k *
          ∑ z ∈ (indices N d D H).filter (fun z => key z = k),
            residual d T a F1 F2 FM W Phi α β x y z := by
  rw [PRZZAStarFubini.literal_eq_integral_sum N d D H T A B a
    F1 F2 FM W Phi α β hFM hW hPhi hsM hsP hA hB hT]
  simp_rw [regroup]

#print axioms literal_regroup

/-- The two arithmetic variables separate before any DI estimate.
The coupled Phi cutoff is deliberately retained. -/
theorem residual_separated (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (x y : ℝ) (z : Index) :
    residual d T a F1 F2 FM W Phi α β x y z =
      (a (d*z.1.1)*F1 (d*z.1.1)/(z.1.1:ℂ)^α) *
      (star (a (d*z.1.2))*F2 (d*z.1.2)*FM (x*z.1.2)/(z.1.2:ℂ)^β) *
      (e (-(z.2.2:ℝ)*x)*e ((z.2.1:ℝ)*y/(2*Real.pi))) *
      (W (2*Real.pi*x/y)/((d:ℂ)*(x:ℂ)^(α+β))) *
      Phi (x*y*z.1.1*z.1.2/T) := by
  unfold residual outerKernel innerKernel
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

#print axioms residual_separated
end XiPrime8845.PRZZAStarFrequency
