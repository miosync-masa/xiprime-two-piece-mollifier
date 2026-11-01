import PRZZKloostermanInputs

/-! Literal finite A* from Pratt--Robles arXiv:1706.04593v3, p.15,
Section 3.2.3 (the positive h part). N is the original coefficient cutoff.
The strict Delta/h cutoffs, conjugate coefficient, and nested integrals
are retained. Finite-sum/integral exchange has explicit integrability
premises; neither their suppliers nor Mellin inversion are asserted here. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace XiPrime8845.PRZZAStar
open PRZZKloostermanInputs
set_option maxHeartbeats 2000000

abbrev Index := (ℕ × ℕ) × (ℤ × ℕ)

def indices (N d : ℕ) (D H : ℝ) : Finset Index :=
  (((Icc 1 N).product (Icc 1 N)).filter
    (fun z => z.1.Coprime z.2 ∧ d*z.1 ≤ N ∧ d*z.2 ≤ N)).product
  (((Icc (-⌈D/d⌉) ⌈D/d⌉).filter
    (fun Δ : ℤ => 0 < |(Δ:ℝ)| ∧ |(Δ:ℝ)| < D/d)).product
    ((Icc 1 ⌊H⌋₊).filter (fun h => (h:ℝ) < H)))

/-- The integer interval used to make the strict Delta cutoff finite
introduces no further restriction. -/
theorem delta_cutoff_iff (B : ℝ) (Δ : ℤ) :
    Δ ∈ (Icc (-⌈B⌉) ⌈B⌉).filter (fun Δ : ℤ => 0 < |(Δ:ℝ)| ∧ |(Δ:ℝ)| < B) ↔
      0 < |(Δ:ℝ)| ∧ |(Δ:ℝ)| < B := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,h⟩
    · have hb := Int.le_ceil B
      have hh := (abs_le.mp h.2.le).1
      exact_mod_cast (show -(⌈B⌉:ℝ) ≤ (Δ:ℝ) by linarith)
    · exact_mod_cast ((abs_le.mp h.2.le).2.trans (Int.le_ceil B))

theorem h_cutoff_iff (H : ℝ) (h : ℕ) :
    h ∈ (Icc 1 ⌊H⌋₊).filter (fun h : ℕ => (h:ℝ) < H) ↔ 1 ≤ h ∧ (h:ℝ) < H := by
  constructor
  · intro hh
    exact ⟨(mem_Icc.mp (mem_filter.mp hh).1).1,(mem_filter.mp hh).2⟩
  · intro hh
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hh.1,Nat.le_floor hh.2.le⟩,hh.2⟩

def prefactor (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (α β : ℂ) (z : Index) : ℂ :=
  a (d*z.1.1)*star (a (d*z.1.2))*F1 (d*z.1.1)*F2 (d*z.1.2) /
    ((d:ℂ)*(z.1.1:ℂ)^α*(z.1.2:ℂ)^β) *
    e (-((z.2.2:ℝ)*(z.2.1:ℝ))*inverseResidue z.1.2 z.1.1/z.1.2)

def innerKernel (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x y : ℝ) : ℂ :=
  e ((z.2.1:ℝ)*y/(2*Real.pi))*W (2*Real.pi*x/y)*Phi (x*y*z.1.1*z.1.2/T)

def outerKernel (FM : ℝ → ℂ) (α β : ℂ) (z : Index) (x : ℝ) : ℂ :=
  e (-(z.2.2:ℝ)*x)*FM (x*z.1.2)/(x:ℂ)^(α+β)

def literal (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) : ℂ :=
  ∑ z ∈ indices N d D H, prefactor a F1 F2 d α β z *
    ∫ x in Set.Ioi (0:ℝ), outerKernel FM α β z x * ∫ y, innerKernel W Phi T z x y

def kernel (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index) (x y : ℝ) : ℂ :=
  prefactor a F1 F2 d α β z*outerKernel FM α β z x*innerKernel W Phi T z x y

/-- Pointwise identification with the original iterated integral, without
any interchange of sums or integrals and without a Mellin substitution. -/
theorem literal_eq_sum_integrals (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∑ z ∈ indices N d D H, ∫ x in Set.Ioi (0:ℝ), ∫ y,
        kernel d T a F1 F2 FM W Phi α β z x y := by
  unfold literal
  apply sum_congr rfl
  intro z hz
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [kernel,integral_const_mul,mul_assoc]

/-- The precise finite-sum exchange needed before Mellin separation.
Integrability is a premise, not hidden in a source-identification axiom. -/
theorem literal_eq_integral_sum (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hy : ∀ x ∈ Set.Ioi (0:ℝ), ∀ z ∈ indices N d D H,
      Integrable (kernel d T a F1 F2 FM W Phi α β z x))
    (hx : ∀ z ∈ indices N d D H, IntegrableOn
      (fun x => ∫ y, kernel d T a F1 F2 FM W Phi α β z x y) (Set.Ioi (0:ℝ))) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Set.Ioi (0:ℝ), ∫ y, ∑ z ∈ indices N d D H,
        kernel d T a F1 F2 FM W Phi α β z x y := by
  rw [literal_eq_sum_integrals,← integral_finsetSum _ hx]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx'
  exact (integral_finsetSum _ (hy x hx')).symm

/-- Positivity of the Mellin argument comes from the actual height cutoff,
not from silently changing the original y integral to positive y. -/
theorem innerKernel_zero_of_nonpos (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x y : ℝ)
    (hT : 0 < T) (hx : 0 ≤ x) (hy : y ≤ 0)
    (hPhi : ∀ t ≤ 0, Phi t = 0) : innerKernel W Phi T z x y = 0 := by
  unfold innerKernel
  rw [hPhi _ (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hx hy) (by positivity))
      (by positivity)) hT.le),mul_zero]

#print axioms literal_eq_sum_integrals
#print axioms literal_eq_integral_sum
#print axioms innerKernel_zero_of_nonpos
#print axioms delta_cutoff_iff
#print axioms h_cutoff_iff
end XiPrime8845.PRZZAStar
