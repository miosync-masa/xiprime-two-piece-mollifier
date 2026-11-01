import PRZZActualMellin

/-! A common window for one original dyadic coefficient box. Insert this
window before Mellin inversion; its indicator must survive inversion.
The area bound is uniform in M and retains the crucial factor 1/(X*V).
This module does not supply the uniform analytic W/shift envelope. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Complex
namespace XiPrime8845.PRZZDyadicWindow
open PRZZAStar PRZZAStarMellin PRZZActualMellin
set_option maxHeartbeats 2000000

def box (T M X V : ℝ) : Set (ℝ × ℝ) :=
  Icc (M/(4*V)) (3*M/V) ×ˢ Icc (T/(12*M*X)) (8*T/(M*X))

theorem support_box (d : ℕ) (T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (h1 : (z.1.1:ℝ) ∈ Icc X (2*X)) (h2 : (z.1.2:ℝ) ∈ Icc V (2*V))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Function.support (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) ⊆
      box T M X V := by
  intro p hp
  have hm : FM (p.1*z.1.2) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,outerKernel,hz])
  have hph : Phi (p.1*p.2*z.1.1*z.1.2/T) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,innerKernel,hz])
  have hm' := hsM hm
  have hp' := hsP hph
  have hlo := (le_div_iff₀ hT).mp hp'.1
  have hhi := (div_le_iff₀ hT).mp hp'.2
  have hn1 : 0 < (z.1.1:ℝ) := hX.trans_le h1.1
  have hn2 : 0 < (z.1.2:ℝ) := hV.trans_le h2.1
  have hx : 0 < p.1 := by nlinarith only [hm'.1,hn2,hM]
  have hy : 0 < p.2 := by
    by_contra hh
    have hh' := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hx.le (le_of_not_gt hh)) hn1.le) hn2.le
    linarith only [hlo,hh',hT]
  have hxlo := mul_le_mul_of_nonneg_left h2.2 hx.le
  have hxhi := mul_le_mul_of_nonneg_left h2.1 hx.le
  have hylo := mul_le_mul_of_nonneg_right hm'.2 (mul_pos hy hn1).le
  have hylo' := mul_le_mul_of_nonneg_left h1.2 (by positivity : 0 ≤ p.2*(3*M))
  have hyhi := mul_le_mul_of_nonneg_right hm'.1 (mul_pos hy hn1).le
  have hyhi' := mul_le_mul_of_nonneg_left h1.1 (by positivity : 0 ≤ p.2*(M/2))
  refine ⟨⟨(div_le_iff₀ (by positivity : 0 < 4*V)).mpr ?_,
    (le_div_iff₀ hV).mpr ?_⟩,⟨(div_le_iff₀ (by positivity : 0 < 12*M*X)).mpr ?_,
    (le_div_iff₀ (mul_pos hM hX)).mpr ?_⟩⟩
  · nlinarith only [hm'.1,hxlo]
  · nlinarith only [hm'.2,hxhi]
  · nlinarith only [hlo,hylo,hylo',mul_pos hy (mul_pos hM hX)]
  · nlinarith only [hhi,hyhi,hyhi',hT]

theorem indicator_kernel (d : ℕ) (T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (h1 : (z.1.1:ℝ) ∈ Icc X (2*X)) (h2 : (z.1.2:ℝ) ∈ Icc V (2*V))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (box T M X V).indicator
      (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) =
      (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) :=
  Set.indicator_eq_self.mpr (support_box d T M X V a F1 F2 FM W Phi α β z
    hT hM hX hV h1 h2 hsM hsP)

/-- The original coefficient cutoffs supply the box membership, even for
the full original index set. No arithmetic condition or phase is dropped. -/
theorem support_box_of_cutoffs (d : ℕ) (T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hs1 : Function.support F1 ⊆ Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Function.support (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) ⊆
      box T M X V := by
  intro p hp
  have hf1 : F1 (d*z.1.1) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,prefactor,hz])
  have hf2 : F2 (d*z.1.2) ≠ 0 := by
    intro hz; exact hp (by simp [kernel,prefactor,hz])
  have h1 := hs1 hf1
  have h2 := hs2 hf2
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hn1 : (z.1.1:ℝ) ∈ Icc X (2*X) := by
    constructor <;> nlinarith only [h1.1,h1.2,hd0]
  have hn2 : (z.1.2:ℝ) ∈ Icc V (2*V) := by
    constructor <;> nlinarith only [h2.1,h2.2,hd0]
  exact support_box d T M X V a F1 F2 FM W Phi α β z hT hM hX hV hn1 hn2 hsM hsP hp

theorem literal_box (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM) (hW : Continuous W) (hPhi : Continuous Phi)
    (hs1 : Function.support F1 ⊆ Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Ioi (0:ℝ), ∫ y, (box T M X V).indicator
        (fun p : ℝ × ℝ => ∑ z ∈ indices N d D H,
          kernel d T a F1 F2 FM W Phi α β z p.1 p.2) (x,y) := by
  rw [PRZZAStarFubini.literal_eq_integral_sum N d D H T (M/2) (3*M) a
    F1 F2 FM W Phi α β hFM hW hPhi hsM hsP (by positivity) (by positivity) hT]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  by_cases hp : (x,y) ∈ box T M X V
  · simp [hp]
  · rw [Set.indicator_of_notMem hp]
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hh
    exact hp (support_box_of_cutoffs d T M X V a F1 F2 FM W Phi α β z
      hd hT hM hX hV hs1 hs2 hsM hsP hh)

theorem volume_bound (T M X V : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V) :
    volume.real (box T M X V) ≤ 24*T/(X*V) := by
  rw [box,Measure.volume_eq_prod,measureReal_prod_prod,Real.volume_real_Icc,Real.volume_real_Icc]
  calc
    _ ≤ (3*M/V)*(8*T/(M*X)) := by
      apply mul_le_mul
      · exact max_le (sub_le_self _ (by positivity)) (by positivity)
      · exact max_le (sub_le_self _ (by positivity)) (by positivity)
      · exact le_max_right _ _
      · positivity
    _ = _ := by field_simp; ring

/-- The analytic envelope is explicit; the geometric constant is independent
of every scale, in particular M. A uniform W/shift supplier remains separate. -/
theorem mass_bound (T M X V C d : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V) (hC : 0 ≤ C) (hd : 0 < d)
    (f : ℝ × ℝ → ℂ) (hf : Integrable f)
    (hs : Function.support f ⊆ box T M X V)
    (hb : ∀ p ∈ box T M X V, ‖f p‖ ≤ C/d) :
    (∫ p, ‖f p‖) ≤ 24*C*T/(d*X*V) := by
  have hm : MeasurableSet (box T M X V) := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hi : Integrable ((box T M X V).indicator (fun _ : ℝ × ℝ => C/d)) :=
    (integrable_indicator_iff hm).mpr
      (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
  have hp : ∀ p, ‖f p‖ ≤ (box T M X V).indicator (fun _ => C/d) p := by
    intro p
    by_cases h : p ∈ box T M X V
    · simpa only [Set.indicator_of_mem h] using hb p h
    · have hz : f p = 0 := by by_contra hz; exact h (hs hz)
      simp [h,hz]
  calc
    _ ≤ ∫ p, (box T M X V).indicator (fun _ : ℝ × ℝ => C/d) p := integral_mono hf.norm hi hp
    _ = volume.real (box T M X V)*(C/d) := by rw [integral_indicator hm,setIntegral_const]; rfl
    _ ≤ (24*T/(X*V))*(C/d) := mul_le_mul_of_nonneg_right
      (volume_bound T M X V hT hM hX hV) (div_nonneg hC hd.le)
    _ = _ := by ring

/-- Restrict the already integrable Mellin kernel without discarding its
original common-window indicator. This supplies Fubini for the sharper box. -/
theorem dyadic_swap (N d : ℕ) (T A B M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    (∫ p, ∫ t, (box T M X V).indicator
      (fun p => localized N d T A B a F1 F2 FM W Phi α β z p t) p) =
    ∫ t, ∫ p, (box T M X V).indicator
      (fun p => localized N d T A B a F1 F2 FM W Phi α β z p t) p := by
  have hm : MeasurableSet (box T M X V) := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hi := (localized_integrable N d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hs hN hT hA hB hn1 hn2).indicator
      (hm.preimage measurable_fst)
  apply integral_integral_swap
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro q
  by_cases hp : q.1 ∈ box T M X V <;> simp [Set.indicator,Function.uncurry,hp]

#print axioms support_box
#print axioms indicator_kernel
#print axioms support_box_of_cutoffs
#print axioms literal_box
#print axioms volume_bound
#print axioms mass_bound
#print axioms dyadic_swap
end XiPrime8845.PRZZDyadicWindow
