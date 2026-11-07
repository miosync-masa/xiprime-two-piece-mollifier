import PRZZAllPoissonAFE
import PRZZSourceBoundaryDecay
import PRZZSourceWindowCutoff

/-! The actual cover-boundary in resolved Poisson rows. A sourceW cap is
supplied once for the whole scaled cutoff family. The unrestricted growing
family still requires summing its displayed arithmetic cap. -/
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory Finset
namespace XiPrime8845.PRZZResolvedBoundary
open PRZZSourceBoundaryDecay
set_option maxHeartbeats 5000000

theorem cover_bound (F : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ (L : ℕ) (M T t : ℝ) (z : PRZZAStar.Index) (a b sigma : ℂ),
      0 < M → 0 < T → t ∈ Icc T (2*T) → 0 < z.1.1 → 0 < z.1.2 →
      sigma ≠ 0 → 0 ≤ (a+b+1).re → |(z.2.1:ℝ)| ≤ M*z.1.1/4 →
      ‖PRZZWeightedSourcePoisson.boundary L (PRZZActualPoissonError.cover L M z)
        F M z a b sigma t‖ ≤ cap CF T z a b sigma*tail L := by
  obtain ⟨CF,hCF,hc⟩ := cutoff_cap F hF hsF
  refine ⟨CF,hCF,?_⟩
  intro L M T t z a b sigma hM hT ht hu hv hs hab hg
  have hLB := (PRZZActualPoissonError.cover_bounds L M z hv).1
  let f : ℤ × ℤ → ℂ := fun p => if p.1*z.1.1-p.2*z.1.2= -z.2.1 then
    PRZZSourceLattice.source F M z a b sigma t p.1 else 0
  have he := boundary_integer L (PRZZActualPoissonError.cover L M z) hLB f
  change ‖∑ p ∈ _, f p‖ ≤ _
  rw [← he]
  apply boundary_bound L _ hLB _ _ (by unfold cap PRZZWArithmeticCutoff.decayConstant; positivity)
  intro p
  simpa only [f,row,Int.cast_natCast,Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_one] using row_bound F CF M T t z a b sigma
    hCF hc hsF hM hT ht hu hv hs hab hg p

theorem cover_time (F : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ (L : ℕ) (M T : ℝ) (z : PRZZAStar.Index) (a b sigma c : ℂ)
      (phi : ℝ → ℂ), 0 < M → 0 < T → 0 < z.1.1 → 0 < z.1.2 → sigma ≠ 0 →
      0 ≤ (a+b+1).re → |(z.2.1:ℝ)| ≤ M*z.1.1/4 → Continuous phi →
      ‖∫ t in Icc T (2*T), c*phi t*PRZZWeightedSourcePoisson.boundary L
        (PRZZActualPoissonError.cover L M z) F M z a b sigma t‖ ≤
        ‖c‖*cap CF T z a b sigma*tail L*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨CF,hCF,h⟩ := cover_bound F hF hsF
  refine ⟨CF,hCF,?_⟩
  intro L M T z a b sigma c phi hM hT hu hv hs hab hg hp
  let D := ‖c‖*cap CF T z a b sigma*tail L
  have hi : IntegrableOn (fun t : ℝ => D*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hp.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_left (h L M T t z a b sigma hM hT ht hu hv hs hab hg)
      (mul_nonneg (norm_nonneg c) (norm_nonneg (phi t)))).trans_eq (by dsimp [D]; ring)

/-- Uniform exact disappearance on the bounded spatial part, for the
same cover as the exhaustive family; no fixed-family assumption is used. -/
theorem bounded_cover_zero (L N : ℕ) (X M t : ℝ) (F : ℝ → ℂ) (z : PRZZAStar.Index)
    (a b sigma : ℂ) (hN : 1 ≤ (N:ℝ)) (hM : 0 < M) (hMX : M ≤ X)
    (hu : 0 < z.1.1) (huN : z.1.1 ≤ N) (hv : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hg : |(z.2.1:ℝ)| ≤ M*z.1.1/4) (hL : 4*(N:ℝ)*X ≤ L) :
    PRZZWeightedSourcePoisson.boundary L (PRZZActualPoissonError.cover L M z) F M z a b sigma t = 0 := by
  exact PRZZSourceWindowCutoff.boundary_zero L _ N X F M t z a b sigma hN hM hMX hu
    (by exact_mod_cast huN) hv hsF hg hL

#print axioms cover_bound
#print axioms cover_time
#print axioms bounded_cover_zero
end XiPrime8845.PRZZResolvedBoundary
