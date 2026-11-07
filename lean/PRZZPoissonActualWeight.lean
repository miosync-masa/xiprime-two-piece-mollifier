import PRZZPoissonTimeChange
import PRZZFullWeightSmooth
import PRZZWeightFourier
import PRZZL1Poisson

/-! Identify the retained W weight with the full differentiated spatial weight.
The reciprocal phase, the extra inverse x from the time Jacobian, and all
outer arithmetic factors are retained. This is after V-to-W and phase
replacement; it does not assert that those replacements have zero error. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff FourierTransform
namespace XiPrime8845.PRZZPoissonActualWeight
open PRZZAStar PRZZKloostermanInputs PRZZPoissonTimeChange
open PRZZDyadicEnvelope PRZZFullWeightSmooth
set_option maxHeartbeats 2000000

theorem frozen_identity (F Phi : ℝ → ℂ) (M T : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (x t : ℝ) (_hM : 0 < M)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hx : 0 < x) :
    (outerKernel (fun y => F (M⁻¹*y)) alpha beta z x /
      ((x*z.1.1*z.1.2:ℝ):ℂ)) * timeKernel (sourceW sigma) Phi T z x t =
      e (-(z.2.2:ℝ)*x) / (((z.1.1:ℝ)*z.1.2:ℝ):ℂ) *
        weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
          ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma x * Phi (t/T) := by
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hn0 : (z.1.1:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (z.1.2:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hp : (x:ℂ)^(-(alpha+beta+1)) = ((x:ℂ)^(alpha+beta)*(x:ℂ))⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_add _ _ hxC,Complex.cpow_one]
  have he : e ((z.2.1:ℝ)*t/(2*Real.pi*(x*z.1.1*z.1.2))) =
      Complex.exp (Complex.I*((((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2))/x:ℝ):ℂ)) := by
    unfold e
    congr 1
    push_cast
    field_simp
  rw [weight_eq _ _ _ _ _ _ _ hx,hp]
  unfold outerKernel timeKernel
  rw [he]
  have hf : (M/(z.1.2:ℝ))⁻¹*x = M⁻¹*(x*z.1.2) := by
    simp only [inv_div]; ring
  have hk : 2*Real.pi*x*(x*z.1.1*z.1.2)/t =
      (2*Real.pi*z.1.1*z.1.2/t)*x^2 := by ring
  rw [hf,hk]
  push_cast
  ring

/-- Exact finite arithmetic aggregation, with no exchange of time and space
integrals. In particular prefactor retains the inverse-residue phase and
the conjugated coefficient; indices retains every strict cutoff. -/
theorem literal_frozen (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) (hM : 0 < M) :
    literal N d D H T a F1 F2 (fun y => F (M⁻¹*y))
      (sourceW sigma) Phi alpha beta =
    ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      ∫ x in Ioi (0:ℝ), ∫ t : ℝ,
        e (-(z.2.2:ℝ)*x) / (((z.1.1:ℝ)*z.1.2:ℝ):ℂ) *
          weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
            ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma x * Phi (t/T) := by
  rw [literal_time_form]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact frozen_identity F Phi M T z alpha beta sigma x t hM
    (by have := (Finset.mem_Icc.mp hn.1).1; omega)
    (by have := (Finset.mem_Icc.mp hn.2).1; omega) hx

/-- The residue phase has unit norm, so the outer arithmetic mass is
exactly the displayed coefficient, cutoff and complex-power mass. -/
theorem prefactor_norm (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : Index) :
    ‖prefactor a F1 F2 d alpha beta z‖ =
      ‖a (d*z.1.1)‖*‖a (d*z.1.2)‖*‖F1 (d*z.1.1)‖*‖F2 (d*z.1.2)‖ /
        ‖(d:ℂ)*(z.1.1:ℂ)^alpha*(z.1.2:ℂ)^beta‖ := by
  simp [prefactor,e,Complex.norm_exp]

/-- Aggregation with the actual outer coefficients, not a count of rows.
The remaining per-row integral norm is retained, not assumed uniformly bounded. -/
theorem literal_arithmetic_bound (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) :
    ‖literal N d D H T a F1 F2 FM W Phi alpha beta‖ ≤
      ∑ z ∈ indices N d D H,
        (‖a (d*z.1.1)‖*‖a (d*z.1.2)‖*‖F1 (d*z.1.1)‖*‖F2 (d*z.1.2)‖ /
          ‖(d:ℂ)*(z.1.1:ℂ)^alpha*(z.1.2:ℂ)^beta‖) *
        ‖∫ x in Ioi (0:ℝ), outerKernel FM alpha beta z x * ∫ y, innerKernel W Phi T z x y‖ := by
  unfold literal
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  rw [norm_mul,prefactor_norm]

/-- Poisson applied to precisely the frozen weight above. Smoothness and
compact support are supplied, not premises about the composite weight.
This is a spatial equality at fixed positive time, not a Fubini theorem. -/
theorem frozen_poisson (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (lo hi M t q residue : ℝ) (z : Index) (alpha beta sigma : ℂ)
    (hlo : 0 < lo) (hM : 0 < M) (ht : 0 < t) (hq : 0 < q)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hsigma : sigma ≠ 0)
    (hs : Function.support F ⊆ Icc lo hi) :
    let f := weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
      ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma
    (∑' n : ℤ, f (residue+q*n)) =
      ∑' n : ℤ, ((q⁻¹:ℝ):ℂ) * 𝓕 f ((n:ℝ)/q) *
        Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(residue:ℂ)/(q:ℂ)) := by
  dsimp only
  apply PRZZL1Poisson.progression_normalized
  · exact PRZZWeightFourier.smooth lo hi hlo F hF _ _ _ _ _
      (by positivity) (by positivity) hsigma hs
  · exact PRZZWeightFourier.compact lo hi hlo F _ _ _ _ _ (by positivity) hs
  · exact hq

#print axioms frozen_poisson
#print axioms prefactor_norm
#print axioms literal_arithmetic_bound
#print axioms frozen_identity
#print axioms literal_frozen
end XiPrime8845.PRZZPoissonActualWeight
