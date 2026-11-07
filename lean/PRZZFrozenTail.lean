import PRZZPoissonActualWeight
import PRZZFourierTime

/-! Match the actual frozen Poisson weight and residue phases to the
two-sided tail used in the proved time-interchange theorem. No assertion
that an arithmetic sharp cutoff is a smooth spatial cutoff is made. -/
noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform ContDiff
namespace XiPrime8845.PRZZFrozenTail
open PRZZAStar PRZZFullWeightSmooth
set_option maxHeartbeats 3000000

def phase (q residue v : ℝ) : ℂ :=
  Complex.exp (2*Real.pi*I*(v:ℂ)*(residue:ℂ)/(q:ℂ))

theorem phase_norm (q residue v : ℝ) : ‖phase q residue v‖ = 1 := by
  simp [phase,Complex.norm_exp]

def frozen (F : ℝ → ℂ) (M : ℝ) (z : Index) (alpha beta sigma : ℂ) (t : ℝ) :=
  weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
    ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma

def pair (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (H j : ℕ) (t : ℝ) : ℂ :=
  ((q⁻¹:ℝ):ℂ)*𝓕 (frozen F M z alpha beta sigma t) (((H+j:ℝ)+1)/q)*
      phase q residue ((H+j:ℝ)+1) +
  ((q⁻¹:ℝ):ℂ)*𝓕 (frozen F M z alpha beta sigma t) (-(((H+j:ℝ)+1)/q))*
      phase q residue (-((H+j:ℝ)+1))

/-- Exact normalization and sign matching, including q inverse. -/
theorem pair_eq (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (H j : ℕ) (t : ℝ) (hq : q ≠ 0) :
    pair F M q residue z alpha beta sigma H j t =
      PRZZFourierTime.term F (M/z.1.2) ((z.1.1:ℝ)*z.1.2*q) q ((z.2.1:ℝ)*q)
        (alpha+beta+1) sigma H j
        (fun j => phase q residue ((H+j:ℝ)+1))
        (fun j => phase q residue (-((H+j:ℝ)+1))) t := by
  have hk : 2*Real.pi*((z.1.1:ℝ)*z.1.2*q)/(t*q) = 2*Real.pi*z.1.1*z.1.2/t := by
    field_simp
  have ho : ((z.2.1:ℝ)*q)*t/((z.1.1:ℝ)*z.1.2*q) =
      (z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2) := by field_simp
  simp only [pair,frozen,PRZZFourierTime.term,hk,ho,Complex.real_smul]
  ring

/-- The actual residue phases have unit norm; all time measurability and
summable domination are supplied by the Fourier theorem, not assumed. -/
theorem time_swap (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M q residue : ℝ) (z : Index) (alpha beta sigma : ℂ) (H : ℕ)
    (hT : 0 < T) (hM : 0 < M) (hq : 0 < q)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hs : sigma ≠ 0)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∑' j, ∫ t in Icc T (2*T), Phi (t/T)*pair F M q residue z alpha beta sigma H j t) =
      ∫ t in Icc T (2*T), ∑' j, Phi (t/T)*pair F M q residue z alpha beta sigma H j t := by
  simp_rw [pair_eq F M q residue z alpha beta sigma H _ _ hq.ne']
  exact PRZZFourierTime.actual_swap F hF hsF T (M/z.1.2)
    ((z.1.1:ℝ)*z.1.2*q) q ((z.2.1:ℝ)*q) (alpha+beta+1) sigma H _ _
    hT (by positivity) (by positivity) hq hs
    (fun j => (phase_norm _ _ _).le) (fun j => (phase_norm _ _ _).le) Phi hPhi

/-- Return to the original spatial variable y = n2*x. In particular the
source scale is M, not M/n2, and the reciprocal phase has denominator n1.
The complex-power dilation factor must not be discarded. -/
theorem frozen_dilation (F : ℝ → ℂ) (M : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t y : ℝ) (hm : 0 < z.1.2) (hy : 0 < y) :
    frozen F M z alpha beta sigma t (y/z.1.2) =
      Complex.exp ((alpha+beta+1)*(Real.log (z.1.2:ℝ):ℂ)) *
        weight F M (2*Real.pi*z.1.1/(t*z.1.2))
          ((z.2.1:ℝ)*t/z.1.1) (alpha+beta+1) sigma y := by
  have hv : (z.1.2:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcut : (M/(z.1.2:ℝ))⁻¹*(y/z.1.2) = M⁻¹*y := by
    simp only [inv_div]; field_simp
  have hk : (2*Real.pi*z.1.1*z.1.2/t)*(y/(z.1.2:ℝ))^2 =
      (2*Real.pi*z.1.1/(t*z.1.2))*y^2 := by field_simp
  have ho : ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2))/(y/z.1.2) =
      ((z.2.1:ℝ)*t/z.1.1)/y := by field_simp
  unfold frozen weight
  rw [hcut,hk,ho,Real.log_div hy.ne' hv,Complex.ofReal_sub]
  rw [show -(alpha+beta+1)*((Real.log y:ℂ)-↑(Real.log (z.1.2:ℝ))) =
    (alpha+beta+1)*↑(Real.log (z.1.2:ℝ)) + -(alpha+beta+1)*(Real.log y:ℂ) by ring,
    Complex.exp_add]
  ring

/-- The spatial dilation Jacobian cancels exactly the extra inverse-x
power. The remaining factor is the one bounded in PRZZDualError. -/
theorem jacobian_dilation (v : ℝ) (alpha beta : ℂ) (hv : 0 < v) :
    ((v⁻¹:ℝ):ℂ)*Complex.exp ((alpha+beta+1)*(Real.log v:ℂ)) =
      Complex.exp ((alpha+beta)*(Real.log v:ℂ)) := by
  have he : Complex.exp (Real.log v:ℂ) = (v:ℂ) := by
    rw [← Complex.ofReal_exp,Real.exp_log hv]
  rw [show (alpha+beta+1)*(Real.log v:ℂ) =
    (alpha+beta)*(Real.log v:ℂ)+(Real.log v:ℂ) by ring,Complex.exp_add,he]
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  push_cast
  field_simp

/-- Fourier dilation for the actual supported weight, including reciprocal
frequency and the complex-power factor after the Jacobian cancellation. -/
theorem frozen_fourier (F : ℝ → ℂ) (M : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t ξ : ℝ) (hM : 0 < M) (hm : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    𝓕 (frozen F M z alpha beta sigma t) ξ =
      Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ)) *
        𝓕 (weight F M (2*Real.pi*z.1.1/(t*z.1.2))
          ((z.2.1:ℝ)*t/z.1.1) (alpha+beta+1) sigma) (ξ/z.1.2) := by
  let v : ℝ := z.1.2
  let g := weight F M (2*Real.pi*z.1.1/(t*z.1.2))
    ((z.2.1:ℝ)*t/z.1.1) (alpha+beta+1) sigma
  let C := Complex.exp ((alpha+beta+1)*(Real.log v:ℂ))
  have hv : 0 < v := by dsimp [v]; exact_mod_cast hm
  have hfzero : ∀ r : ℝ, r ≤ 0 → F r = 0 := by
    intro r hr
    by_contra hn
    have hh := hsF hn
    linarith [hh.1]
  have he : ∀ x : ℝ, frozen F M z alpha beta sigma t x = C*g (v*x) := by
    intro x
    by_cases hx : 0 < x
    · have hh := frozen_dilation F M z alpha beta sigma t (v*x) hm (mul_pos hv hx)
      simpa only [v,mul_div_cancel_left₀ x (show (z.1.2:ℝ) ≠ 0 by exact_mod_cast hm.ne')] using hh
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      have h1 := hfzero ((M/(z.1.2:ℝ))⁻¹*x)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx0)
      have h2 := hfzero (M⁻¹*(v*x))
        (mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonneg_of_nonpos hv.le hx0))
      simp only [frozen,weight,g,h1,h2,zero_mul,mul_zero]
  calc
    _ = C*𝓕 (PRZZL1Poisson.scaled g v) ξ := by
      rw [Real.fourier_eq',Real.fourier_eq',← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [he]
      simp only [PRZZL1Poisson.scaled,smul_eq_mul]
      ring
    _ = (v⁻¹:ℂ)*C*𝓕 g (ξ/v) := by
      rw [PRZZL1Poisson.scaled_fourier g v ξ hv]
      simp only [Complex.real_smul,Complex.ofReal_inv]
      ring
    _ = _ := by
      rw [show (v⁻¹:ℂ)*C = Complex.exp ((alpha+beta)*(Real.log v:ℂ)) by
        simpa only [C,Complex.ofReal_inv] using jacobian_dilation v alpha beta hv]

#print axioms frozen_fourier
#print axioms jacobian_dilation
#print axioms frozen_dilation
#print axioms phase_norm
#print axioms pair_eq
#print axioms time_swap
end XiPrime8845.PRZZFrozenTail
