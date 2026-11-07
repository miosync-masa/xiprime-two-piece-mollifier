import PRZZFrozenTail
import PRZZSourceWOuter
import PRZZFilteredResidual

/-! Fubini for the actual frozen spatial weight and time cutoff.
Joint integrability is proved from positive compact supports; it is not
an estimate premise. Zero and negative Fourier modes are not discarded. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform RealInnerProductSpace
open MeasureTheory Set Complex
namespace XiPrime8845.PRZZCentralFubini
open PRZZFullWeightSmooth PRZZDyadicEnvelope
set_option maxHeartbeats 4000000

def kernel (F Phi : ℝ → ℂ) (N u delta T xi : ℝ) (z sigma : ℂ) (x t : ℝ) : ℂ :=
  Complex.exp ((↑(-2*Real.pi*(x*xi)))*I) *
    weight F N (2*Real.pi*u/t) (delta*t/u) z sigma x * Phi (t/T)

theorem kernel_support (F Phi : ℝ → ℂ) (N u delta T xi : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hT : 0 < T)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Function.support (Function.uncurry (kernel F Phi N u delta T xi z sigma)) ⊆
      Icc (N/2) (3*N) ×ˢ Icc T (2*T) := by
  intro p hp
  have hw : weight F N (2*Real.pi*u/p.2) (delta*p.2/u) z sigma p.1 ≠ 0 := by
    intro h; exact hp (by simp [Function.uncurry,kernel,h])
  have ht : Phi (p.2/T) ≠ 0 := by
    intro h; exact hp (by simp [Function.uncurry,kernel,h])
  have hx := PRZZWeightFourier.support_subset (1/2) 3 (by norm_num) F N
    (2*Real.pi*u/p.2) (delta*p.2/u) z sigma hN hsF hw
  have hh := hsP ht
  constructor
  · simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hx
  · constructor
    · simpa only [one_mul] using (le_div_iff₀ hT).mp hh.1
    · exact (div_le_iff₀ hT).mp hh.2

theorem kernel_continuousOn (F Phi : ℝ → ℂ) (hF : Continuous F) (hP : Continuous Phi)
    (N u delta T xi : ℝ) (z sigma : ℂ) (hN : 0 < N) (hu : 0 < u)
    (hT : 0 < T) (hs : sigma ≠ 0) :
    ContinuousOn (Function.uncurry (kernel F Phi N u delta T xi z sigma))
      (Icc (N/2) (3*N) ×ˢ Icc T (2*T)) := by
  intro p hp
  have hx : 0 < p.1 := (by positivity : 0 < N/2).trans_le hp.1.1
  have ht : 0 < p.2 := hT.trans_le hp.2.1
  have hx0 : p.1 ≠ 0 := hx.ne'
  have ht0 : p.2 ≠ 0 := ht.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hT0 : T ≠ 0 := hT.ne'
  have ha : 0 < (2*Real.pi*u/p.2)*p.1^2 := by positivity
  have hw : ContinuousAt (sourceW sigma) ((2*Real.pi*u/p.2)*p.1^2) :=
    (PRZZSourceWOuter.sourceW_continuous sigma hs).continuousAt (Ioi_mem_nhds ha)
  have hc : ContinuousAt (fun q : ℝ × ℝ => sourceW sigma ((2*Real.pi*u/q.2)*q.1^2)) p :=
    hw.comp (f := fun q : ℝ × ℝ => (2*Real.pi*u/q.2)*q.1^2) (by fun_prop)
  have hl : ContinuousAt (fun q : ℝ × ℝ => Real.log q.1) p :=
    (Real.continuousAt_log hx.ne').comp continuousAt_fst
  have hlc := Complex.continuous_ofReal.continuousAt.comp hl
  have hoc : ContinuousAt (fun q : ℝ × ℝ => (delta*q.2/u/q.1:ℝ) : ℝ × ℝ → ℂ) p :=
    Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
  have hfc : ContinuousAt (fun q : ℝ × ℝ => (↑(-2*Real.pi*(q.1*xi)):ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
  change ContinuousWithinAt
    (fun q : ℝ × ℝ => Complex.exp ((↑(-2*Real.pi*(q.1*xi)))*I) *
      (F (N⁻¹*q.1) * Complex.exp (-z*(Real.log q.1:ℂ)) *
        Complex.exp (I*(delta*q.2/u/q.1:ℝ)) *
        sourceW sigma ((2*Real.pi*u/q.2)*q.1^2)) * Phi (q.2/T)) _ p
  exact (show ContinuousAt _ p by fun_prop).continuousWithinAt

theorem kernel_integrable (F Phi : ℝ → ℂ) (hF : Continuous F) (hP : Continuous Phi)
    (N u delta T xi : ℝ) (z sigma : ℂ) (hN : 0 < N) (hu : 0 < u)
    (hT : 0 < T) (hs : sigma ≠ 0)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Integrable (Function.uncurry (kernel F Phi N u delta T xi z sigma))
      (volume.prod volume) := by
  apply (kernel_continuousOn F Phi hF hP N u delta T xi z sigma hN hu hT hs
    |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).integrable_of_forall_notMem_eq_zero
  intro p hp
  by_contra hn
  exact hp (kernel_support F Phi N u delta T xi z sigma hN hT hsF hsP hn)

theorem kernel_fourier (F Phi : ℝ → ℂ) (N u delta T xi : ℝ) (z sigma : ℂ) (t : ℝ) :
    (∫ x : ℝ, kernel F Phi N u delta T xi z sigma x t) =
      Phi (t/T) * 𝓕 (weight F N (2*Real.pi*u/t) (delta*t/u) z sigma) xi := by
  rw [Real.fourier_eq',← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [kernel,RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring

theorem spectrum_integrable (F Phi : ℝ → ℂ) (hF : Continuous F) (hP : Continuous Phi)
    (N u delta T xi : ℝ) (z sigma : ℂ) (hN : 0 < N) (hu : 0 < u)
    (hT : 0 < T) (hs : sigma ≠ 0)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Integrable (fun t : ℝ => Phi (t/T) *
      𝓕 (weight F N (2*Real.pi*u/t) (delta*t/u) z sigma) xi) := by
  have hi := (kernel_integrable F Phi hF hP N u delta T xi z sigma
    hN hu hT hs hsF hsP).integral_prod_right
  simpa only [Function.uncurry,kernel_fourier] using hi

/-- The actual time/spatial integrals may be exchanged, with no supplied
Fubini or measurability premise. -/
theorem kernel_swap (F Phi : ℝ → ℂ) (hF : Continuous F) (hP : Continuous Phi)
    (N u delta T xi : ℝ) (z sigma : ℂ) (hN : 0 < N) (hu : 0 < u)
    (hT : 0 < T) (hs : sigma ≠ 0)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ x in Ioi (0:ℝ), ∫ t : ℝ, kernel F Phi N u delta T xi z sigma x t) =
      ∫ t : ℝ, Phi (t/T) *
        𝓕 (weight F N (2*Real.pi*u/t) (delta*t/u) z sigma) xi := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_integral_swap (kernel_integrable F Phi hF hP N u delta T xi z sigma
      hN hu hT hs hsF hsP)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    exact kernel_fourier F Phi N u delta T xi z sigma t
  · intro x hx
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro t
    have hz : kernel F Phi N u delta T xi z sigma x t = 0 := by
      by_contra hn
      have hh := (kernel_support F Phi N u delta T xi z sigma hN hT hsF hsP
        (show (x,t) ∈ Function.support (Function.uncurry (kernel F Phi N u delta T xi z sigma)) from hn)).1.1
      have hx0 : x ≤ 0 := by simpa only [mem_Ioi,not_lt] using hx
      linarith
    exact hz

/-- Literal A* is the positive retained Fourier family of the actual
frozen weight, integrated in time. All strict original arithmetic cutoffs
and the residue prefactor are retained. -/
theorem literal_fourier (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    PRZZAStar.literal N d D H T a F1 F2 (fun y => F (M⁻¹*y))
      (sourceW sigma) Phi alpha beta =
      ∑ z ∈ PRZZAStar.indices N d D H,
        (PRZZAStar.prefactor a F1 F2 d alpha beta z /
          (((z.1.1:ℝ)*z.1.2:ℝ):ℂ)) *
          ∫ t : ℝ, Phi (t/T) *
            𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) (z.2.2:ℝ) := by
  rw [PRZZPoissonActualWeight.literal_frozen N d D H T M a F1 F2 F Phi alpha beta sigma hM]
  apply Finset.sum_congr rfl
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hu : (0:ℝ) < z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn.1).1
  have hv : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn.2).1
  have he (x t : ℝ) :
      PRZZKloostermanInputs.e (-(z.2.2:ℝ)*x) /
        (((z.1.1:ℝ)*z.1.2:ℝ):ℂ) *
        weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
          ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma x * Phi (t/T) =
      (1/(((z.1.1:ℝ)*z.1.2:ℝ):ℂ)) *
        kernel F Phi (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T z.2.2
          (alpha+beta+1) sigma x t := by
    have hp : PRZZKloostermanInputs.e (-(z.2.2:ℝ)*x) =
        Complex.exp ((↑(-2*Real.pi*(x*(z.2.2:ℝ))))*I) := by
      unfold PRZZKloostermanInputs.e
      congr 1
      push_cast
      ring
    rw [hp]
    simp only [kernel,mul_assoc]
    ring
  simp_rw [he,integral_const_mul]
  rw [kernel_swap F Phi hF hP (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T z.2.2
    (alpha+beta+1) sigma (by positivity) (by positivity) hT hs hsF hsP]
  simp only [PRZZFrozenTail.frozen,mul_assoc]
  ring

/-- The central positive-frequency sum is inside the time integral.
Finite arithmetic summation is exchanged using the proved integrability
of each actual Fourier weight, not an assumed interchange identity. -/
theorem literal_fourier_time (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    PRZZAStar.literal N d D H T a F1 F2 (fun y => F (M⁻¹*y))
      (sourceW sigma) Phi alpha beta =
      ∫ t : ℝ, ∑ z ∈ PRZZAStar.indices N d D H,
        (PRZZAStar.prefactor a F1 F2 d alpha beta z /
          (((z.1.1:ℝ)*z.1.2:ℝ):ℂ)) *
          (Phi (t/T) * 𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) (z.2.2:ℝ)) := by
  rw [literal_fourier N d D H T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro z hz
    exact (integral_const_mul _ _).symm
  · intro z hz
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    have hu : (0:ℝ) < z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn.1).1
    have hv : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn.2).1
    apply Integrable.const_mul
    simpa only [PRZZFrozenTail.frozen,mul_assoc] using
      spectrum_integrable F Phi hF hP (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T z.2.2
        (alpha+beta+1) sigma (by positivity) (by positivity) hT hs hsF hsP

/-- Identify the genuine normalized Poisson modes with literal A*,
including the arithmetic shift-slot convention. This is only the positive
strictly retained h-family: the central zero/negative modes stay separate. -/
theorem positive_modes_literal (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ t : ℝ, ∑ z ∈ PRZZAStar.indices N d D H, Phi (t/T) *
      (PRZZUnfrozenPoisson.arithmetic a F1 F2 d alpha beta z /
        ((z.1.1:ℂ)*(z.1.2:ℂ)) *
        PRZZCentralTail.mode F M 1 (PRZZCentralTail.residue z/z.1.2) z
          beta alpha sigma t (z.2.2:ℤ))) =
      PRZZAStar.literal N d D H T a F1 F2 (fun y => F (M⁻¹*y))
        (sourceW sigma) Phi alpha beta := by
  rw [literal_fourier_time N d D H T M a F1 F2 F Phi alpha beta sigma
    hF hP hT hM hs hsF hsP]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply Finset.sum_congr rfl
  intro z hz
  rw [PRZZFilteredResidual.normalized_mode a F1 F2 F d beta alpha sigma z M t z.2.2,
    PRZZFilteredResidual.signedPrefactor_nat]
  simp only [PRZZFrozenTail.frozen,add_comm beta alpha,Int.cast_natCast,
    Complex.ofReal_mul,Complex.ofReal_natCast]
  ring

#print axioms positive_modes_literal
#print axioms literal_fourier_time
#print axioms literal_fourier
#print axioms kernel_fourier
#print axioms spectrum_integrable
#print axioms kernel_support
#print axioms kernel_continuousOn
#print axioms kernel_integrable
#print axioms kernel_swap
end XiPrime8845.PRZZCentralFubini
