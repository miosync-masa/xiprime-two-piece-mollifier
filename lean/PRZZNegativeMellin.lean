import PRZZNegativeArithmetic

/-! The actual negative signed literal, not a replacement model. Unit phase
modulation preserves joint integrability and the original positive window.
Time substitution retains its Jacobian and the inverse-residue phase. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex Finset
namespace XiPrime8845.PRZZNegativeMellin
open PRZZAStar PRZZAStarWindow PRZZAStarMellin PRZZMellinSeparation
open PRZZNegativeArithmetic PRZZPoissonTimeChange
open PRZZKloostermanInputs
set_option maxHeartbeats 5000000

def modulation (z : Index) (x : ℝ) : ℂ :=
  PRZZKloostermanInputs.e (2*(z.2.2:ℝ)*x)*
    PRZZKloostermanInputs.e (2*(z.2.2:ℝ)*(z.2.1:ℝ)*inverseResidue z.1.2 z.1.1/z.1.2)

theorem modulation_norm (z : Index) (x : ℝ) : ‖modulation z x‖ = 1 := by
  simp [modulation,PRZZKloostermanInputs.e,Complex.norm_exp]

theorem phase_prefactor (d : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta : ℂ) (z : Index) (x : ℝ) :
    modulation z x*prefactor a F1 F2 d alpha beta z*PRZZKloostermanInputs.e (-(z.2.2:ℝ)*x) =
      PRZZFilteredResidual.signedPrefactor a F1 F2 d beta alpha z (-(z.2.2:ℤ))*
        PRZZKloostermanInputs.e ((z.2.2:ℝ)*x) := by
  have he (u : ℝ) : PRZZKloostermanInputs.e (2*u)*PRZZKloostermanInputs.e (-u) =
      PRZZKloostermanInputs.e u := by
    unfold PRZZKloostermanInputs.e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hx := he ((z.2.2:ℝ)*x)
  have hr := he ((z.2.2:ℝ)*(z.2.1:ℝ)*inverseResidue z.1.2 z.1.1/z.1.2)
  unfold modulation prefactor PRZZFilteredResidual.signedPrefactor PRZZUnfrozenPoisson.arithmetic
  simp only [Int.cast_neg,Int.cast_natCast,neg_mul,neg_neg]
  convert congrArg (fun c : ℂ =>
    (a (d*z.1.1)*star (a (d*z.1.2))*F1 (d*z.1.1)*F2 (d*z.1.2)/
    ((d:ℂ)*(z.1.1:ℂ)^alpha*(z.1.2:ℂ)^beta))*c) (congrArg₂ (fun u v : ℂ => u*v) hr hx) using 1 <;>
    ring_nf at *

theorem amplitude_modulation (d : ℕ) (a : ℕ → ℂ) (F1 F2 FM W : ℝ → ℂ)
    (alpha beta : ℂ) (z : Index) (x y : ℝ) :
    modulation z x*amplitude d a F1 F2 FM W alpha beta x y z =
      amplitudeMinus d a F1 F2 FM W alpha beta x y z := by
  have h := phase_prefactor d a F1 F2 alpha beta z x
  unfold amplitude outerKernel amplitudeMinus
  convert congrArg (fun c : ℂ => c*FM (x*z.1.2)/(x:ℂ)^(alpha+beta)*
    PRZZKloostermanInputs.e ((z.2.1:ℝ)*y/(2*Real.pi))*W (2*Real.pi*x/y)) h using 1 <;> ring

theorem physical_original (d : ℕ) (a : ℕ → ℂ) (F1 F2 F Phi : ℝ → ℂ)
    (M T : ℝ) (alpha beta sigma : ℂ) (z : Index) (x t : ℝ)
    (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hx : 0 < x) :
    (PRZZFilteredResidual.signedPrefactor a F1 F2 d beta alpha z (-(z.2.2:ℤ))/
      ((z.1.1:ℂ)*(z.1.2:ℂ)))*
      PRZZCentralFubini.kernel F Phi (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T (-(z.2.2:ℝ))
        (alpha+beta+1) sigma x t =
    (modulation z x*prefactor a F1 F2 d alpha beta z)*
      ((outerKernel (fun y => F (M⁻¹*y)) alpha beta z x/((x*z.1.1*z.1.2:ℝ):ℂ))*
        timeKernel (PRZZDyadicEnvelope.sourceW sigma) Phi T z x t) := by
  rw [PRZZPoissonActualWeight.frozen_identity F Phi M T z alpha beta sigma x t hM hu hv hx]
  have he : Complex.exp ((↑(-2*Real.pi*(x*(-(z.2.2:ℝ)))))*I) =
      PRZZKloostermanInputs.e ((z.2.2:ℝ)*x) := by
    unfold PRZZKloostermanInputs.e
    congr 1
    push_cast
    ring
  unfold PRZZCentralFubini.kernel
  rw [he]
  have hh := phase_prefactor d a F1 F2 alpha beta z x
  push_cast
  convert congrArg (fun c : ℂ => c/((z.1.1:ℂ)*(z.1.2:ℂ))*
    PRZZFullWeightSmooth.weight F (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
      ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma x*Phi (t/T)) hh.symm using 1 <;> ring

theorem literal_original (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) (hM : 0 < M) :
    PRZZSignedCentral.signedLiteral (-1) N d D H T M a F1 F2 F Phi alpha beta sigma =
      ∑ z ∈ indices N d D H, ∫ x in Ioi (0:ℝ), ∫ y : ℝ,
        modulation z x*kernel d T a F1 F2 (fun y => F (M⁻¹*y))
          (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z x y := by
  unfold PRZZSignedCentral.signedLiteral
  simp only [Int.cast_neg,Int.cast_one,neg_mul,one_mul]
  apply sum_congr rfl
  intro z hz
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  have hu : 0 < z.1.1 := by have := (mem_Icc.mp hn.1).1; omega
  have hv : 0 < z.1.2 := by have := (mem_Icc.mp hn.2).1; omega
  rw [← integral_const_mul]
  have he (t : ℝ) := physical_original d a F1 F2 F Phi M T alpha beta sigma z x t hM hu hv hx
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul,time_integral _ _ _ _ _ hx hu hv]
  unfold kernel
  simp_rw [integral_const_mul]
  have hx0 : 0 < x := hx
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hc : ((x*z.1.1*z.1.2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (show x*(z.1.1:ℝ)*z.1.2 ≠ 0 by positivity)
  field_simp
  <;> ring

def localizedMinus (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (z : Index) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
  modulation z p.1*PRZZActualMellin.localized N d T A B a F1 F2 FM W Phi alpha beta z p t

theorem localized_integrable (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) :
    Integrable (Function.uncurry (localizedMinus N d T A B a F1 F2 FM W Phi alpha beta z)) := by
  have hi := PRZZPositiveMellin.localized_integrable_positive N d T A B a F1 F2 FM W Phi
    alpha beta z hFM hW hPhi hsP hN hT hA hB hu hv
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => modulation z q.1.1) := by
    unfold modulation PRZZKloostermanInputs.e
    fun_prop
  have hh := hi.mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q => (modulation_norm z q.1.1).le))
  convert hh using 1
  funext q
  exact mul_comm _ _

theorem localized_sum (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (p : ℝ × ℝ) (t : ℝ) :
    (∑ z ∈ indices N d D H, localizedMinus N d T A B a F1 F2 FM W Phi alpha beta z p t) =
      PRZZAStarIntegralBound.common N d T A B W alpha beta p*mellin Phi (t*I)*
        twist (p.1*p.2/T) t*negativeSum N d D H a F1 F2 FM alpha beta p.1 p.2 t := by
  by_cases hp : p ∈ window N T A B
  · simp only [localizedMinus,PRZZActualMellin.localized,Set.indicator_of_mem hp,
      PRZZAStarIntegralBound.common]
    have he (z : Index) : modulation z p.1*
        (amplitude d a F1 F2 FM W alpha beta p.1 p.2 z*mellin Phi (t*I)*
          (twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t)) =
        (mellin Phi (t*I)*twist (p.1*p.2/T) t)*
          (amplitudeMinus d a F1 F2 FM W alpha beta p.1 p.2 z*twist z.1.1 t*twist z.1.2 t) := by
      rw [← amplitude_modulation]
      ring
    simp_rw [he]
    rw [← mul_sum,amplitude_negative]
    ring
  · simp [localizedMinus,PRZZActualMellin.localized,PRZZAStarIntegralBound.common,hp]

theorem row_mellin (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hz : z ∈ indices N d D H) :
    (∫ x in Ioi (0:ℝ), ∫ y : ℝ, modulation z x*kernel d T a F1 F2 FM W Phi alpha beta z x y) =
      (1/(2*Real.pi):ℂ)*∫ q : (ℝ × ℝ) × ℝ,
        localizedMinus N d T A B a F1 F2 FM W Phi alpha beta z q.1 q.2 := by
  have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  have hu : 0 < z.1.1 := by have := (mem_Icc.mp hn.1).1; omega
  have hv : 0 < z.1.2 := by have := (mem_Icc.mp hn.2).1; omega
  have hbase := PRZZPositiveMellin.kernel_integrable_positive d T A B a F1 F2 FM W Phi
    alpha beta z hFM hW hPhi.continuous hsM hsP hA hB hT hu hv
  have hm : Measurable (fun p : ℝ × ℝ => modulation z p.1) := by
    unfold modulation PRZZKloostermanInputs.e
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => modulation z p.1*kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2) := by
    convert hbase.mul_bdd hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (modulation_norm z p.1).le)) using 1
    funext p
    exact mul_comm _ _
  have hj := localized_integrable N d T A B a F1 F2 FM W Phi alpha beta z hFM hW hPhi hsP
    hN hT hA hB hu hv
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← integral_prod _ hi]
    calc
      _ = ∫ p : ℝ × ℝ, (1/(2*Real.pi):ℂ)*∫ t : ℝ,
          localizedMinus N d T A B a F1 F2 FM W Phi alpha beta z p t := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro p
        dsimp only
        rw [PRZZAStarTransform.kernel_inversion N d D H T A B a F1 F2 FM W Phi alpha beta z
          hPhi hsP hsM hN hT hA hB hz p]
        simp only [localizedMinus]
        rw [integral_const_mul]
        ring
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        simpa only [Function.uncurry,← MeasureTheory.Measure.volume_eq_prod] using (integral_prod _ hj).symm
  · intro x hx
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    have hp : (x,y) ∉ window N T A B := by
      intro hp
      exact hx ((div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1)
    have he := congrFun (PRZZAStarWindow.indicator_kernel N d D H T A B a F1 F2 FM W Phi
      alpha beta z hsM hsP hA hB hT hz) (x,y)
    have hk : kernel d T a F1 F2 FM W Phi alpha beta z x y = 0 := by
      simpa only [Set.indicator_of_notMem hp] using he.symm
    simp [hk]

/-- Exact product-space Mellin representation of the actual negative
signedLiteral. Both original support indicators and all finite masks remain. -/
theorem literal_mellin (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hPhi : ContDiff ℝ ∞ Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M) (hs : sigma ≠ 0) :
    PRZZSignedCentral.signedLiteral (-1) N d D H T M a F1 F2 F Phi alpha beta sigma =
      (1/(2*Real.pi):ℂ)*∫ q : (ℝ × ℝ) × ℝ,
        ∑ z ∈ indices N d D H, localizedMinus N d T (M/2) (3*M) a F1 F2
          (fun y => F (M⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z q.1 q.2 := by
  have hFM : Continuous (fun y => F (M⁻¹*y)) := hF.comp (continuous_const.mul continuous_id)
  have hsM : Function.support (fun y => F (M⁻¹*y)) ⊆ Icc (M/2) (3*M) := by
    intro y hy
    have hh := hsF hy
    have he : M⁻¹*y = y/M := by ring
    rw [he] at hh
    constructor
    · have := (le_div_iff₀ hM).mp hh.1; linarith
    · exact (div_le_iff₀ hM).mp hh.2
  have hW := PRZZSourceWOuter.sourceW_continuous sigma hs
  rw [literal_original N d D H T M a F1 F2 F Phi alpha beta sigma hM]
  have he : (∑ z ∈ indices N d D H, ∫ x in Ioi (0:ℝ), ∫ y : ℝ,
      modulation z x*kernel d T a F1 F2 (fun y => F (M⁻¹*y))
        (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z x y) =
      ∑ z ∈ indices N d D H, (1/(2*Real.pi):ℂ)*∫ q : (ℝ × ℝ) × ℝ,
        localizedMinus N d T (M/2) (3*M) a F1 F2 (fun y => F (M⁻¹*y))
          (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z q.1 q.2 := by
    apply sum_congr rfl
    intro z hz
    exact row_mellin N d D H T (M/2) (3*M) a F1 F2 _ _ Phi alpha beta z
      hFM hW hPhi hsP hsM hN hT (by positivity) (by positivity) hz
  rw [he]
  rw [← mul_sum,integral_finsetSum]
  intro z hz
  have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  exact localized_integrable N d T (M/2) (3*M) a F1 F2 _ _ Phi alpha beta z hFM hW hPhi hsP
    hN hT (by positivity) (by positivity)
    (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)

/-- Time-first form, with Fubini proved from joint integrability. The
arithmetic field here is precisely the one bounded by negative_weil_di. -/
theorem literal_mellin_time (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hPhi : ContDiff ℝ ∞ Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M) (hs : sigma ≠ 0) :
    PRZZSignedCentral.signedLiteral (-1) N d D H T M a F1 F2 F Phi alpha beta sigma =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        PRZZAStarIntegralBound.common N d T (M/2) (3*M) (PRZZDyadicEnvelope.sourceW sigma)
          alpha beta p*mellin Phi (t*I)*twist (p.1*p.2/T) t*
            negativeSum N d D H a F1 F2 (fun y => F (M⁻¹*y)) alpha beta p.1 p.2 t := by
  let J := fun p t => ∑ z ∈ indices N d D H, localizedMinus N d T (M/2) (3*M) a F1 F2
    (fun y => F (M⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z p t
  have hi : Integrable (Function.uncurry J) := by
    apply integrable_finsetSum
    intro z hz
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact localized_integrable N d T (M/2) (3*M) a F1 F2 _ _ Phi alpha beta z
      (hF.comp (continuous_const.mul continuous_id)) (PRZZSourceWOuter.sourceW_continuous sigma hs)
      hPhi hsP hN hT (by positivity) (by positivity)
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  rw [literal_mellin N d D H T M a F1 F2 F Phi alpha beta sigma hF hPhi hsF hsP hN hT hM hs]
  have hp := integral_prod (Function.uncurry J) hi
  simp only [Function.uncurry,← MeasureTheory.Measure.volume_eq_prod] at hp
  change (1/(2*Real.pi):ℂ)*(∫ q : (ℝ × ℝ) × ℝ, J q.1 q.2) = _
  rw [hp,integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact localized_sum N d D H T (M/2) (3*M) a F1 F2 _ _ Phi alpha beta p t

#print axioms literal_mellin_time
#print axioms localized_integrable
#print axioms localized_sum
#print axioms row_mellin
#print axioms literal_mellin
#print axioms modulation_norm
#print axioms phase_prefactor
#print axioms amplitude_modulation
#print axioms physical_original
#print axioms literal_original
end XiPrime8845.PRZZNegativeMellin
