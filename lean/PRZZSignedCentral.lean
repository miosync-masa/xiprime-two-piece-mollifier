import PRZZCentralFubini

/-! Exact zero/positive/negative central Fourier families with the actual
arithmetic prefactors. The signed A* is a nested space/time integral;
its positive specialization is the existing literal A*. The zero mode is
not defined to be a cancelling Mellin correction. -/
noncomputable section
open scoped BigOperators FourierTransform
open Complex MeasureTheory Finset Set
namespace XiPrime8845.PRZZSignedCentral
open PRZZCentralFubini PRZZFilteredResidual PRZZFrozenTail
set_option maxHeartbeats 5000000

/-- Pairing the two actual gap signs in the zero Fourier kernel gives
the cosine weight. This keeps the cutoff values, complex power, sourceW
argument and time cutoff; no improper Mellin transform is assumed. -/
theorem zero_kernel_pair (F Phi : ℝ → ℂ) (M u delta T : ℝ)
    (z sigma : ℂ) (x t : ℝ) :
    kernel F Phi M u delta T 0 z sigma x t+
      kernel F Phi M u (-delta) T 0 z sigma x t =
      (2*cos ((delta*t/u/x:ℝ):ℂ))*
        (F (M⁻¹*x)*Complex.exp (-z*(Real.log x:ℂ))*
          PRZZDyadicEnvelope.sourceW sigma ((2*Real.pi*u/t)*x^2)*Phi (t/T)) := by
  have he (y : ℂ) : Complex.exp (I*y)+Complex.exp (-(I*y)) = 2*cos y := by
    rw [Complex.cos]
    ring_nf
  simp only [kernel,PRZZFullWeightSmooth.weight,mul_zero,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero,one_mul,neg_mul,neg_div,Complex.ofReal_neg,mul_neg]
  calc
    _ = (Complex.exp (I*(delta*t/u/x:ℝ))+Complex.exp (-(I*(delta*t/u/x:ℝ))))*
        (F (M⁻¹*x)*Complex.exp (-z*(Real.log x:ℂ))*
          PRZZDyadicEnvelope.sourceW sigma ((2*Real.pi*u/t)*x^2)*Phi (t/T)) := by ring
    _ = _ := by rw [he]; simp only [neg_mul]

def signedLiteral (s : ℤ) (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D H,
    (signedPrefactor a F1 F2 d beta alpha z (s*(z.2.2:ℤ))/((z.1.1:ℂ)*(z.1.2:ℂ))) *
      ∫ x in Set.Ioi (0:ℝ), ∫ t : ℝ,
        kernel F Phi (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T ((s:ℝ)*z.2.2)
          (alpha+beta+1) sigma x t

theorem signed_fourier (s : ℤ) (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    signedLiteral s N d D H T M a F1 F2 F Phi alpha beta sigma =
      ∑ z ∈ PRZZAStar.indices N d D H,
        (signedPrefactor a F1 F2 d beta alpha z (s*(z.2.2:ℤ))/((z.1.1:ℂ)*(z.1.2:ℂ))) *
          ∫ t : ℝ, Phi (t/T)*𝓕 (frozen F M z alpha beta sigma t) ((s:ℝ)*z.2.2) := by
  unfold signedLiteral
  apply Finset.sum_congr rfl
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hu : (0:ℝ) < z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn.1).1
  have hv : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn.2).1
  rw [kernel_swap F Phi hF hP (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T ((s:ℝ)*z.2.2)
    (alpha+beta+1) sigma (by positivity) (by positivity) hT hs hsF hsP]
  simp only [frozen,mul_assoc]

theorem positive_literal (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    signedLiteral 1 N d D H T M a F1 F2 F Phi alpha beta sigma =
      PRZZAStar.literal N d D H T a F1 F2 (fun y => F (M⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta := by
  rw [signed_fourier 1 N d D H T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP,
    literal_fourier N d D H T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [one_mul,Int.cast_one,signedPrefactor_nat,Complex.ofReal_mul,Complex.ofReal_natCast]

def band (s : ℤ) (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D H,
    Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))*
      PRZZCentralTail.mode F M 1 (PRZZCentralTail.residue z/z.1.2) z beta alpha sigma t (s*(z.2.2:ℤ)))

theorem band_integrable (s : ℤ) (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    Integrable (band s N d D H T M a F1 F2 F Phi alpha beta sigma) := by
  unfold band
  apply integrable_finsetSum
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hu : (0:ℝ) < z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn.1).1
  have hv : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn.2).1
  have he (t : ℝ) : Phi (t/T)*
      (PRZZUnfrozenPoisson.arithmetic a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        PRZZCentralTail.mode F M 1 (PRZZCentralTail.residue z/z.1.2) z beta alpha sigma t (s*(z.2.2:ℤ))) =
      (signedPrefactor a F1 F2 d beta alpha z (s*(z.2.2:ℤ))/((z.1.1:ℂ)*(z.1.2:ℂ)))*
        (Phi (t/T)*𝓕 (frozen F M z alpha beta sigma t) ((s:ℝ)*z.2.2)) := by
    rw [normalized_mode a F1 F2 F d beta alpha sigma z M t (s*(z.2.2:ℤ))]
    simp only [Int.cast_mul,Int.cast_natCast,frozen,add_comm beta alpha]
    ring
  simp_rw [he]
  apply Integrable.const_mul
  simpa only [frozen,mul_assoc] using spectrum_integrable F Phi hF hP
    (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T ((s:ℝ)*z.2.2) (alpha+beta+1) sigma
    (by positivity) (by positivity) hT hs hsF hsP

theorem band_literal (s : ℤ) (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ t : ℝ, band s N d D H T M a F1 F2 F Phi alpha beta sigma t) =
      signedLiteral s N d D H T M a F1 F2 F Phi alpha beta sigma := by
  rw [signed_fourier s N d D H T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP]
  unfold band
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [normalized_mode a F1 F2 F d beta alpha sigma z M t (s*(z.2.2:ℤ))]
    simp only [Int.cast_mul,Int.cast_natCast,frozen,add_comm beta alpha]
    ring
  · intro z hz
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    have hu : (0:ℝ) < z.1.1 := by exact_mod_cast (Finset.mem_Icc.mp hn.1).1
    have hv : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hn.2).1
    simp_rw [normalized_mode a F1 F2 F d beta alpha sigma z M _ (s*(z.2.2:ℤ))]
    have hi := spectrum_integrable F Phi hF hP (M/z.1.2) ((z.1.1:ℝ)*z.1.2) z.2.1 T
      ((s:ℝ)*z.2.2) (alpha+beta+1) sigma (by positivity) (by positivity) hT hs hsF hsP
    convert hi.const_mul (signedPrefactor a F1 F2 d beta alpha z (s*(z.2.2:ℤ))/
      ((z.1.1:ℂ)*(z.1.2:ℂ))) using 1
    funext t
    simp only [Int.cast_mul,Int.cast_natCast,frozen,add_comm beta alpha]
    ring

theorem frequency_reindex (N d J : ℕ) (D : ℝ) (f : PRZZAStar.Index → ℂ) :
    (∑ z ∈ PRZZAStar.indices N d D ((J:ℝ)+1), f z) =
      ∑ z ∈ PRZZAStar.indices N d D 2, ∑ j ∈ Finset.range J,
        f (z.1,(z.2.1,j+1)) := by
  classical
  have hj : (Finset.Icc 1 ⌊(J:ℝ)+1⌋₊).filter (fun h : ℕ => (h:ℝ)<(J:ℝ)+1) = Finset.Icc 1 J := by
    ext h
    rw [PRZZAStar.h_cutoff_iff,Finset.mem_Icc]
    constructor
    · intro hh
      have hlt : h < J+1 := by exact_mod_cast hh.2
      exact ⟨hh.1,by omega⟩
    · intro hh
      exact ⟨hh.1,by exact_mod_cast (show h < J+1 by omega)⟩
  have h2 : (Finset.Icc 1 ⌊(2:ℝ)⌋₊).filter (fun h : ℕ => (h:ℝ)<2) = {1} := by
    ext h
    rw [PRZZAStar.h_cutoff_iff,Finset.mem_singleton]
    constructor
    · intro hh
      have hlt : h < 2 := by exact_mod_cast hh.2
      omega
    · intro hh
      subst h
      norm_num
  unfold PRZZAStar.indices
  rw [hj,h2]
  simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro delta hd
  exact PRZZL1Truncation.positive_sum _ J

def centralRows (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D 2,
    Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))*
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z beta alpha sigma t J)

theorem central_split (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ) (t : ℝ) :
    centralRows N d J D T M a F1 F2 F Phi alpha beta sigma t =
      band 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma t+
      band 1 N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma t+
      band (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma t := by
  classical
  unfold centralRows band
  rw [frequency_reindex,frequency_reindex]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [PRZZCentralTail.central,PRZZFrozenTail.pair,Finset.mul_sum,mul_add,
    Nat.cast_zero,zero_add,inv_one,Complex.ofReal_one,one_mul,div_one,zero_mul,neg_mul,
    PRZZCentralTail.mode,PRZZCentralTail.residue,frozen,PRZZUnfrozenPoisson.arithmetic,
    Int.cast_neg,Int.cast_one,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_zero,
    Nat.cast_add,Nat.cast_one,Finset.sum_add_distrib]
  ring_nf

/-- Every central frequency is now an actual nested A* integral. Zero
and negative modes are explicit; neither is silently called positive A*. -/
theorem central_time (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ t : ℝ, centralRows N d J D T M a F1 F2 F Phi alpha beta sigma t) =
      signedLiteral 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma+
      PRZZAStar.literal N d D ((J:ℝ)+1) T a F1 F2 (fun y => F (M⁻¹*y))
        (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta+
      signedLiteral (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma := by
  simp_rw [central_split]
  have h0 := band_integrable 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  have hp := band_integrable 1 N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  have hm := band_integrable (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  rw [integral_add (h0.fun_add hp) hm,
    integral_add h0 hp,
    band_literal 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP,
    band_literal 1 N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP,
    band_literal (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP,
    positive_literal N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP]

#print axioms central_split
#print axioms central_time

/-- Sum the actual central identities over the full gcd and dyadic
configuration grids. D, J and the outer coefficients may vary by cell. -/
theorem configuration_sum (N K : ℕ) (D : ℕ → ℕ → ℝ) (J : ℕ → ℕ → ℕ)
    (w : ℕ → ℕ → ℂ) (T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
      ∫ t : ℝ, centralRows N d (J d k) (D d k) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma t) =
      (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
        signedLiteral 0 N d (D d k) 2 T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma)+
      (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
        PRZZAStar.literal N d (D d k) ((J d k:ℝ)+1) T a F1 F2
          (fun y => F (((2:ℝ)^k*M)⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta)+
      (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
        signedLiteral (-1) N d (D d k) ((J d k:ℝ)+1) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma) := by
  simp only [← Finset.sum_add_distrib,← mul_add]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact central_time N d (J d k) (D d k) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma
    hF hP hT (by positivity) hs hsF hsP

#print axioms configuration_sum

#print axioms signed_fourier
#print axioms positive_literal
#print axioms band_integrable
#print axioms band_literal
#print axioms frequency_reindex
#print axioms zero_kernel_pair
end XiPrime8845.PRZZSignedCentral
