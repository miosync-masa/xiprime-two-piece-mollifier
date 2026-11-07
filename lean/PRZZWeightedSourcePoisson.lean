import PRZZSourceLattice

/-! Exact logarithmic phase versus the reciprocal-phase source weight.
The W argument and complex power here are already frozen. Their own
replacement errors are not part of the phase defect defined below.
The original prefactor (including both cutoff values) is preserved. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex MeasureTheory
namespace XiPrime8845.PRZZWeightedSourcePoisson
set_option maxHeartbeats 3000000

def amplitude (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m : ℝ) : ℂ :=
  exp ((alpha+beta+1)*(Real.log (z.1.2:ℝ):ℂ))*
    F (M⁻¹*m)*exp (-(alpha+beta+1)*(Real.log m:ℂ))*
    PRZZDyadicEnvelope.sourceW sigma ((2*Real.pi*z.1.1/(t*z.1.2))*m^2)

def linearPhase (z : PRZZAStar.Index) (t m : ℝ) : ℂ :=
  exp (I*(((z.2.1:ℝ)*t/((z.1.1:ℝ)*m):ℝ):ℂ))

def exactPhase (z : PRZZAStar.Index) (t m k : ℝ) : ℂ :=
  exp (I*((t*Real.log (k*z.1.2/(m*z.1.1)):ℝ):ℂ))

def phaseDefect (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ) : ℂ :=
  amplitude F M z alpha beta sigma t m*(exactPhase z t m k-linearPhase z t m)

theorem source_factor (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m : ℝ) (hv : 0 < z.1.2) (hm : 0 < m) :
    PRZZSourceLattice.source F M z alpha beta sigma t m =
      amplitude F M z alpha beta sigma t m*linearPhase z t m := by
  rw [PRZZSourceLattice.source,PRZZFrozenTail.frozen_dilation F M z alpha beta sigma t m hv hm]
  unfold PRZZFullWeightSmooth.weight amplitude linearPhase
  rw [show (z.2.1:ℝ)*t/z.1.1/m = (z.2.1:ℝ)*t/((z.1.1:ℝ)*m) by ring]
  ring

theorem phase_split (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ) (hv : 0 < z.1.2) (hm : 0 < m) :
    amplitude F M z alpha beta sigma t m*exactPhase z t m k =
      PRZZSourceLattice.source F M z alpha beta sigma t m+
        phaseDefect F M z alpha beta sigma t m k := by
  rw [source_factor F M z alpha beta sigma t m hv hm]
  unfold phaseDefect
  ring

theorem phase_bound (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ)
    (hmu : m*(z.1.1:ℝ) ≠ 0)
    (hgap : m*z.1.1-k*z.1.2 = -(z.2.1:ℝ))
    (hsmall : |(-(z.2.1:ℝ))/(m*z.1.1)| ≤ 1/2) :
    ‖phaseDefect F M z alpha beta sigma t m k‖ ≤
      ‖amplitude F M z alpha beta sigma t m‖*
        (2*|t| *(z.2.1:ℝ)^2/(m*z.1.1)^2) := by
  have hh := PRZZCongruencePoisson.signed_phase_error m k z.1.1 z.1.2
    (-(z.2.1:ℝ)) t hmu hgap hsmall
  simp only [neg_neg,neg_sq] at hh
  have he : t*(z.2.1:ℝ)/(m*z.1.1) = (z.2.1:ℝ)*t/((z.1.1:ℝ)*m) := by ring
  rw [he] at hh
  unfold phaseDefect
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)

def sharp (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then
      amplitude F M z alpha beta sigma t m*exactPhase z t m k else 0

def phaseSum (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then phaseDefect F M z alpha beta sigma t m k else 0

def boundary (L B : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) \
    ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)),
    if p.1*z.1.1-p.2*z.1.2= -z.2.1 then
      PRZZSourceLattice.source F M z alpha beta sigma t p.1 else 0

/-- Zero cutoff values are handled before imposing the small-ratio
condition. The remaining amplitude includes the actual sourceW and
complex-power dilation factor, not just a coefficient placeholder. -/
theorem active_phase_bound (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hu : 0 < z.1.1)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hgap : m*z.1.1-k*z.1.2 = -(z.2.1:ℝ)) :
    ‖phaseDefect F M z alpha beta sigma t m k‖ ≤
      ‖amplitude F M z alpha beta sigma t m‖*
        (8*|t| *(z.2.1:ℝ)^2/(M*z.1.1)^2) := by
  by_cases hz : amplitude F M z alpha beta sigma t m = 0
  · simp [phaseDefect,hz]
  have hf : F (M⁻¹*m) ≠ 0 := by
    intro hh; apply hz; simp [amplitude,hh]
  have hlow : M/2 ≤ m := by
    have h1 : (1/2:ℝ) ≤ m/M := by simpa [div_eq_mul_inv,mul_comm] using (hsF hf).1
    have h2 := (le_div_iff₀ hM).mp h1
    linarith
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hm : 0 < m := (by positivity : 0 < M/2).trans_le hlow
  have hsmall : |(-(z.2.1:ℝ))/(m*z.1.1)| ≤ 1/2 := by
    rw [abs_div,abs_neg,abs_of_pos (mul_pos hm hu0)]
    apply (div_le_iff₀ (mul_pos hm hu0)).mpr
    nlinarith
  have hb := phase_bound F M z alpha beta sigma t m k (mul_pos hm hu0).ne' hgap hsmall
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ 2*|t| *(z.2.1:ℝ)^2/((M/2)*z.1.1)^2 := by gcongr
    _ = _ := by ring

/-- Finite retained phase error with its full analytic mass displayed. -/
theorem phase_sum_bound (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hu : 0 < z.1.1)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4) :
    ‖phaseSum L F M z alpha beta sigma t‖ ≤
      (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
        if m*z.1.1-k*z.1.2= -z.2.1 then
          ‖amplitude F M z alpha beta sigma t m‖ else 0)*
        (8*|t| *(z.2.1:ℝ)^2/(M*z.1.1)^2) := by
  unfold phaseSum
  apply (norm_sum_le _ _).trans
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  split_ifs with hg
  · exact active_phase_bound F M z alpha beta sigma t m k hsF hM hu hdelta
      (by exact_mod_cast hg)
  · simp

/-- The phase correction and both sharp boundary corrections survive
the passage to the central Fourier block. The transformed modulus is 1. -/
theorem sharp_eq (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2) :
    sharp L F M z alpha beta sigma t =
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J +
      (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t) -
      boundary L B F M z alpha beta sigma t+phaseSum L F M z alpha beta sigma t := by
  have he := PRZZSourceLattice.source_boundary L B J hLB F hF hsF M t z alpha beta sigma
    hM ht hu hv hc hs hdelta hB hkB
  have hp : sharp L F M z alpha beta sigma t =
      (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
        if m*z.1.1-k*z.1.2= -z.2.1 then PRZZSourceLattice.source F M z alpha beta sigma t m else 0)+
      phaseSum L F M z alpha beta sigma t := by
    unfold sharp phaseSum
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · exact phase_split F M z alpha beta sigma t m k hv
        (by have h := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show (0:ℤ) < m by omega))
    · simp
  change _+boundary L B F M z alpha beta sigma t = _ at he
  rw [hp,← he]
  ring

/-- Retain the literal arithmetic prefactor, hence the cutoff values,
inside the weighted time integral. No extra integrability premise or
exchange of an infinite Fourier sum is used by this equality. -/
theorem weighted_time_eq (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M T : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2)
    (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ) (d : ℕ) :
    (∫ t in Icc T (2*T), PRZZAStar.prefactor a F1 F2 d alpha beta z * Phi (t/T)*
      sharp L F M z alpha beta sigma t) =
    ∫ t in Icc T (2*T), PRZZAStar.prefactor a F1 F2 d alpha beta z * Phi (t/T)*
      (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J +
      (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t) -
      boundary L B F M z alpha beta sigma t+phaseSum L F M z alpha beta sigma t) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [sharp_eq L B J hLB F hF hsF M t z alpha beta sigma hM (hT.trans_le ht.1)
    hu hv hc hs hdelta hB hkB]

#print axioms source_factor
#print axioms active_phase_bound
#print axioms phase_sum_bound
#print axioms phase_split
#print axioms phase_bound
#print axioms sharp_eq
#print axioms weighted_time_eq
end XiPrime8845.PRZZWeightedSourcePoisson
