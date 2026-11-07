import PRZZWeightedSourcePoisson
import PRZZFreezeErrorBudget

/-! The unfrozen positive monomials, their joint freezing defect, and
the exact sharp Poisson identity. Arithmetic coefficients are phase-free
before Poisson; the Fourier residue phase is introduced by the mode once.
All spatial amplitude factors remain in the defect mass. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZUnfrozenPoisson
open PRZZPowerJets PRZZDyadicEnvelope
set_option maxHeartbeats 5000000

def arithmetic (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) : ℂ :=
  a (d*z.1.1)*star (a (d*z.1.2))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)/
    ((d:ℂ)*(z.1.1:ℂ)^alpha*(z.1.2:ℂ)^beta)

def residuePhase (z : PRZZAStar.Index) : ℂ :=
  PRZZKloostermanInputs.e (-((z.2.2:ℝ)*(z.2.1:ℝ))*
    PRZZKloostermanInputs.inverseResidue z.1.2 z.1.1/z.1.2)

theorem prefactor_eq (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) :
    PRZZAStar.prefactor a F1 F2 d alpha beta z = arithmetic a F1 F2 d alpha beta z*residuePhase z := rfl

/-- The computed coefficient mass remains valid after removing the
premature Fourier phase; no arithmetic size bound is lost. -/
theorem arithmetic_mass_eq (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) :
    ‖arithmetic a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ =
      ‖PRZZAStar.prefactor a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ := by
  rw [prefactor_eq]
  simp [residuePhase,PRZZKloostermanInputs.e,Complex.norm_exp]

def boost (z : PRZZAStar.Index) (alpha beta : ℂ) : ℂ :=
  exp (((1/2:ℂ)+beta)*(Real.log (z.1.1:ℝ):ℂ)+
    ((1/2:ℂ)+alpha)*(Real.log (z.1.2:ℝ):ℂ))

def base (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ) (m : ℝ) : ℂ :=
  exp ((alpha+beta+1)*(Real.log (z.1.2:ℝ):ℂ))*F (M⁻¹*m)*
    exp (-(alpha+beta+1)*(Real.log m:ℂ))

def raw (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ) : ℂ :=
  boost z alpha beta*F (M⁻¹*m)*power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) k*
    sourceW sigma (2*Real.pi*m*k/t)*PRZZWeightedSourcePoisson.exactPhase z t m k

def errorTerm (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m : ℝ) : ℂ :=
  base F M z alpha beta m*
    PRZZAmplitudeFreeze.error ((1/2:ℂ)+beta) sigma
      (2*Real.pi*m^2*z.1.1/(t*z.1.2)) t ((z.2.1:ℝ)/(m*z.1.1))

theorem frozen_monomial (z : PRZZAStar.Index) (alpha beta : ℂ) (m : ℝ)
    (hm : 0 < m) (hu : 0 < z.1.1) (hv : 0 < z.1.2) :
    boost z alpha beta*power ((1/2:ℂ)+alpha) m*
      power ((1/2:ℂ)+beta) (m*z.1.1/z.1.2) =
    exp ((alpha+beta+1)*(Real.log (z.1.2:ℝ):ℂ))*
      exp (-(alpha+beta+1)*(Real.log m:ℂ)) := by
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  unfold boost power
  rw [Real.log_div (mul_pos hm hu0).ne' hv0.ne',Real.log_mul hm.ne' hu0.ne']
  push_cast
  simp only [← Complex.exp_add]
  congr 1
  ring

theorem power_inv_cpow (w : ℂ) (x : ℝ) (hx : 0 < x) :
    ((x:ℂ)^w)⁻¹ = power w x := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),← Complex.exp_neg]
  unfold power
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

/-- Cancel the time phases of the two original mollifier factors before
introducing any Fourier mode. The gcd contributes precisely d^-1. -/
theorem positive_weight_identity (d m k u v t : ℝ) (alpha beta : ℂ)
    (hd : 0 < d) (hm : 0 < m) (hk : 0 < k) (hu : 0 < u) (hv : 0 < v) :
    power ((1/2:ℂ)+alpha+(t:ℂ)*I) m*power ((1/2:ℂ)+beta-(t:ℂ)*I) k*
      power ((1/2:ℂ)+(t:ℂ)*I) (d*u)*power ((1/2:ℂ)-(t:ℂ)*I) (d*v) =
    power 1 d*power (1/2:ℂ) u*power (1/2:ℂ) v*
      power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) k*
      exp (I*((t*Real.log (k*v/(m*u)):ℝ):ℂ)) := by
  unfold power
  rw [Real.log_mul hd.ne' hu.ne',Real.log_mul hd.ne' hv.ne',
    Real.log_div (mul_pos hk hv).ne' (mul_pos hm hu).ne',
    Real.log_mul hk.ne' hv.ne',Real.log_mul hm.ne' hu.ne']
  push_cast
  simp only [← Complex.exp_add]
  congr 1
  ring

theorem star_power (w : ℂ) (x : ℝ) : star (power w x) = power (star w) x := by
  simp [power,← Complex.exp_conj]

/-- Match the normalization to both original square-root mollifier
denominators. Freezing k=m*u/v swaps the two A* shift slots. -/
theorem arithmetic_boost (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (hu : 0 < z.1.1) (hv : 0 < z.1.2) :
    arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*boost z alpha beta =
      (a (d*z.1.1)*star (a (d*z.1.2))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)/(d:ℂ))*
        power (1/2:ℂ) z.1.1*power (1/2:ℂ) z.1.2 := by
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hpu : ((z.1.1:ℂ)^beta)⁻¹ = power beta (z.1.1:ℝ) := by
    simpa only [Complex.ofReal_natCast] using power_inv_cpow beta (z.1.1:ℝ) hu0
  have hpv : ((z.1.2:ℂ)^alpha)⁻¹ = power alpha (z.1.2:ℝ) := by
    simpa only [Complex.ofReal_natCast] using power_inv_cpow alpha (z.1.2:ℝ) hv0
  have heu : exp ((Real.log (z.1.1:ℝ):ℂ)) = (z.1.1:ℂ) := by
    rw [← Complex.ofReal_exp,Real.exp_log hu0]; rfl
  have hev : exp ((Real.log (z.1.2:ℝ):ℂ)) = (z.1.2:ℂ) := by
    rw [← Complex.ofReal_exp,Real.exp_log hv0]; rfl
  have hb : (power beta (z.1.1:ℝ)*power alpha (z.1.2:ℝ)*boost z alpha beta)/
      ((z.1.1:ℂ)*(z.1.2:ℂ)) = power (1/2:ℂ) z.1.1*power (1/2:ℂ) z.1.2 := by
    rw [← heu,← hev]
    unfold power boost
    simp only [div_eq_mul_inv,← Complex.exp_neg,← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (a (d*z.1.1)*star (a (d*z.1.2))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)/(d:ℂ))*
        ((power beta (z.1.1:ℝ)*power alpha (z.1.2:ℝ)*boost z alpha beta)/
          ((z.1.1:ℂ)*(z.1.2:ℂ))) := by
      unfold arithmetic
      simp only [div_eq_mul_inv,mul_inv_rev,hpu,hpv]
      ring
    _ = _ := by rw [hb]; ring

/-- Direct identification with the literal four-index W-form AFE term.
The cutoff values are not replaced by support masks or by unit weights. -/
theorem afe_term_eq (a : ℕ → ℂ) (F F1 F2 : ℝ → ℂ) (d m k : ℕ)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hd : 0 < d) (hm : 0 < m) (hk : 0 < k) (hu : 0 < z.1.1) (hv : 0 < z.1.2) :
    F (M⁻¹*(m:ℝ))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)*
      PRZZL1Finite.term a a alpha beta
        (fun n t => sourceW sigma (2*Real.pi*(n:ℝ)/t)) t m k (d*z.1.1) (d*z.1.2) =
    arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
      raw F M z alpha beta sigma t m k := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have invpow (n : ℕ) (hn : 0 < n) (w : ℂ) : ((n:ℂ)^w)⁻¹ = power w (n:ℝ) := by
    simpa only [Complex.ofReal_natCast] using power_inv_cpow w (n:ℝ) (by exact_mod_cast hn)
  have he := positive_weight_identity (d:ℝ) m k z.1.1 z.1.2 t alpha beta hd0 hm0 hk0 hu0 hv0
  have hpd : power 1 (d:ℝ) = (d:ℂ)⁻¹ := by
    rw [← power_inv_cpow 1 (d:ℝ) hd0,Complex.cpow_one]
    rfl
  let c := a (d*z.1.1)*star (a (d*z.1.2))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)
  calc
    _ = c*F (M⁻¹*(m:ℝ))*sourceW sigma (2*Real.pi*(m:ℝ)*k/t)*
        (power ((1/2:ℂ)+alpha+(t:ℂ)*I) m*power ((1/2:ℂ)+beta-(t:ℂ)*I) k*
          power ((1/2:ℂ)+(t:ℂ)*I) ((d:ℝ)*z.1.1)*
          power ((1/2:ℂ)-(t:ℂ)*I) ((d:ℝ)*z.1.2)) := by
      unfold PRZZL1Finite.term PRZZL1Finite.directTerm
      simp only [div_eq_mul_inv,mul_inv_rev]
      rw [invpow m hm,invpow k hk,invpow (d*z.1.1) (Nat.mul_pos hd hu),
        invpow (d*z.1.2) (Nat.mul_pos hd hv)]
      simp only [star_mul,star_power,Nat.cast_mul]
      dsimp [c]
      simp [sub_eq_add_neg,map_ofNat,add_comm,add_left_comm,add_assoc] <;> ring
    _ = arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        raw F M z alpha beta sigma t m k := by
      rw [he,hpd]
      unfold raw
      have hh := arithmetic_boost a F1 F2 d alpha beta z hu hv
      rw [show arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
          (boost z alpha beta*F (M⁻¹*(m:ℝ))*power ((1/2:ℂ)+alpha) m*
            power ((1/2:ℂ)+beta) k*sourceW sigma (2*Real.pi*(m:ℝ)*k/t)*
            PRZZWeightedSourcePoisson.exactPhase z t m k) =
          (arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*boost z alpha beta)*
            F (M⁻¹*(m:ℝ))*power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) k*
            sourceW sigma (2*Real.pi*(m:ℝ)*k/t)*PRZZWeightedSourcePoisson.exactPhase z t m k by ring,hh]
      unfold PRZZWeightedSourcePoisson.exactPhase
      dsimp [c]
      ring

/-- The spatial amplitude that must be paid by the remainder estimate.
In particular it is not silently replaced by 1. -/
theorem base_norm (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ) (m : ℝ) :
    ‖base F M z alpha beta m‖ = ‖F (M⁻¹*m)‖*
      Real.exp ((alpha.re+beta.re+1)*(Real.log (z.1.2:ℝ)-Real.log m)) := by
  unfold base
  simp only [norm_mul,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,
    neg_re,add_re,one_re]
  rw [mul_right_comm,← Real.exp_add,mul_comm]
  congr 2
  ring

/-- A literal monomial equality: W, complex powers and logarithmic phase
are replaced together, with their full spatial amplitude multiplying the
defect. Nothing has yet been bounded or discarded. -/
theorem raw_split (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t m k : ℝ)
    (hm : 0 < m) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (ht : 0 < t)
    (hg : m*z.1.1-k*z.1.2 = -(z.2.1:ℝ))
    (hsmall : |(z.2.1:ℝ)/(m*z.1.1)| ≤ 1/2) :
    raw F M z alpha beta sigma t m k =
      PRZZSourceLattice.source F M z alpha beta sigma t m+errorTerm F M z alpha beta sigma t m := by
  have he := PRZZAmplitudeFreeze.monomial_identity ((1/2:ℂ)+alpha) ((1/2:ℂ)+beta)
    sigma m k z.1.1 z.1.2 z.2.1 t hm (by exact_mod_cast hu) (by exact_mod_cast hv) ht hg hsmall
  have hf := frozen_monomial z alpha beta m hm hu hv
  have hf' : boost z alpha beta*F (M⁻¹*m)*
      (power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) (m*z.1.1/z.1.2)) =
      base F M z alpha beta m := by
    unfold base
    calc
      _ = (boost z alpha beta*power ((1/2:ℂ)+alpha) m*
          power ((1/2:ℂ)+beta) (m*z.1.1/z.1.2))*F (M⁻¹*m) := by ring
      _ = _ := by rw [hf]; ring
  have hsource := PRZZWeightedSourcePoisson.source_factor F M z alpha beta sigma t m hv hm
  have hsource' : PRZZSourceLattice.source F M z alpha beta sigma t m =
      base F M z alpha beta m*sourceW sigma (2*Real.pi*m^2*z.1.1/(t*z.1.2))*
        exp (I*((t*((z.2.1:ℝ)/(m*z.1.1)):ℝ):ℂ)) := by
    rw [hsource]
    unfold PRZZWeightedSourcePoisson.amplitude PRZZWeightedSourcePoisson.linearPhase base
    rw [show 2*Real.pi*(z.1.1:ℝ)/(t*z.1.2)*m^2 = 2*Real.pi*m^2*z.1.1/(t*z.1.2) by ring,
      show (z.2.1:ℝ)*t/((z.1.1:ℝ)*m) = t*((z.2.1:ℝ)/(m*z.1.1)) by ring]
  have hh' : raw F M z alpha beta sigma t m k-
      PRZZSourceLattice.source F M z alpha beta sigma t m = errorTerm F M z alpha beta sigma t m := by
    calc
      _ = boost z alpha beta*F (M⁻¹*m)*
          (power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) k*sourceW sigma (2*Real.pi*m*k/t)*
              exp (I*((t*Real.log (k*z.1.2/(m*z.1.1)):ℝ):ℂ))-
            power ((1/2:ℂ)+alpha) m*power ((1/2:ℂ)+beta) (m*z.1.1/z.1.2)*
              sourceW sigma (2*Real.pi*m^2*z.1.1/(t*z.1.2))*
              exp (I*((t*((z.2.1:ℝ)/(m*z.1.1)):ℝ):ℂ))) := by
        rw [hsource',← hf']
        unfold raw PRZZWeightedSourcePoisson.exactPhase
        ring
      _ = _ := by
        rw [he]
        unfold errorTerm
        rw [← hf']
        ring
  exact sub_eq_iff_eq_add.mp hh' |>.trans (add_comm _ _)

def rawSum (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then raw F M z alpha beta sigma t m k else 0

def errorSum (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then errorTerm F M z alpha beta sigma t m else 0

def afeRow (L : ℕ) (F F1 F2 : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then
      F (M⁻¹*(m:ℝ))*F1 ((d:ℝ)*z.1.1)*F2 ((d:ℝ)*z.1.2)*
        PRZZL1Finite.term a a alpha beta
          (fun n t => sourceW sigma (2*Real.pi*(n:ℝ)/t)) t m.toNat k.toNat (d*z.1.1) (d*z.1.2)
    else 0

/-- Sum the literal AFE summands on the full sharp congruence row.
No phase, denominator or cutoff-value equality is an input. -/
theorem afe_row_eq (L : ℕ) (F F1 F2 : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ)
    (hd : 0 < d) (hu : 0 < z.1.1) (hv : 0 < z.1.2) :
    afeRow L F F1 F2 M z alpha beta sigma a d t =
      arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*rawSum L F M z alpha beta sigma t := by
  unfold afeRow rawSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hg
  · have hm0 : (0:ℤ) < m := by have := (Finset.mem_Icc.mp hm).1; omega
    have hk0 : (0:ℤ) < k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hmc : (m.toNat:ℝ) = (m:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0.le
    have hkc : (k.toNat:ℝ) = (k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
    simpa only [hmc,hkc] using afe_term_eq a F F1 F2 d m.toNat k.toNat M t z alpha beta sigma
      hd (by omega) (by omega) hu hv
  · simp

/-- The source support supplies the small ratio on every nonzero term. -/
theorem sum_split (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) (hM : 0 < M) (ht : 0 < t)
    (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4) :
    rawSum L F M z alpha beta sigma t =
      (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
        if m*z.1.1-k*z.1.2= -z.2.1 then PRZZSourceLattice.source F M z alpha beta sigma t m else 0)+
      errorSum L F M z alpha beta sigma t := by
  unfold rawSum errorSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hg
  · have hm0 : (0:ℝ) < m := by have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show (0:ℤ) < m by omega)
    by_cases hf : F (M⁻¹*(m:ℝ)) = 0
    · rw [PRZZWeightedSourcePoisson.source_factor F M z alpha beta sigma t m hv hm0]
      simp [raw,errorTerm,base,PRZZWeightedSourcePoisson.amplitude,hf]
    · have hlo := (hsF hf).1
      have hlow : M/2 ≤ (m:ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hlo hM.le
        field_simp at hh
        linarith
      have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
      have hsmall : |(z.2.1:ℝ)/((m:ℝ)*z.1.1)| ≤ 1/2 := by
        rw [abs_div,abs_of_pos (mul_pos hm0 hu0)]
        apply (div_le_iff₀ (mul_pos hm0 hu0)).mpr
        nlinarith
      exact raw_split F M z alpha beta sigma t m k hm0 hu hv ht (by exact_mod_cast hg) hsmall
  · simp

/-- Exact Poisson decomposition of the UNFROZEN W row, including the
sharp boundary and the joint amplitude/phase replacement error. -/
theorem poisson_eq (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2) :
    rawSum L F M z alpha beta sigma t =
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
      (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t)-
      PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t+
      errorSum L F M z alpha beta sigma t := by
  rw [sum_split L F M z alpha beta sigma t hM ht hu hv hsF hdelta]
  have he := PRZZSourceLattice.source_boundary L B J hLB F hF hsF M t z alpha beta sigma
    hM ht hu hv hc hs hdelta hB hkB
  change _+PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t = _ at he
  rw [← he]
  ring

/-- Weighted time identity with the phase-free original arithmetic
coefficient. No exchange or splitting of improper integrals is assumed. -/
theorem weighted_time_eq (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M T : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2)
    (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ) (d : ℕ) :
    (∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/
        ((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*rawSum L F M z alpha beta sigma t) =
      ∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/
        ((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
          (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
            (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t)-
            PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t+
            errorSum L F M z alpha beta sigma t) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [poisson_eq L B J hLB F hF hsF M t z alpha beta sigma hM (hT.trans_le ht.1)
    hu hv hc hs hdelta hB hkB]

/-- The weighted original W-form AFE congruence row, with every correction
retained, now has the exact same Poisson decomposition under time integration. -/
theorem afe_time_eq (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M T : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2)
    (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ) (d : ℕ) (hd : 0 < d) :
    (∫ t in Icc T (2*T), phi t*afeRow L F F1 F2 M z alpha beta sigma a d t) =
      ∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/
        ((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
          (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
            (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t)-
            PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t+
            errorSum L F M z alpha beta sigma t) := by
  have he : (∫ t in Icc T (2*T), phi t*afeRow L F F1 F2 M z alpha beta sigma a d t) =
      ∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/
        ((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*rawSum L F M z alpha beta sigma t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [afe_row_eq L F F1 F2 M z alpha beta sigma a d t hd hu hv]
    ring
  rw [he]
  exact weighted_time_eq L B J hLB F hF hsF M T z alpha beta sigma hM hT hu hv hc hs hdelta hB hkB a F1 F2 phi d

def retained (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)).filter
    (fun p => p.1*z.1.1-p.2*z.1.2= -z.2.1 ∧ F (M⁻¹*(p.1:ℝ)) ≠ 0)

def numerator (z : PRZZAStar.Index) (m : ℝ) : ℝ := 2*Real.pi*m^2*z.1.1/z.1.2

def analyticMass (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ retained L F M z, ‖base F M z alpha beta p.1‖/(numerator z p.1)^2

theorem error_sum_prune (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) :
    errorSum L F M z alpha beta sigma t =
      ∑ p ∈ retained L F M z, base F M z alpha beta p.1*
        PRZZAmplitudeFreeze.error ((1/2:ℂ)+beta) sigma (numerator z p.1/t) t
          ((z.2.1:ℝ)/((p.1:ℝ)*z.1.1)) := by
  classical
  unfold retained
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hg : m*z.1.1-k*z.1.2= -z.2.1
  · by_cases hf : F (M⁻¹*(m:ℝ)) = 0
    · simp [errorTerm,base,hg,hf]
    · simp only [hg,ite_true,true_and,if_pos hf]
      unfold errorTerm numerator
      rw [show 2*Real.pi*(m:ℝ)^2*z.1.1/(t*z.1.2) = (2*Real.pi*(m:ℝ)^2*z.1.1/z.1.2)/t by ring]
  · simp [hg]

/-- Quantitative domination of the actual joint freezing remainder,
with all m,k support masks and the full analytic amplitude supplied.
No premise is an assumed bound on the error or on its coefficient mass. -/
theorem error_time_bound (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (L : ℕ) (F phi : ℝ → ℂ)
      (M T : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi → 0 < M → 0 < T →
      0 < z.1.1 → 0 < z.1.2 → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      |(z.2.1:ℝ)| ≤ M*z.1.1/4 →
      ‖∫ t in Icc T (2*T), phi t*errorSum L F M z alpha beta sigma t‖ ≤
        (C+D/‖sigma‖^2)*
          (2*|(z.2.1:ℝ)|/(M*z.1.1)+2*T*(2*|(z.2.1:ℝ)|/(M*z.1.1))^2)*(2*T)^2*
          analyticMass L F M z alpha beta*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,D,hC,hD,hh⟩ := PRZZAmplitudeFreeze.time_bound (ι := ℤ × ℤ) Z
  refine ⟨C,D,hC,hD,?_⟩
  intro L F phi M T z alpha beta sigma hz hs hphi hM hT hu hv hsF hdelta
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  let kap := 2*|(z.2.1:ℝ)|/(M*z.1.1)
  have hkap : 0 ≤ kap := by dsimp [kap]; positivity
  have hkhalf : kap ≤ 1/2 := by
    dsimp [kap]
    apply (div_le_iff₀ (mul_pos hM hu0)).mpr
    nlinarith
  have hgeo (p : ℤ × ℤ) (hp : p ∈ retained L F M z) :
      0 < numerator z p.1 ∧ |(z.2.1:ℝ)/((p.1:ℝ)*z.1.1)| ≤ kap := by
    have hp' := Finset.mem_filter.mp hp
    have hm : (0:ℝ) < p.1 := by
      have hh := (Finset.mem_Icc.mp (Finset.mem_product.mp hp'.1).1).1
      exact_mod_cast (show (0:ℤ) < p.1 by omega)
    have hlo : M/2 ≤ (p.1:ℝ) := by
      have hb := mul_le_mul_of_nonneg_left (hsF hp'.2.2).1 hM.le
      field_simp at hb
      linarith
    refine ⟨by unfold numerator; positivity,?_⟩
    rw [abs_div,abs_of_pos (mul_pos hm hu0)]
    calc
      _ ≤ |(z.2.1:ℝ)|/((M/2)*z.1.1) := by gcongr
      _ = kap := by dsimp [kap]; ring
  have hb := hh ((1/2:ℂ)+beta) sigma hz hs (retained L F M z)
    (fun p => base F M z alpha beta p.1) (fun p => numerator z p.1)
    (fun p => (z.2.1:ℝ)/((p.1:ℝ)*z.1.1)) T kap phi hT hkap hphi
    (fun p hp => (hgeo p hp).1)
    (fun p hp => ((hgeo p hp).2).trans hkhalf) (fun p hp => (hgeo p hp).2)
  simpa only [analyticMass,← error_sum_prune,kap] using hb

/-- The actual coefficient-weighted Poisson joint remainder, not a
separately named proxy with an assumed bound. Tail and sharp-boundary
terms are subtracted explicitly, rather than being set to zero. -/
theorem joint_remainder_time_bound (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (L B J : ℕ), L ≤ B →
      ∀ (F : ℝ → ℂ), ContDiff ℝ ∞ F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ∀ (M T : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → 0 < M → 0 < T →
      0 < z.1.1 → 0 < z.1.2 → z.1.1.Coprime z.1.2 →
      |(z.2.1:ℝ)| ≤ M*z.1.1/4 → 3*M ≤ B →
      3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2 →
      ∀ (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ) (d : ℕ), Continuous phi →
      ‖∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
        (rawSum L F M z alpha beta sigma t-
          (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
            (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t)-
            PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t))‖ ≤
        ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
          (C+D/‖sigma‖^2)*
          (2*|(z.2.1:ℝ)|/(M*z.1.1)+2*T*(2*|(z.2.1:ℝ)|/(M*z.1.1))^2)*(2*T)^2*
          analyticMass L F M z alpha beta*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,D,hC,hD,hh⟩ := error_time_bound Z
  refine ⟨C,D,hC,hD,?_⟩
  intro L B J hLB F hF hsF M T z alpha beta sigma hz hs hM hT hu hv hc hdelta hB hkB a F1 F2 phi d hphi
  let c := arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))
  have hb := hh L F (fun t => c*phi t) M T z alpha beta sigma hz hs
    (continuous_const.mul hphi) hM hT hu hv hsF hdelta
  have he : (∫ t in Icc T (2*T), ‖c*phi t‖) =
      ‖c‖*(∫ t in Icc T (2*T), ‖phi t‖) := by
    simp only [norm_mul]
    rw [integral_const_mul]
  rw [he] at hb
  have hm : ‖c‖ = ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ :=
    arithmetic_mass_eq a F1 F2 d beta alpha z
  rw [hm] at hb
  have hi : (∫ t in Icc T (2*T), c*phi t*
      (rawSum L F M z alpha beta sigma t-
        (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
          (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J j t)-
          PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t))) =
      ∫ t in Icc T (2*T), c*phi t*errorSum L F M z alpha beta sigma t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [poisson_eq L B J hLB F hF hsF M t z alpha beta sigma hM (hT.trans_le ht.1)
      hu hv hc hs hdelta hB hkB]
    ring
  change ‖∫ t in Icc T (2*T), c*phi t*(_-_)‖ ≤ _
  rw [hi]
  exact hb.trans_eq (by ring)

#print axioms prefactor_eq
#print axioms arithmetic_mass_eq
#print axioms frozen_monomial
#print axioms power_inv_cpow
#print axioms positive_weight_identity
#print axioms star_power
#print axioms arithmetic_boost
#print axioms afe_term_eq
#print axioms afe_row_eq
#print axioms base_norm
#print axioms raw_split
#print axioms sum_split
#print axioms poisson_eq
#print axioms weighted_time_eq
#print axioms afe_time_eq
#print axioms error_sum_prune
#print axioms error_time_bound
#print axioms joint_remainder_time_bound
end XiPrime8845.PRZZUnfrozenPoisson
