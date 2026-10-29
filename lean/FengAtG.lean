import FengShift

/-! Exact Feng decomposition at g*n. The divisor correction sharing a prime
with g remains explicit; it is not absorbed into an unproved error term. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.FengAtG
open PRZZ CoprimeShift ShiftWeights
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def mark (r : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt r * Real.log r : ℝ)

def shared (g n : ℕ) : ℂ :=
  ∑ r ∈ (g*n).divisors.filter (fun r => ¬ r.Coprime g), mark r * (μ ((g*n)/r) : ℂ)

def outside (g n : ℕ) : ℂ :=
  ∑ r ∈ n.divisors.filter (fun r => r.Coprime g),
    mark r * (if (n/r).Coprime g then (μ (n/r) : ℂ) else 0)

theorem coprime_divisors (g n : ℕ) (hg : g ≠ 0) :
    (g*n).divisors.filter (fun r => r.Coprime g) =
      n.divisors.filter (fun r => r.Coprime g) := by
  ext r
  simp only [Finset.mem_filter,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd,hn⟩,hc⟩
    exact ⟨⟨hc.dvd_mul_left.mp hd,(mul_ne_zero_iff.mp hn).2⟩,hc⟩
  · rintro ⟨⟨hd,hn⟩,hc⟩
    exact ⟨⟨hc.dvd_mul_left.mpr hd,mul_ne_zero hg hn⟩,hc⟩

/-- The sharing condition is on r, not on g*n; repeated powers are retained. -/
theorem feng_at_mul (g n : ℕ) (hg : g ≠ 0) :
    (fengArithmetic (g*n) : ℂ) = (μ (g*n) : ℂ) * (Real.log (g*n) : ℂ)^2 +
      (μ g : ℂ) * outside g n + shared g n := by
  have h := congrArg (fun x : ℝ => (x:ℂ)) (FengArithmetic.feng_divisor_formula (g*n))
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_sum,muReal,ArithmeticFunction.coe_mk,Complex.ofReal_intCast,Nat.cast_mul] at h
  rw [h]
  have hs := Finset.sum_filter_add_sum_filter_not (g*n).divisors (fun r => r.Coprime g)
    (fun r => mark r * (μ ((g*n)/r):ℂ))
  simp only [mark,Complex.ofReal_mul] at hs
  rw [← hs,coprime_divisors g n hg]
  have ho : (∑ r ∈ n.divisors.filter (fun r => r.Coprime g),
      mark r * (μ ((g*n)/r):ℂ)) = (μ g:ℂ)*outside g n := by
    unfold outside
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.mul_div_assoc g (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1),
      SmoothMobius.moebius_mul_indicator]
    ring
  simp only [mark,Complex.ofReal_mul] at ho
  rw [ho]
  simp only [shared,mark,Complex.ofReal_mul]
  ring

theorem mark_zero_of_not_prime_pow (r : ℕ) (hr : ¬ IsPrimePow r) : mark r = 0 := by
  simp [mark,ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hr]

/-- Shared prime-power terms do not vanish even in the smallest repeated-prime test. -/
theorem shared_prime_square (p : ℕ) (hp : p.Prime) :
    shared p p = (Real.log p : ℂ)^2 := by
  have ho : outside p p = 0 := by
    unfold outside
    apply Finset.sum_eq_zero
    intro r hr
    have hr' := (Finset.mem_filter.mp hr)
    have hd := (Nat.dvd_prime hp).mp (Nat.dvd_of_mem_divisors hr'.1)
    rcases hd with rfl | rfl
    · simp [mark]
    · exact False.elim ((hp.coprime_iff_not_dvd.mp hr'.2) (dvd_refl _))
  have h := feng_at_mul p p hp.ne_zero
  have hm : μ (p*p) = 0 := by
    simpa [pow_two] using ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num : (2:ℕ) ≠ 0)
  rw [ho,hm] at h
  have hf := congrArg (fun x : ℝ => (x:ℂ)) (FengArithmetic.feng_prime_square p hp)
  simp only [pow_two] at hf
  simpa only [Int.cast_zero,zero_mul,mul_zero,zero_add,Complex.ofReal_mul,pow_two] using (h.symm.trans hf)

def coprimeScaled (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L:ℂ)*coprimeInner N g L u θ P A

theorem coprimeScaled_entire (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℂ ⊤ (coprimeScaled N g L u θ P) := by
  unfold coprimeScaled coprimeInner weight
  fun_prop

theorem coprimeScaled_derivative (k N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    iteratedDeriv k (coprimeScaled N g L u θ P) A =
      (L:ℂ)*∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime g),
        (μ n:ℂ)/n * (-(Real.log n/L : ℝ):ℂ)^k * weight A u θ P (Real.log n/L) := by
  unfold coprimeScaled coprimeInner
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_sum (by intros; unfold weight; fun_prop)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_const_mul_field,FengShift.weight_iteratedDeriv]
  ring

/-- The log-square part, scaled by L and divided by L^2, before theta^-2. -/
def logBlock (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L:ℂ)*∑ n ∈ Finset.Icc 1 N, (μ (g*n):ℂ)/n *
    ((Real.log (g*n)/L : ℝ):ℂ)^2 * weight A u θ P (Real.log n/L)

theorem logBlock_derivatives (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ)
    (hg : g ≠ 0) :
    logBlock N g L u θ P A = (μ g:ℂ) *
      (((Real.log g/L : ℝ):ℂ)^2 * coprimeScaled N g L u θ P A -
        2*((Real.log g/L : ℝ):ℂ)*iteratedDeriv 1 (coprimeScaled N g L u θ P) A +
        iteratedDeriv 2 (coprimeScaled N g L u θ P) A) := by
  rw [coprimeScaled_derivative,coprimeScaled_derivative]
  simp only [logBlock,coprimeScaled,coprimeInner,Finset.sum_filter,
    mul_add,mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by
    have := (Finset.mem_Icc.mp hn).1; omega)
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast hg
  rw [SmoothMobius.moebius_mul_indicator]
  by_cases hc : n.Coprime g
  · simp only [if_pos hc,Real.log_mul hg0 hn0,add_div,Complex.ofReal_add,pow_one]
    ring
  · simp [hc]

/-- The complete Feng block at g*n, before the common theta^-2 normalization. -/
def fengBlock (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L:ℂ)*∑ n ∈ Finset.Icc 1 N, (fengArithmetic (g*n):ℂ)/n/(L:ℂ)^2 *
    weight A u θ P (Real.log n/L)

def outsideBlock (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L:ℂ)*∑ n ∈ Finset.Icc 1 N, (μ g:ℂ)*outside g n/n/(L:ℂ)^2 *
    weight A u θ P (Real.log n/L)

def sharedBlock (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L:ℂ)*∑ n ∈ Finset.Icc 1 N, shared g n/n/(L:ℂ)^2 *
    weight A u θ P (Real.log n/L)

/-- Exact cutoff-preserving split; no condition on squarefreeness of g or n. -/
theorem fengBlock_decomposition (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ)
    (hg : g ≠ 0) :
    fengBlock N g L u θ P A = logBlock N g L u θ P A +
      outsideBlock N g L u θ P A + sharedBlock N g L u θ P A := by
  simp only [fengBlock,logBlock,outsideBlock,sharedBlock,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [feng_at_mul g n hg]
  simp only [Complex.ofReal_div,div_pow]
  ring

#print axioms fengBlock_decomposition
#print axioms coprime_divisors
#print axioms feng_at_mul
#print axioms mark_zero_of_not_prime_pow
#print axioms shared_prime_square
#print axioms coprimeScaled_entire
#print axioms coprimeScaled_derivative
#print axioms logBlock_derivatives
end XiPrime8845.FengAtG
