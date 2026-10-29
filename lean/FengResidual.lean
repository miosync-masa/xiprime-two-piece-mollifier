import FengSharedBlock

/-! Exact p-adic reindexing of the shared residual. All prime powers, translated
profiles and finite cutoffs are retained. No shared term is declared negligible. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.FengResidual
open FengAtG FengSharedBlock CoprimeShift ShiftWeights
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem factorization_pow_mul (p a m : ℕ) (hp : p.Prime)
    (hm : m ≠ 0) (hc : p.Coprime m) : (p^a*m).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm]
  simp [hp.factorization,
    Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hc)]

/-- Unique p-power times p-free decomposition of the entire finite interval.
For N=0 all inner sums are empty, including the a=0 summand. -/
theorem prime_power_reindex (N p : ℕ) (hp : p.Prime) (f : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, f n) =
      ∑ a ∈ range (Nat.log p N+1),
        ∑ m ∈ (Icc 1 (N/p^a)).filter (fun m => p.Coprime m), f (p^a*m) := by
  rw [Finset.sum_sigma' (range (Nat.log p N+1))
    (fun a => (Icc 1 (N/p^a)).filter (fun m => p.Coprime m))]
  symm
  apply Finset.sum_bij (fun x _ => p^x.1*x.2)
  · intro x hx
    obtain ⟨ha,hm⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hm,hc⟩ := mem_filter.mp hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨Nat.mul_pos (pow_pos hp.pos _) hm1,
      by simpa only [mul_comm] using (Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mp hmN⟩
  · intro x hx y hy he
    obtain ⟨_,hm⟩ := Finset.mem_sigma.mp hx
    obtain ⟨_,hn⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hm,hcm⟩ := mem_filter.mp hm
    obtain ⟨hn,hcn⟩ := mem_filter.mp hn
    have hxm : x.2 ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    have hyn : y.2 ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have ha := congrArg (fun n : ℕ => n.factorization p) he
    rw [factorization_pow_mul p x.1 x.2 hp hxm hcm,
      factorization_pow_mul p y.1 y.2 hp hyn hcn] at ha
    have hm : x.2 = y.2 := by
      rw [ha] at he
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) he
    exact Sigma.ext ha (heq_of_eq hm)
  · intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    let a := n.factorization p
    let m := n/p^a
    have he : p^a*m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    refine ⟨⟨a,m⟩,?_,he⟩
    apply Finset.mem_sigma.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩⟩
    · exact Nat.le_log_of_pow_le hp.one_lt
        ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.ordProj_dvd n p)).trans (mem_Icc.mp hn).2)
    · exact Nat.ordCompl_pos p hn0
    · apply (Nat.le_div_iff_mul_le (pow_pos hp.pos a)).mpr
      simpa only [mul_comm,he] using (mem_Icc.mp hn).2
    · exact Nat.coprime_ordCompl hp hn0
  · intros; rfl

/-- The p-free coprimality indicator becomes coprimality to h*p. -/
theorem residual_weighted (N p h : ℕ) (hp : p.Prime) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N,
      (if (n/p^(n.factorization p)).Coprime h then (μ (n/p^(n.factorization p)):ℂ) else 0)*w n) =
      ∑ a ∈ range (Nat.log p N+1),
        ∑ m ∈ (Icc 1 (N/p^a)).filter (fun m => m.Coprime (h*p)),
          (μ m:ℂ)*w (p^a*m) := by
  rw [prime_power_reindex N p hp]
  apply sum_congr rfl
  intro a ha
  simp only [Finset.sum_filter]
  apply sum_congr rfl
  intro m hm
  by_cases hc : p.Coprime m
  · rw [if_pos hc, Nat.ordCompl_pow_mul_of_not_dvd a hp (hp.coprime_iff_not_dvd.mp hc)]
    by_cases hh : m.Coprime h
    · have hh' : m.Coprime (h*p) := Nat.coprime_mul_iff_right.mpr ⟨hh,hc.symm⟩
      rw [if_pos hh, if_pos hh']
    · simp [hh, Nat.coprime_mul_iff_right]
  · have hc' : ¬ m.Coprime p := fun h => hc h.symm
    simp [hc, hc', Nat.coprime_mul_iff_right]

/-- Exact unnormalized residual, with each prime-power cutoff left finite. -/
theorem residualInner_expansion (N p h : ℕ) (hp : p.Prime)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    residualInner N p h L u θ P A =
      ∑ a ∈ range (Nat.log p N+1), supportFactor (p^a) L A *
        coprimeInner (N/p^a) (h*p) L (u-Real.log (p^a)/L) θ P A := by
  have he : residualInner N p h L u θ P A =
      ∑ n ∈ Icc 1 N,
        (if (n/p^(n.factorization p)).Coprime h then (μ (n/p^(n.factorization p)):ℂ) else 0)*
          (weight A u θ P (Real.log n/L)/(n:ℂ)) := by
    unfold residualInner
    apply sum_congr rfl
    intros
    ring
  rw [he,residual_weighted N p h hp]
  apply sum_congr rfl
  intro a ha
  rw [coprimeInner,Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  have hp0 : ((p^a:ℕ):ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero a hp.ne_zero
  have hm0 : (m:ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by have := (mem_Icc.mp (mem_filter.mp hm).1).1; omega)
  rw [Nat.cast_mul,Real.log_mul hp0 hm0,add_div,weight_translate]
  unfold supportFactor
  push_cast
  ring

/-- The normalization is L times the residual, not an additional 1/L. -/
theorem residual_scaled (N p h : ℕ) (hp : p.Prime)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    (L:ℂ)*residualInner N p h L u θ P A =
      ∑ a ∈ range (Nat.log p N+1), supportFactor (p^a) L A *
        coprimeScaled (N/p^a) (h*p) L (u-Real.log (p^a)/L) θ P A := by
  rw [residualInner_expansion N p h hp,Finset.mul_sum]
  apply sum_congr rfl
  intros
  unfold coprimeScaled
  ring

/-- At the exponential cutoff, each shifted inner cutoff is exact, also at
the endpoint where u-log(p^a)/L is zero. -/
theorem residual_scaled_cutoff (p h : ℕ) (hp : p.Prime)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) (hL : L ≠ 0) :
    (L:ℂ)*residualInner ⌊Real.exp (L*u)⌋₊ p h L u θ P A =
      ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊+1), supportFactor (p^a) L A *
        coprimeScaled ⌊Real.exp (L*(u-Real.log (p^a)/L))⌋₊ (h*p)
          L (u-Real.log (p^a)/L) θ P A := by
  rw [residual_scaled _ p h hp]
  apply sum_congr rfl
  intro a ha
  rw [translated_cutoff L u (p^a) hL (pow_ne_zero a hp.ne_zero)]
  simp only [Nat.cast_pow]

/-- Only the coefficient is geometric. The inner cutoff and profile still
depend on a, so no infinite Euler factor is substituted in the finite sum. -/
theorem supportFactor_pow (p a : ℕ) (L : ℝ) (A : ℂ) :
    supportFactor (p^a) L A = (supportFactor p L A)^a := by
  simp only [supportFactor, Nat.cast_pow, Real.log_pow, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [show -A*((a:ℂ)*(Real.log p:ℂ)/(L:ℂ)) =
    (a:ℂ)*(-A*((Real.log p:ℂ)/(L:ℂ))) by ring, Complex.exp_nat_mul, div_pow]

theorem residual_scaled_geometric (N p h : ℕ) (hp : p.Prime)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    (L:ℂ)*residualInner N p h L u θ P A =
      ∑ a ∈ range (Nat.log p N+1), (supportFactor p L A)^a *
        coprimeScaled (N/p^a) (h*p) L (u-Real.log (p^a)/L) θ P A := by
  rw [residual_scaled N p h hp]
  simp only [supportFactor_pow]

/-- The actual sharedBlock connected to the existing coprimeScaled family.
mu(h) is retained even when g is not squarefree; no limit has been taken. -/
theorem sharedBlock_coprimeScaled (N g : ℕ) (hg : g ≠ 0)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    sharedBlock N g L u θ P A =
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ) *
          ∑ a ∈ range (Nat.log p N+1), supportFactor (p^a) L A *
            coprimeScaled (N/p^a) ((g/p^(g.factorization p))*p)
              L (u-Real.log (p^a)/L) θ P A := by
  rw [sharedBlock_residual N g L u θ P A hg]
  apply sum_congr rfl
  intro p hp
  rw [residual_scaled N p _ (Nat.prime_of_mem_primeFactors hp)]

#print axioms factorization_pow_mul
#print axioms prime_power_reindex
#print axioms residual_weighted
#print axioms residualInner_expansion
#print axioms residual_scaled
#print axioms residual_scaled_cutoff
#print axioms sharedBlock_coprimeScaled
#print axioms supportFactor_pow
#print axioms residual_scaled_geometric
end XiPrime8845.FengResidual
