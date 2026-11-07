import PRZZArithmeticTime
import PRZZAFEDual

/-! Weighted time interchange for the literal finite mollifiers and both
actual Gamma-kernel series. The dual Gamma multiplier is retained. This
does not assert that their sum is the zeta product: contour residues and
horizontal edges remain separate obligations. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace XiPrime8845.PRZZMollifiedTime
open PRZZArithmeticTime PRZZActualDirectSum PRZZL1Finite PRZZAFEDual
set_option maxHeartbeats 3000000

theorem polynomial_continuous (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => PRZZ.dirichletPolynomial a N (1/2+t*I)) := by
  unfold PRZZ.dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hc : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
  simp_rw [Complex.cpow_def_of_ne_zero hc]
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  exact Complex.exp_ne_zero _

def mollifierWeight (φ : ℝ → ℂ) (c e : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  φ t * PRZZ.dirichletPolynomial c N (1/2+t*I) *
    star (PRZZ.dirichletPolynomial e N (1/2+t*I))

theorem mollifierWeight_continuous (φ : ℝ → ℂ) (hφ : Continuous φ)
    (c e : ℕ → ℂ) (N : ℕ) : Continuous (mollifierWeight φ c e N) :=
  (hφ.mul (polynomial_continuous c N)).mul (polynomial_continuous e N).star

theorem gammaPair_continuous (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    Continuous (gammaPair a b) := by
  change Continuous (fun t => gammaPair a b t)
  simp_rw [gammaPair_formula]
  apply continuous_const.mul
  have hleft : Continuous (fun t : ℝ => Gamma (leftArg a t/2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (PRZZGammaPath.gamma_analytic _ (by simp [leftArg]; linarith)).continuousAt.comp
    unfold leftArg
    fun_prop
  have hright : Continuous (fun t : ℝ => Gamma (rightArg b t/2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (PRZZGammaPath.gamma_analytic _ (by simp [rightArg]; linarith)).continuousAt.comp
    unfold rightArg
    fun_prop
  exact hleft.mul hright

theorem dualMultiplier_continuous (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 1/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 1/2) :
    Continuous (dualMultiplier a b) := by
  apply Continuous.div (gammaPair_continuous (-b) (-a) (by simp; linarith) (by simp; linarith))
    (gammaPair_continuous a b ha hb)
  intro t
  exact gammaPair_ne_zero a b t (by simp [leftArg]; linarith) (by simp [rightArg]; linarith)

/-- The time weight is the actual cutoff times both finite mollifiers. -/
theorem direct_mollified_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (R : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ) (c e : ℕ → ℂ) (N : ℕ) :
    (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R, mollifierWeight φ c e N t *
      directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) =
      ∫ t in Icc (-R) R, ∑' p : ℕ × ℕ, mollifierWeight φ c e N t *
        directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) :=
  weighted_time_swap a b ha ha' hb hb' hs R _ (mollifierWeight_continuous φ hφ c e N)

/-- The dual multiplier is proved continuous; it is not discarded or
replaced by a supplied bounded-weight hypothesis. -/
theorem dual_mollified_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 1/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 1/2) (hs : a+b ≠ 0)
    (R : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ) (c e : ℕ → ℂ) (N : ℕ) :
    (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R, (mollifierWeight φ c e N t * dualMultiplier a b t) *
      directTerm (-b) (-a) (actualWeight (-b) (-a)) t (p.1+1) (p.2+1)) =
      ∫ t in Icc (-R) R, ∑' p : ℕ × ℕ, (mollifierWeight φ c e N t * dualMultiplier a b t) *
        directTerm (-b) (-a) (actualWeight (-b) (-a)) t (p.1+1) (p.2+1) := by
  apply weighted_time_swap (-b) (-a) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by
      rw [show -b + -a = -(a+b) by ring]
      exact neg_ne_zero.mpr hs)
  exact (mollifierWeight_continuous φ hφ c e N).mul
    (dualMultiplier_continuous a b ha ha' hb hb')

/-- Remove the auxiliary compact time window using the original cutoff
support, without an assumed integrability statement. -/
theorem cutoff_integral (φ g : ℝ → ℂ) (R : ℝ)
    (hs : Function.support φ ⊆ Icc (-R) R) :
    (∫ t, φ t*g t) = ∫ t in Icc (-R) R, φ t*g t := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ Icc (-R) R
  · simp [ht]
  · have hz : φ t = 0 := by
      by_contra hz
      exact ht (hs hz)
    simp [ht,hz]

/-- Full real-line time integration for the literal cutoff and mollifiers.
The arithmetic series still uses the actual Gamma kernel. -/
theorem direct_full_time_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (R : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hsφ : Function.support φ ⊆ Icc (-R) R) (c e : ℕ → ℂ) (N : ℕ) :
    (∑' p : ℕ × ℕ, ∫ t, mollifierWeight φ c e N t *
      directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) =
      ∫ t, ∑' p : ℕ × ℕ, mollifierWeight φ c e N t *
        directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
  have hsupport : Function.support (mollifierWeight φ c e N) ⊆ Icc (-R) R := by
    intro t ht
    apply hsφ
    intro hz
    exact ht (by simp [mollifierWeight,hz])
  have hterm (p : ℕ × ℕ) := cutoff_integral (mollifierWeight φ c e N)
    (fun t => directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) R hsupport
  simp_rw [hterm]
  rw [direct_mollified_swap a b ha ha' hb hb' hs R φ hφ c e N]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ Icc (-R) R
  · simp [ht]
  · have hz : φ t = 0 := by
      by_contra hz
      exact ht (hsφ hz)
    simp [ht,mollifierWeight,hz]

#print axioms cutoff_integral
#print axioms direct_full_time_swap
#print axioms polynomial_continuous
#print axioms mollifierWeight_continuous
#print axioms gammaPair_continuous
#print axioms dualMultiplier_continuous
#print axioms direct_mollified_swap
#print axioms dual_mollified_swap
end XiPrime8845.PRZZMollifiedTime
