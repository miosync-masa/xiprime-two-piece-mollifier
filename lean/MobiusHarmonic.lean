import Mathlib

/-! Harmonic inversion and the qualitative logarithmic Mobius main term.
PNT is an explicit hypothesis where needed, never a new axiom. No quantitative
rate is required. The imported PNT+ theorem itself is not transplanted here. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction Finset Filter Topology MeasureTheory

namespace XiPrime8845.MobiusHarmonic

def reciprocal : ArithmeticFunction ℝ := ⟨fun n => 1 / (n : ℝ), by simp⟩
def mobiusReciprocal : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩

theorem reciprocal_convolution : mobiusReciprocal * reciprocal = 1 := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  rw [mul_apply]
  have he : (∑ x ∈ n.divisorsAntidiagonal,
      mobiusReciprocal x.1 * reciprocal x.2) =
      (∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ)) / n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
    change (μ x.1 : ℝ) / x.1 * (1 / (x.2 : ℝ)) = (μ x.1 : ℝ) / n
    rw [div_mul_div_comm, mul_one, ← Nat.cast_mul, hp]
  rw [he]
  have hm := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  rw [mul_apply] at hm
  simp only [natCoe_apply] at hm
  have hsum : (∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ)) =
      (1 : ArithmeticFunction ℝ) n := by
    convert hm using 1
    apply Finset.sum_congr rfl
    intro x hx
    simp [ArithmeticFunction.zeta_apply,
      Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx]
  rw [hsum]
  by_cases h : n = 1 <;> simp [h]

def harmonic (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, 1 / (n : ℝ)

theorem harmonic_inversion (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Ioc 0 N, (μ n : ℝ) / n * harmonic (N / n)) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum mobiusReciprocal reciprocal N
  rw [reciprocal_convolution] at h
  simpa [mobiusReciprocal, reciprocal, harmonic, ArithmeticFunction.one_apply,
    Nat.one_le_iff_ne_zero.mpr hN.ne'] using h.symm

def mobiusMass (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n
def logMean (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n * Real.log (x / n)
def harmonicError (x : ℝ) : ℝ := harmonic ⌊x⌋₊ - Real.log x - Real.eulerMascheroniConstant
def inversionError (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n * harmonicError (x / n)

theorem harmonic_inversion_real (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) / n * harmonic ⌊x / n⌋₊) = 1 := by
  simp_rw [Nat.floor_div_natCast]
  exact harmonic_inversion _ ((Nat.one_le_floor_iff x).mpr hx)

/-- Exact remainder identity; no cancellation estimate has been used. -/
theorem logMean_decomposition (x : ℝ) (hx : 1 ≤ x) :
    logMean x + Real.eulerMascheroniConstant * mobiusMass x + inversionError x = 1 := by
  rw [logMean, mobiusMass, inversionError, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  convert harmonic_inversion_real x hx using 1
  apply Finset.sum_congr rfl
  intro n hn
  unfold harmonicError
  ring

def remainderKernel (v : ℝ) : ℝ := harmonicError (1 / v) / v

theorem harmonic_eq_rat (N : ℕ) : harmonic N = (_root_.harmonic N : ℝ) := by
  simp only [harmonic, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    ← Finset.Icc_add_one_left_eq_Ioc, zero_add, one_div]

/-- A concrete bound valid for every real height, not just integral heights. -/
theorem harmonicError_bound (x : ℝ) (hx : 1 ≤ x) : |harmonicError x| ≤ 2 / x := by
  let N := ⌊x⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < N+1) hN0)
    rw [Real.log_div (by positivity) hN0.ne'] at hh
    convert hh using 1
    field_simp
    ring
  have hl : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
  have hu : Real.log x ≤ Real.log ((N : ℝ)+1) := Real.log_le_log (by linarith) hxN.le
  have hglo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hghi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    if_neg (by omega : N ≠ 0)] at hglo hghi
  have hsmall : |harmonicError x| ≤ 1 / N := by
    rw [abs_le, harmonicError, harmonic_eq_rat]
    change -(1 / (N : ℝ)) ≤ (_root_.harmonic N : ℝ) - Real.log x -
        Real.eulerMascheroniConstant ∧ _ ≤ _
    constructor <;> linarith
  apply hsmall.trans
  apply (div_le_div_iff₀ hN0 (by linarith : 0 < x)).mpr
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

theorem remainderKernel_bound (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    |remainderKernel v| ≤ 2 := by
  have h := harmonicError_bound (1/v) ((one_le_div hv).mpr hv1)
  rw [remainderKernel, abs_div, abs_of_pos hv]
  apply (div_le_iff₀ hv).mpr
  simpa only [div_div_eq_mul_div, div_one] using h

/-- Finite hyperbola swap for the part above a cutoff. -/
theorem harmonic_tail_swap (N X : ℕ) :
    (∑ n ∈ Ioc N X, (μ n : ℝ) / n * harmonic (X/n)) =
    ∑ j ∈ Ioc 0 X, (1/(j : ℝ)) *
      ∑ n ∈ Ioc N (X/j), (μ n : ℝ) / n := by
  let a : ArithmeticFunction ℝ :=
    ⟨fun n => if N < n then (μ n : ℝ)/n else 0, by simp⟩
  have h := sum_Ioc_mul_eq_sum_sum a reciprocal X
  rw [mul_comm, sum_Ioc_mul_eq_sum_sum] at h
  have hf (Y : ℕ) : (Ioc 0 Y).filter (fun n => N < n) = Ioc N Y := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  simp only [a, reciprocal, ArithmeticFunction.coe_mk, ite_mul, zero_mul,
    ← Finset.sum_filter, hf] at h
  exact h.symm

theorem harmonic_tail_short (N K : ℕ) (hN : 0 < N) (hK : 0 < K) :
    (∑ n ∈ Ioc N (K*N), (μ n : ℝ) / n * harmonic (K*N/n)) =
    ∑ j ∈ Ioc 0 K, (1/(j : ℝ)) *
      ∑ n ∈ Ioc N (K*N/j), (μ n : ℝ) / n := by
  rw [harmonic_tail_swap]
  symm
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl (by nlinarith : K ≤ K*N))
  intro j hj hjK
  have hj0 : 0 < j := (Finset.mem_Ioc.mp hj).1
  have hKj : K < j := by simpa only [Finset.mem_Ioc, hj0, true_and, not_le] using hjK
  have hd : K*N/j ≤ N := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hj0).mpr
    nlinarith
  simp [Finset.Ioc_eq_empty_of_le hd]

theorem sum_split (f : ℕ → ℝ) (N X : ℕ) (hNX : N ≤ X) :
    (∑ n ∈ Ioc 0 N, f n) + (∑ n ∈ Ioc N X, f n) = ∑ n ∈ Ioc 0 X, f n := by
  rw [← Finset.sum_union]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  · exact Finset.disjoint_left.mpr (by
      intro n hn hn'
      have := Finset.mem_Ioc.mp hn
      have := Finset.mem_Ioc.mp hn'
      omega)

def tailMass (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Ioc 0 K, (1/(j : ℝ)) * (mobiusMass (K*x/j) - mobiusMass x)

def headError (K : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)/n * harmonicError (K*x/n)

theorem harmonic_tail_real (K : ℕ) (hK : 0 < K) (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊K*x⌋₊, (μ n : ℝ)/n * harmonic (⌊K*x⌋₊/n)) = tailMass K x := by
  rw [harmonic_tail_swap]
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKX : K ≤ ⌊(K : ℝ)*x⌋₊ := Nat.le_floor (by nlinarith)
  have hcut : (∑ j ∈ Ioc 0 ⌊(K : ℝ)*x⌋₊, (1/(j : ℝ)) *
      ∑ n ∈ Ioc ⌊x⌋₊ (⌊(K : ℝ)*x⌋₊/j), (μ n : ℝ)/n) =
      ∑ j ∈ Ioc 0 K, (1/(j : ℝ)) *
        ∑ n ∈ Ioc ⌊x⌋₊ (⌊(K : ℝ)*x⌋₊/j), (μ n : ℝ)/n := by
    symm
    apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl hKX)
    intro j hj hjK
    have hj0 : 0 < j := (Finset.mem_Ioc.mp hj).1
    have hKj : K < j := by simpa only [Finset.mem_Ioc, hj0, true_and, not_le] using hjK
    have hd : ⌊(K : ℝ)*x⌋₊/j ≤ ⌊x⌋₊ := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hj0).mpr
      have ha := Nat.floor_le (show 0 ≤ (K : ℝ)*x by positivity)
      have hb := Nat.lt_floor_add_one x
      have hc : (K : ℝ) < j := by exact_mod_cast hKj
      have hxf : (0 : ℝ) ≤ ⌊x⌋₊ := by positivity
      have : (⌊(K : ℝ)*x⌋₊ : ℝ) < (⌊x⌋₊+1 : ℕ)*(j : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    simp [Finset.Ioc_eq_empty_of_le hd]
  rw [hcut, tailMass]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Ioc.mp hj).1
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Ioc.mp hj).2
  have hle : ⌊x⌋₊ ≤ ⌊(K : ℝ)*x⌋₊/j := by
    rw [← Nat.floor_div_natCast]
    apply Nat.floor_mono
    apply (le_div_iff₀ hj0).mpr
    nlinarith
  have h := sum_split (fun n => (μ n : ℝ)/n) _ _ hle
  simp only [mobiusMass, Nat.floor_div_natCast]
  linarith

/-- The head remainder is uniformly small when the dilation K is large. -/
theorem headError_bound (K : ℕ) (hK : 0 < K) (x : ℝ) (hx : 1 ≤ x) :
    |headError K x| ≤ 2 / K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hx0 : 0 < x := by linarith
  have hK0 : (0 : ℝ) < K := by positivity
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |(μ n : ℝ)/n * harmonicError (K*x/n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, 2 / ((K : ℝ)*x) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
        (Nat.floor_le hx0.le)
      have hz : 1 ≤ (K : ℝ)*x/n := (one_le_div hn0).mpr (by nlinarith)
      have hm : |(μ n : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      rw [abs_mul, abs_div, abs_of_pos hn0]
      have hh := mul_le_mul (div_le_div_of_nonneg_right hm hn0.le)
        (harmonicError_bound _ hz) (abs_nonneg _) (by positivity : 0 ≤ 1/(n : ℝ))
      convert hh using 1
      field_simp
    _ ≤ 2 / K := by
      simp only [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      apply (mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le)
        (by positivity : 0 ≤ 2 / ((K : ℝ)*x))).trans
      have : x*(2/((K : ℝ)*x)) = 2/K := by field_simp
      exact this.le

/-- Dilation isolates a head bounded by 2/K and only finitely many Mobius masses.
This avoids needing a separate Riemann-integrable-kernel cancellation theorem. -/
theorem dilation_identity (K : ℕ) (hK : 0 < K) (x : ℝ) (hx : 1 ≤ x) :
    logMean x + (Real.log K + Real.eulerMascheroniConstant) * mobiusMass x +
      headError K x + tailMass K x = 1 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by positivity
  have hx0 : 0 < x := by linarith
  have hle : ⌊x⌋₊ ≤ ⌊(K : ℝ)*x⌋₊ := Nat.floor_mono (by nlinarith)
  have h := sum_split (fun n => (μ n : ℝ)/n * harmonic (⌊(K : ℝ)*x⌋₊/n))
    _ _ hle
  rw [harmonic_inversion _ ((Nat.one_le_floor_iff _).mpr (by nlinarith)),
    harmonic_tail_real K hK x hx] at h
  have hh : (∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)/n * harmonic (⌊(K : ℝ)*x⌋₊/n)) =
      logMean x + (Real.log K + Real.eulerMascheroniConstant) * mobiusMass x + headError K x := by
    rw [logMean, mobiusMass, headError, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
    rw [harmonicError, Nat.floor_div_natCast,
      show (K : ℝ)*x/n = K*(x/n) by ring, Real.log_mul hK0.ne' (div_ne_zero hx0.ne' hn0)]
    ring
  rw [hh] at h
  exact h

theorem tailMass_tendsto (K : ℕ) (hK : 0 < K)
    (hm : Tendsto mobiusMass atTop (nhds 0)) : Tendsto (tailMass K) atTop (nhds 0) := by
  have hK0 : (0 : ℝ) < K := by positivity
  have hterm (j : ℕ) (hj : j ∈ Ioc 0 K) :
      Tendsto (fun x : ℝ => (1/(j : ℝ)) * (mobiusMass (K*x/j) - mobiusMass x))
        atTop (nhds 0) := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Ioc.mp hj).1
    simpa using ((hm.comp ((tendsto_id.const_mul_atTop hK0).atTop_div_const hj0)).sub hm).const_mul (1/(j : ℝ))
  unfold tailMass
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Ioc 0 K) hterm

/-- Qualitative cancellation of sum mu(n)/n is enough for the smoothed main term.
The PNT input is an explicit argument; no quantitative rate and no new axiom. -/
theorem logMean_tendsto_of_mass
    (hm : Tendsto mobiusMass atTop (nhds 0)) : Tendsto logMean atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨K, hK⟩ := exists_nat_gt (4/eps)
  have hK0 : (0 : ℝ) < K := lt_trans (by positivity : (0 : ℝ) < 4/eps) hK
  have hKn : 0 < K := by exact_mod_cast hK0
  have hsmall : 2/(K : ℝ) < eps/2 := by
    have hh := (div_lt_iff₀ heps).mp hK
    apply (div_lt_iff₀ hK0).mpr
    nlinarith
  have hrem : Tendsto (fun x => (Real.log K + Real.eulerMascheroniConstant)*mobiusMass x +
      tailMass K x) atTop (nhds 0) := by
    simpa using (hm.const_mul (Real.log K + Real.eulerMascheroniConstant)).add
      (tailMass_tendsto K hKn hm)
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hrem (eps/2) (by positivity)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right X 1).trans hx
  have hr : |(Real.log K + Real.eulerMascheroniConstant)*mobiusMass x + tailMass K x| < eps/2 := by
    simpa only [Real.dist_eq, sub_zero] using hX x ((le_max_left X 1).trans hx)
  rw [Real.dist_eq]
  calc
    |logMean x - 1| = |-(headError K x) -
        ((Real.log K + Real.eulerMascheroniConstant)*mobiusMass x + tailMass K x)| := by
      congr 1
      linarith [dilation_identity K hKn x hx1]
    _ ≤ |headError K x| + |(Real.log K + Real.eulerMascheroniConstant)*mobiusMass x + tailMass K x| := by
      simpa only [abs_neg] using abs_sub (-(headError K x))
        ((Real.log K + Real.eulerMascheroniConstant)*mobiusMass x + tailMass K x)
    _ < eps := by linarith [headError_bound K hKn x hx1]

theorem inversionError_kernel (x : ℝ) (hx : 0 < x) :
    inversionError x = (∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * remainderKernel (n / x)) / x := by
  rw [inversionError, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
  unfold remainderKernel
  rw [one_div_div]
  field_simp

/-- Alternative decomposition-based transfer with both errors explicit.
`logMean_tendsto_of_mass` above needs only the first input. -/
theorem logMean_tendsto_of_errors
    (hm : Tendsto mobiusMass atTop (nhds 0))
    (he : Tendsto inversionError atTop (nhds 0)) :
    Tendsto logMean atTop (nhds 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (hm.const_mul Real.eulerMascheroniConstant)).sub he
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  linarith [logMean_decomposition x hx]

theorem mass_sum_Icc (x : ℝ) :
    (∑ n ∈ Icc 0 ⌊x⌋₊, (μ n : ℝ) / n) = mobiusMass x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [mobiusMass]

theorem mass_range_endpoint (x : ℝ) :
    mobiusMass x = (∑ n ∈ range ⌊x⌋₊, (μ n : ℝ)/n) + (μ ⌊x⌋₊ : ℝ)/⌊x⌋₊ := by
  rw [← mass_sum_Icc, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ]

/-- Adapter for the exact range convention and little-o type of PNT+ mu_pnt_alt.
The caller must supply that proved theorem; this is not an axiom or a PNT proof. -/
theorem mass_tendsto_of_mu_pnt_alt
    (h : (fun x : ℝ => ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ)/n) =o[atTop] (fun _ => (1 : ℝ))) :
    Tendsto mobiusMass atTop (nhds 0) := by
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with x hx
    have := Nat.lt_floor_add_one x
    linarith
  have hedge : Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ)/⌊x⌋₊) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg _) _ (tendsto_inv_atTop_zero.comp hf)
    intro x
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Nat.cast_nonneg ⌊x⌋₊ : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ))]
    have hm : |(μ ⌊x⌋₊ : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := ⌊x⌋₊))
    dsimp only [Function.comp_apply]
    simpa only [one_div] using div_le_div_of_nonneg_right hm (Nat.cast_nonneg ⌊x⌋₊)
  have hh := ((Asymptotics.isLittleO_one_iff ℝ).mp h).add hedge
  simpa only [← mass_range_endpoint, add_zero] using hh

theorem logMean_tendsto_of_mu_pnt_alt
    (h : (fun x : ℝ => ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ)/n) =o[atTop] (fun _ => (1 : ℝ))) :
    Tendsto logMean atTop (nhds 1) :=
  logMean_tendsto_of_mass (mass_tendsto_of_mu_pnt_alt h)

def linearProfile (L u : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊, (μ n : ℝ)/n * (u - Real.log n/L)

theorem scaled_linearProfile (L u : ℝ) (hL : L ≠ 0) :
    L * linearProfile L u = logMean (Real.exp (L*u)) := by
  rw [linearProfile, logMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
  rw [Real.log_div (Real.exp_ne_zero _) hn0, Real.log_exp]
  field_simp

/-- The linear test already realizes the 1/L leading term. Uniformity is on
u >= u0 > 0; no false uniform convergence at the u=0 endpoint is claimed. -/
theorem linearProfile_uniform_of_mass (u0 : ℝ) (hu0 : 0 < u0)
    (hm : Tendsto mobiusMass atTop (nhds 0)) :
    TendstoUniformlyOn (fun L u => L * linearProfile L u) (fun _ => 1)
      atTop (Set.Ici u0) := by
  have hJ := logMean_tendsto_of_mass hm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hJ eps heps
  have hexp : Tendsto (fun L : ℝ => Real.exp (L*u0)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hu0)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hexp.eventually (eventually_ge_atTop X)] with L hL hLX
  intro u hu
  rw [scaled_linearProfile L u hL.ne', dist_comm]
  exact hX _ (hLX.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hL.le)))

theorem linearProfile_uniform_of_mu_pnt_alt (u0 : ℝ) (hu0 : 0 < u0)
    (h : (fun x : ℝ => ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ)/n) =o[atTop] (fun _ => (1 : ℝ))) :
    TendstoUniformlyOn (fun L u => L * linearProfile L u) (fun _ => 1)
      atTop (Set.Ici u0) :=
  linearProfile_uniform_of_mass u0 hu0 (mass_tendsto_of_mu_pnt_alt h)

/-- Abel summation identifies J with the logarithmic primitive of the mass. -/
theorem logMean_integral (x : ℝ) (hx : 1 ≤ x) :
    logMean x = ∫ t in Set.Ioc 1 x, mobiusMass t / t := by
  have hf : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := by
    intro t ht
    exact Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hi : IntegrableOn (deriv Real.log) (Set.Icc (1 : ℝ) x) := by
    have he : deriv Real.log = fun t => t⁻¹ := funext Real.deriv_log
    rw [he]
    exact (continuousOn_id.inv₀ (fun t ht =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).integrableOn_compact isCompact_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => (μ n : ℝ) / n)
    (by simp) x hf hi
  rw [mass_sum_Icc] at h
  simp_rw [Real.deriv_log, mass_sum_Icc] at h
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons] at h
  simp only [Nat.cast_zero, Real.log_zero, zero_mul, zero_add] at h
  have he : logMean x = Real.log x * mobiusMass x -
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * ((μ n : ℝ) / n) := by
    rw [logMean, mobiusMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
    rw [Real.log_div (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)) hn0]
    ring
  rw [he, h]
  simp only [sub_sub_cancel, div_eq_mul_inv, mul_comm]

#print axioms reciprocal_convolution
#print axioms harmonic_inversion
#print axioms harmonic_inversion_real
#print axioms harmonicError_bound
#print axioms remainderKernel_bound
#print axioms harmonic_tail_swap
#print axioms harmonic_tail_real
#print axioms headError_bound
#print axioms dilation_identity
#print axioms tailMass_tendsto
#print axioms logMean_tendsto_of_mass
#print axioms logMean_decomposition
#print axioms inversionError_kernel
#print axioms logMean_tendsto_of_errors
#print axioms logMean_integral
#print axioms mass_tendsto_of_mu_pnt_alt
#print axioms logMean_tendsto_of_mu_pnt_alt
#print axioms scaled_linearProfile
#print axioms linearProfile_uniform_of_mass
#print axioms linearProfile_uniform_of_mu_pnt_alt
end XiPrime8845.MobiusHarmonic
