import PRZZProductTime
import PRZZOptimalPowers
import PRZZOptimalOuter
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual time averages retain the off-diagonal frequency gaps. No
mean-value estimate is declared as an external arithmetic input. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZMeanSquare
set_option maxHeartbeats 3000000

def phase (u t : ℝ) : ℂ := exp ((u:ℂ)*I*t)

theorem phase_norm (u t : ℝ) : ‖phase u t‖ = 1 := by
  simp [phase,norm_exp]

theorem phase_integral (T u : ℝ) (hT : 0 ≤ T) (hu : u ≠ 0) :
    ‖∫ t in Icc T (2*T), phase u t‖ ≤ 2/|u| := by
  have hc : (u:ℂ)*I ≠ 0 := mul_ne_zero (by exact_mod_cast hu) I_ne_zero
  have he := integral_exp_mul_complex (a := T) (b := 2*T) hc
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc] at he
  change (∫ t in Icc T (2*T), phase u t) = _ at he
  rw [he,norm_div]
  have h1 : ‖exp ((u:ℂ)*I*(2*T:ℝ))‖ = 1 := phase_norm u (2*T)
  have h2 : ‖exp ((u:ℂ)*I*T)‖ = 1 := phase_norm u T
  have hh := norm_sub_le (exp ((u:ℂ)*I*(2*T:ℝ))) (exp ((u:ℂ)*I*T))
  rw [h1,h2] at hh
  norm_num only [Nat.reduceAdd] at hh
  simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hh (norm_nonneg ((u:ℂ)*I))

theorem summand (c : ℂ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    c/(n:ℂ)^(1/2+t*I) = (c/(n:ℂ)^(1/2:ℂ))*phase (-Real.log n) t := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_add _ _ hn0]
  simp only [phase,Complex.cpow_def_of_ne_zero hn0]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_log (by positivity)]
  rw [div_mul_eq_div_mul_one_div]
  simp only [one_div,← Complex.exp_neg]
  congr 1
  congr 1
  push_cast
  ring

theorem phase_pair (u v t : ℝ) : phase u t * star (phase v t) = phase (u-v) t := by
  change exp ((u:ℂ)*I*t) * starRingEnd ℂ (exp ((v:ℂ)*I*t)) = exp (((u-v:ℝ):ℂ)*I*t)
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,conj_ofReal,conj_I,ofReal_sub]
  ring

def mean (c : ℕ → ℂ) (N : ℕ) (T : ℝ) : ℝ :=
  ∫ t in Icc T (2*T), ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖^2

theorem mean_nonneg (c : ℕ → ℂ) (N : ℕ) (T : ℝ) : 0 ≤ mean c N T :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem exponential_gram {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → ℝ) (T : ℝ) :
    (((∫ t in Icc T (2*T), (‖∑ i ∈ s, c i*phase (u i) t‖^2:ℝ)):ℝ):ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, c i*star (c j)*(∫ t in Icc T (2*T), phase (u i-u j) t) := by
  rw [← integral_complex_ofReal]
  have he (t : ℝ) : ((‖∑ i ∈ s, c i*phase (u i) t‖^2:ℝ):ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, c i*star (c j)*phase (u i-u j) t := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj]
    simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [← phase_pair]
    simp only [starRingEnd_apply]
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
    · intro j hj
      exact (show Continuous (fun t : ℝ => c i*star (c j)*phase (u i-u j) t) by unfold phase; fun_prop).integrableOn_Icc
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (show Continuous (fun t : ℝ => c i*star (c j)*phase (u i-u j) t) by unfold phase; fun_prop).integrableOn_Icc

/-- Each oscillatory pair is integrated before taking its norm. The
diagonal costs T, while nonzero frequency gaps cost at most 2/|gap|. -/
theorem exponential_mean_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (u : ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hu : Set.InjOn u s) :
    (∫ t in Icc T (2*T), ‖∑ i ∈ s, c i*phase (u i) t‖^2) ≤
      ∑ i ∈ s, ∑ j ∈ s, ‖c i‖*‖c j‖*(if i=j then T else 2/|u i-u j|) := by
  have hn : 0 ≤ ∫ t in Icc T (2*T), ‖∑ i ∈ s, c i*phase (u i) t‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hh := congrArg norm (exponential_gram s c u T)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn] at hh
  rw [hh]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul,norm_star]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases hij : i=j
  · subst j
    simp [phase,show 0 ≤ 2*T-T by linarith]
    simp only [show (2:ℂ)*T-T = T by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT,le_refl]
  · rw [if_neg hij]
    exact phase_integral T _ hT (sub_ne_zero.mpr (fun h => hij (hu hi hj h)))

theorem polynomial_expansion (c : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    PRZZ.dirichletPolynomial c N (1/2+t*I) =
      ∑ n ∈ Finset.Icc 1 N, (c n/(n:ℂ)^(1/2:ℂ))*phase (-Real.log n) t := by
  apply Finset.sum_congr rfl
  intro n hn
  exact summand _ _ (Finset.mem_Icc.mp hn).1 t

theorem log_gap (N m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmN : m ≤ N) (hnN : n ≤ N) (hmn : m ≠ n) :
    1/(N:ℝ) ≤ |Real.log m-Real.log n| := by
  have hpos (k : ℕ) (hk : 1 ≤ k) : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hstep (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjN : j ≤ N) :
      1/(N:ℝ) ≤ Real.log j-Real.log i := by
    have hi0 := hpos i hi
    have hj0 : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hj0 hi0)
    rw [Real.log_div hj0.ne' hi0.ne',inv_div] at hh
    have hd : (1:ℝ) ≤ (j:ℝ)-i := by
      have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
      linarith
    have hNj : (j:ℝ) ≤ N := by exact_mod_cast hjN
    calc
      1/(N:ℝ) ≤ 1/(j:ℝ) := one_div_le_one_div_of_le hj0 hNj
      _ ≤ 1-(i:ℝ)/j := by apply (div_le_iff₀ hj0).mpr; field_simp; nlinarith
      _ ≤ _ := hh
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (hstep m n hm hlt hnN).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · exact (hstep n m hn hgt hmN).trans (le_abs_self _)

/-- Elementary mean-square bound with a deliberately coarse but supplied
off-diagonal cost. It keeps the diagonal energy separate from the l1 mass. -/
theorem polynomial_mean (c : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    mean c N T ≤ T*(∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖^2) +
      2*(N:ℝ)*(∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖)^2 := by
  have hu : Set.InjOn (fun n : ℕ => -Real.log n) (Finset.Icc 1 N) := by
    intro m hm n hn he
    have hm0 : (0:ℝ) < m := by exact_mod_cast (by have := (Finset.mem_Icc.mp hm).1; omega : 0 < m)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
    exact_mod_cast Real.log_injOn_pos hm0 hn0 (neg_injective he)
  have hh := exponential_mean_bound (Finset.Icc 1 N)
    (fun n => c n/(n:ℂ)^(1/2:ℂ)) (fun n => -Real.log n) T hT hu
  simp_rw [← polynomial_expansion] at hh
  apply hh.trans
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((if m=n then T*‖c m/(m:ℂ)^(1/2:ℂ)‖^2 else 0) +
          2*(N:ℝ)*‖c m/(m:ℂ)^(1/2:ℂ)‖*‖c n/(n:ℂ)^(1/2:ℂ)‖) := by
      apply Finset.sum_le_sum; intro m hm
      apply Finset.sum_le_sum; intro n hn
      by_cases hmn : m=n
      · subst n; simp only [ite_true]; nlinarith [mul_nonneg (show (0:ℝ) ≤ N by positivity) (sq_nonneg ‖c m/(m:ℂ)^(1/2:ℂ)‖)]
      · simp only [if_neg hmn,zero_add]
        have hg := log_gap N m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1
          (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hn).2 hmn
        have hN : (0:ℝ) < N := by exact_mod_cast (by have := Finset.mem_Icc.mp hm; omega : 0 < N)
        have hb : 2/|-Real.log m- -Real.log n| ≤ 2*(N:ℝ) := by
          rw [show -Real.log (m:ℝ)- -Real.log n = -(Real.log m-Real.log n) by ring,abs_neg]
          apply (div_le_iff₀ ((one_div_pos.mpr hN).trans_le hg)).mpr
          have := (div_le_iff₀ hN).mp hg
          nlinarith
        exact (mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq]
      simp only [Finset.sum_ite_mem]
      simp only [Finset.inter_self]
      rw [sq]
      simp only [Finset.mul_sum,Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem normalized_norm (c : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ‖c/(n:ℂ)^(1/2:ℂ)‖ = ‖c‖/Real.sqrt n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [norm_div,← Complex.ofReal_natCast n, norm_cpow_eq_rpow_re_of_pos hn0]
  have he : (1/2:ℂ).re = (1/2:ℝ) := by norm_num
  rw [he,← Real.sqrt_eq_rpow]

/-- An elementary supplied average; no mean-value theorem is a premise.
The coarse diagonal sqrt N is already enough for the PRZZ target powers. -/
theorem bounded_mean (c : ℕ → ℂ) (N : ℕ) (T A : ℝ) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hc : ∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ A) :
    mean c N T ≤ A^2*(2*T*Real.sqrt N+8*(N:ℝ)^2) := by
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖) ≤ 2*A*Real.sqrt N := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, A*(1/Real.sqrt n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [normalized_norm _ _ (Finset.mem_Icc.mp hn).1]
        simpa only [mul_one_div] using div_le_div_of_nonneg_right (hc n hn) (Real.sqrt_nonneg _)
      _ = A*(∑ n ∈ Finset.Icc 1 N, 1/Real.sqrt n) := (Finset.mul_sum ..).symm
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (PRZZReplacementMass.reciprocal_sqrt_sum N) hA
        nlinarith
  have hdiag : (∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖^2) ≤ 2*A^2*Real.sqrt N := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, A*‖c n/(n:ℂ)^(1/2:ℂ)‖ := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hs : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
        have hh : ‖c n/(n:ℂ)^(1/2:ℂ)‖ ≤ A := by
          rw [normalized_norm _ _ (Finset.mem_Icc.mp hn).1]
          exact (div_le_self (norm_nonneg _) hs).trans (hc n hn)
        nlinarith [norm_nonneg (c n/(n:ℂ)^(1/2:ℂ))]
      _ = A*(∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsum hA]
  have hmass0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n/(n:ℂ)^(1/2:ℂ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsquare := sq_le_sq₀ hmass0 (by positivity) |>.mpr hsum
  have hh := polynomial_mean c N T hT
  have hn : (Real.sqrt N)^2 = (N:ℝ) := Real.sq_sqrt (by positivity)
  have heq : (2*A*Real.sqrt N)^2 = 4*A^2*(N:ℝ) := by
    calc
      _ = 4*A^2*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [hn]
  rw [heq] at hsquare
  nlinarith [mul_le_mul_of_nonneg_left hdiag hT,
    mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2*(N:ℝ) by positivity)]

/-- Transfer the already proved V-W estimate through the actual mean
square. There is no pointwise N multiplier in this statement. -/
theorem replacement_mean (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ (c : ℕ → ℂ) (N : ℕ)
      (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c c N t *
      PRZZReplacementIntegral.difference a b t‖ ≤
      C*(1+32/‖a+b‖^2)*T^(eps-s)*P*mean c N T := by
  obtain ⟨C,hC,h⟩ := PRZZProductSummation.integrated_bound s eps hs hs' he he'
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' c N phi P hphi hP hp
  rw [PRZZProductTime.difference_integral a b ha hb hab T hT hT']
  apply (h a b ha hb hab hsa hsb T hT hT' _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi c c N)).trans
  have hi : (∫ t in Icc T (2*T), ‖PRZZMollifiedTime.mollifierWeight phi c c N t‖) ≤
      P*mean c N T := by
    rw [mean,← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (((PRZZMollifiedTime.polynomial_continuous c N).norm.pow 2).const_mul P).integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [PRZZMollifiedTime.mollifierWeight,norm_mul,norm_star]
    change ‖phi t‖ * ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖ *
      ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖ ≤ P*‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖^2
    nlinarith [mul_le_mul_of_nonneg_right (hp t ht)
      (sq_nonneg ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

/-- The supplied mean suffices for the target powers after the leading
T^(-1/2) kernel saving. Small positive exponent losses remain separate. -/
theorem mean_scale_target (N T : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T) :
    (2*T*Real.sqrt N+8*N^2)/Real.sqrt T ≤ 10*PRZZOptimalPowers.target N T := by
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have h1 : Real.sqrt N ≤ N^(7/8:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have h2 : N^(1/4:ℝ) ≤ Real.sqrt T := by
    calc
      _ ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      _ = Real.sqrt N := Real.sqrt_eq_rpow N |>.symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hNT
  have he : N^2 = N^(1/4:ℝ)*N^(7/4:ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  have hh : N^2 ≤ Real.sqrt T*N^(7/4:ℝ) := by
    rw [he]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn.le _)
  have hfirst := mul_le_mul_of_nonneg_left h1 ht.le
  apply (div_le_iff₀ hs).mpr
  unfold PRZZOptimalPowers.target
  rw [← Real.sqrt_eq_rpow]
  have hsq := Real.sq_sqrt ht.le
  have ht1 : T*N^(7/8:ℝ) = Real.sqrt T*(Real.sqrt T*N^(7/8:ℝ)) := by
    rw [← mul_assoc,← sq,hsq]
  rw [ht1] at hfirst
  nlinarith [mul_nonneg hs.le (Real.rpow_nonneg hn.le (7/4:ℝ)),
    mul_nonneg hs.le (mul_nonneg hs.le (Real.rpow_nonneg hn.le (7/8:ℝ)))]

theorem source_mean (js : List ℕ) (N : ℕ) (T : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T) :
    mean (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N T ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*(2*T*Real.sqrt N+8*(N:ℝ)^2) := by
  have hc : ∀ n ∈ Finset.Icc 1 N, ‖(PRZZGCoefficient.coefficient js n:ℂ)‖ ≤
      (Real.log N)^PRZZGCoefficient.degree js := by
    intro n hn
    simpa using PRZZGCoefficient.coefficient_bound js N hN n
      (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  have hh := bounded_mean (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N T
    ((Real.log N)^PRZZGCoefficient.degree js) hT
    (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _) hc
  simpa [← pow_mul,mul_comm] using hh

/-- The concrete arithmetic coefficients are supplied, not a coefficient
mass assumption. The time weight is controlled by its interval supremum. -/
theorem replacement_source (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ (js : List ℕ) (N : ℕ), 1 ≤ N →
    ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
      PRZZReplacementIntegral.difference a b t‖ ≤
      C*(1+32/‖a+b‖^2)*T^(eps-s)*P*
        ((Real.log N)^(2*PRZZGCoefficient.degree js)*(2*T*Real.sqrt N+8*(N:ℝ)^2)) := by
  obtain ⟨C,hC,h⟩ := replacement_mean s eps hs hs' he he'
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' js N hN phi P hphi hP hp
  exact (h a b ha hb hab hsa hsb T hT hT' _ N phi P hphi hP hp).trans
    (mul_le_mul_of_nonneg_left (source_mean js N T hN (by linarith)) (by positivity))

/-- The replacement error reaches the target N,T powers under explicit
shift and exponent margins. This does not assert the other AFE errors. -/
theorem replacement_target (js : List ℕ) (s eps delta : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1/2) (he : 0 < eps) (he' : eps ≤ 1/2)
    (hmargin : eps-s+1/2 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
    ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
      PRZZReplacementIntegral.difference a b t‖ ≤
      C*(1+32/‖a+b‖^2)*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := replacement_source s eps hs hs' he he'
  obtain ⟨D,hD,hloss⟩ := PRZZOptimalOuter.power_log_absorbed
    (2*PRZZGCoefficient.degree js) (eps-s+1/2) delta hmargin
  refine ⟨10*C*D,by positivity,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' N hN hNT phi P hphi hP hp
  have ht : 0 < T := by linarith
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hn
  have hl : Real.log (N:ℝ) ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hlogT : 0 ≤ Real.log T := hlog.trans hl
  have hscale := (div_le_iff₀ (Real.sqrt_pos.mpr ht)).mp (mean_scale_target N T hn hNT)
  have htar : 0 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target; positivity
  have hpw : T^(eps-s)*Real.sqrt T = T^(eps-s+1/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add ht]
  have hbudget : (Real.log (N:ℝ))^(2*PRZZGCoefficient.degree js)*
      (2*T*Real.sqrt N+8*(N:ℝ)^2) ≤
      (Real.log T)^(2*PRZZGCoefficient.degree js)*
        (10*PRZZOptimalPowers.target N T*Real.sqrt T) := by
    exact mul_le_mul (pow_le_pow_left₀ hlog hl _) hscale (by positivity) (by positivity)
  have hmain := h a b ha hb hab hsa hsb T hT hT' js N hN phi P hphi hP hp
  apply hmain.trans
  apply (mul_le_mul_of_nonneg_left hbudget (show 0 ≤ C*(1+32/‖a+b‖^2)*T^(eps-s)*P by positivity)).trans
  calc
    _ = (10*C*(1+32/‖a+b‖^2)*P*PRZZOptimalPowers.target N T)*
        (T^(eps-s+1/2)*(Real.log T)^(2*PRZZGCoefficient.degree js)) := by
      rw [← hpw]; ring
    _ ≤ (10*C*(1+32/‖a+b‖^2)*P*PRZZOptimalPowers.target N T)*(D*T^delta) :=
      mul_le_mul_of_nonneg_left (hloss T (by linarith)) (by positivity)
    _ = _ := by ring

#print axioms phase_norm
#print axioms phase_integral
#print axioms summand
#print axioms mean_nonneg
#print axioms replacement_mean
#print axioms phase_pair
#print axioms exponential_gram
#print axioms exponential_mean_bound
#print axioms polynomial_expansion
#print axioms log_gap
#print axioms polynomial_mean
#print axioms normalized_norm
#print axioms bounded_mean
#print axioms source_mean
#print axioms replacement_source
#print axioms mean_scale_target
#print axioms replacement_target
end XiPrime8845.PRZZMeanSquare
