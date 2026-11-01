import PRZZLambda
import SupportTail
import PRZZDISeven

/-! The separated arithmetic coefficient in PRZZ p.20. Absolute convolution
bounds use sum_{d|n} Lambda(d)=log n, without squarefree truncation.
The supported-divisor average and the full source separation remain separate. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZGCoefficient
open PRZZ PRZZLambda
set_option maxHeartbeats 2000000

def coefficient : List ℕ → ArithmeticFunction ℝ
  | [] => muReal
  | j::js => coefficient js * weightedLambda j

def degree (js : List ℕ) : ℕ := js.sum+js.length

theorem coefficient_eq (js : List ℕ) : coefficient js = muReal * monomial js := by
  induction js with
  | nil => simp [coefficient,monomial]
  | cons j js ih => simp only [coefficient,monomial,List.map_cons,List.prod_cons] at *; rw [ih]; ring

theorem coefficient_bound (js : List ℕ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n → |coefficient js m| ≤ (Real.log n)^degree js := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn'
  induction js with
  | nil => intro m hm hmn; simpa [coefficient,degree] using abs_muReal_le_one m
  | cons j js ih =>
    intro m hm hmn
    rw [coefficient,ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (fun x y => coefficient js x * weightedLambda j y)]
    have hdlog (d : ℕ) (hd : d ∈ m.divisors) : Real.log d ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors hd)
        (by exact_mod_cast (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hmn)
    calc
      _ ≤ ∑ d ∈ m.divisors, |coefficient js (m/d)*weightedLambda j d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ m.divisors, (Real.log n)^(degree js+j)*vonMangoldt d := by
        apply sum_le_sum
        intro d hd
        have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
        have hld : 0 ≤ Real.log d := Real.log_nonneg hd1
        have hc := ih (m/d) (Nat.div_pos
          (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd))
          (Nat.pos_of_mem_divisors hd)) ((Nat.div_le_self _ _).trans hmn)
        change |coefficient js (m/d)*(Real.log d^j*vonMangoldt d)| ≤ _
        rw [abs_mul,abs_of_nonneg (mul_nonneg (pow_nonneg hld _) vonMangoldt_nonneg),pow_add]
        have hp := pow_le_pow_left₀ hld (hdlog d hd) j
        exact (mul_le_mul hc (mul_le_mul_of_nonneg_right hp vonMangoldt_nonneg)
          (by positivity) (pow_nonneg hl _)).trans_eq (by ring)
      _ = (Real.log n)^(degree js+j)*Real.log m := by rw [← mul_sum,vonMangoldt_sum]
      _ ≤ (Real.log n)^(degree js+j)*Real.log n := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl _)
        exact Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmn)
      _ = _ := by
        rw [← pow_succ]
        congr 1
        simp [degree]
        omega

#print axioms coefficient_eq
#print axioms coefficient_bound

/-- A separated G coefficient before the h^(alpha+w) denominator.
sigma represents sigma_0-1/2; the list is the subset allocated to d*h. -/
def sourceG (js : List ℕ) (k : ℕ) (sigma : ℝ) (d h : ℕ) : ℝ :=
  (h:ℝ)^sigma*(Real.log h)^k*coefficient js (d*h)

theorem sourceG_bound (js : List ℕ) (k : ℕ) (sigma : ℝ) (d h n : ℕ)
    (hσ : sigma ≤ 0) (hd : 1 ≤ d) (hh : 1 ≤ h) (hn : d*h ≤ n) :
    |sourceG js k sigma d h| ≤ (Real.log n)^(k+degree js) := by
  have hdh : 1 ≤ d*h := by nlinarith
  have hhn : h ≤ n := (Nat.le_mul_of_pos_left h (by omega)).trans hn
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hdh.trans hn)
  have hlh : 0 ≤ Real.log h := Real.log_nonneg hh'
  have hp : (h:ℝ)^sigma ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hh' hσ
  have hl : (Real.log h)^k ≤ (Real.log n)^k :=
    pow_le_pow_left₀ hlh (Real.log_le_log (by exact_mod_cast (show 0 < h by omega))
      (by exact_mod_cast hhn)) k
  unfold sourceG
  rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    abs_of_nonneg (pow_nonneg hlh _),pow_add]
  exact mul_le_mul ((mul_le_mul hp hl (pow_nonneg hlh _) (by norm_num)).trans_eq (one_mul _))
    (coefficient_bound js n (hdh.trans hn) (d*h) hdh hn) (abs_nonneg _) (pow_nonneg hln _)

/-- Finite h-average with an explicit Euler product. This does not yet
replace that d-dependent product by a uniform d^epsilon estimate. -/
theorem sourceG_average (js : List ℕ) (k : ℕ) (sigma ε : ℝ) (d n : ℕ)
    (hσ : sigma ≤ 0) (hε : 0 < ε) (hd : 1 ≤ d) (hn : 1 ≤ n) (s : Finset ℕ)
    (hs : ∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) :
    (∑ h ∈ s, |sourceG js k sigma d h|/(h:ℝ)^ε) ≤
      (Real.log n)^(k+degree js)*SupportTail.eulerMass d (1-ε) := by
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc
    _ ≤ ∑ h ∈ s, (Real.log n)^(k+degree js)*(h:ℝ)^(-ε) := by
      apply sum_le_sum
      intro h hh
      rw [Real.rpow_neg (by positivity),← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (sourceG_bound js k sigma d h n hσ hd (hs h hh).1 (hs h hh).2.1)
        (Real.rpow_nonneg (by positivity) _)
    _ = (Real.log n)^(k+degree js)*(∑ h ∈ s, (h:ℝ)^(-ε)) := by rw [mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hln _)
      have hb := SupportTail.supported_mass_le d (by omega) s (1-ε) (by linarith)
        (fun h hh => (hs h hh).2.2)
      simpa only [show 1-ε-1 = -ε by ring] using hb

#print axioms sourceG_bound
#print axioms sourceG_average

/-- The seven balanced terms can now be summed with the concrete separated
G coefficient. The remaining Euler factor is displayed, not assumed small. -/
theorem sourceG_seven_average (js : List ℕ) (k : ℕ) (sigma : ℝ) (d n : ℕ)
    (hσ : sigma ≤ 0) (hd : 1 ≤ d) (hn : 1 ≤ n) (s : Finset ℕ)
    (X A V : ℝ) (E : ℕ → ℝ) (hX : 0 < X) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hs : ∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h)
    (hE : ∀ h ∈ s, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) :
    (∑ h ∈ s, |sourceG js k sigma d h| * PRZZDISeven.seven h (E h) A (X/h) V) ≤
      PRZZDISeven.envelope X A V*((Real.log n)^(k+degree js)*SupportTail.eulerMass d (5/8)) := by
  apply (PRZZDISeven.finite_h_bound s (fun h => |sourceG js k sigma d h|) E X A V
    hX hA hV (fun h hh => ⟨(hs h hh).1,abs_nonneg _,hE h hh⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold PRZZDISeven.envelope; positivity)
  have hb := sourceG_average js k sigma (3/8) d n hσ (by norm_num) hd hn s hs
  norm_num at hb
  exact hb

#print axioms sourceG_seven_average
end XiPrime8845.PRZZGCoefficient
