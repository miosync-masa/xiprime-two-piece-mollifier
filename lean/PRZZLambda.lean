import FengArithmetic

/-! L2: finite generalized von Mangoldt algebra in PRZZ, arXiv:1802.10521v3,
Section 4, printed p. 19. No analytic estimate is assumed here.
`logPower` is a POINTWISE power, whereas multiplication of arithmetic
functions is Dirichlet convolution. In particular Lambda_k is not Lambda^k.
-/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction
namespace XiPrime8845.PRZZLambda
open PRZZ FengArithmetic
set_option maxHeartbeats 1000000

def logPower (k : ℕ) : ArithmeticFunction ℝ := ArithmeticFunction.log.ppow k
def generalizedLambda (k : ℕ) : ArithmeticFunction ℝ := muReal * logPower k

theorem logPower_apply (k n : ℕ) (hn : n ≠ 0) :
    logPower k n = Real.log n ^ k := by
  cases k with
  | zero => simp [logPower, ppow_zero, natCoe_apply, zeta_apply, hn]
  | succ k => simp [logPower, ppow_apply (Nat.succ_pos k), log_apply]

theorem logWeight_logPower (k : ℕ) : logWeight (logPower k) = logPower (k+1) := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  · simp only [logWeight_apply, logPower_apply _ _ hn, pow_succ]; ring

theorem generalizedLambda_zero : generalizedLambda 0 = 1 := by
  change muReal * logPower 0 = 1
  rw [logPower, ppow_zero]
  exact coe_moebius_mul_coe_zeta

theorem generalizedLambda_one : generalizedLambda 1 = vonMangoldt := by
  change muReal * logPower 1 = vonMangoldt
  rw [logPower, ArithmeticFunction.ppow_one]
  exact moebius_mul_log_eq_vonMangoldt

/-- PRZZ p. 19 recurrence, proved from the convolution derivation. -/
theorem generalizedLambda_succ (k : ℕ) :
    generalizedLambda (k+1) = logWeight (generalizedLambda k) +
      vonMangoldt * generalizedLambda k := by
  simp only [generalizedLambda, logWeight_mul, logWeight_mu, logWeight_logPower]
  ring

def weightedLambda (j : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n ^ j * vonMangoldt n, by simp⟩

@[simp] theorem weightedLambda_zero : weightedLambda 0 = vonMangoldt := by
  ext n; simp [weightedLambda]

theorem logWeight_weightedLambda (j : ℕ) :
    logWeight (weightedLambda j) = weightedLambda (j+1) := by
  ext n
  change Real.log n * (Real.log n ^ j * vonMangoldt n) =
    Real.log n ^ (j+1) * vonMangoldt n
  ring

def monomial (js : List ℕ) : ArithmeticFunction ℝ := (js.map weightedLambda).prod
def evaluate (ts : List (List ℕ)) : ArithmeticFunction ℝ := (ts.map monomial).sum

/-- Repeated terms encode integer coefficients, with no existential choice. -/
def differentiate : List ℕ → List (List ℕ)
  | [] => []
  | j::js => ((j+1)::js)::(differentiate js).map (List.cons j)

def terms : ℕ → List (List ℕ)
  | 0 => [[]]
  | k+1 => (terms k).flatMap differentiate ++ (terms k).map (List.cons 0)

theorem evaluate_cons_map (j : ℕ) (ts : List (List ℕ)) :
    evaluate (ts.map (List.cons j)) = weightedLambda j * evaluate ts := by
  induction ts with
  | nil => simp [evaluate]
  | cons t ts ih =>
    change weightedLambda j * monomial t + evaluate (ts.map (List.cons j)) =
      weightedLambda j * (monomial t + evaluate ts)
    rw [ih, mul_add]

theorem logWeight_one : logWeight (1 : ArithmeticFunction ℝ) = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [logWeight_apply, one_apply, hn]

theorem logWeight_add (f g : ArithmeticFunction ℝ) :
    logWeight (f+g) = logWeight f + logWeight g := by
  ext n; simp [logWeight_apply, mul_add]

theorem evaluate_differentiate (js : List ℕ) :
    evaluate (differentiate js) = logWeight (monomial js) := by
  induction js with
  | nil => simp [differentiate, evaluate, monomial, logWeight_one]
  | cons j js ih =>
    change weightedLambda (j+1)*monomial js +
      evaluate ((differentiate js).map (List.cons j)) =
      logWeight (weightedLambda j * monomial js)
    rw [evaluate_cons_map, ih, logWeight_mul, logWeight_weightedLambda]

theorem evaluate_flatMap (ts : List (List ℕ)) :
    evaluate (ts.flatMap differentiate) = logWeight (evaluate ts) := by
  induction ts with
  | nil => ext n; simp [evaluate, logWeight_apply]
  | cons t ts ih =>
    simp only [List.flatMap_cons, evaluate, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at *
    rw [← evaluate, evaluate_differentiate, ih, logWeight_add]

/-- Explicit finite sum of convolutions of log^j Lambda, as in PRZZ p. 19. -/
theorem generalizedLambda_decomposition (k : ℕ) : generalizedLambda k = evaluate (terms k) := by
  induction k with
  | zero => simp [generalizedLambda_zero, terms, evaluate, monomial]
  | succ k ih =>
    rw [generalizedLambda_succ, ih]
    simp only [terms, evaluate, List.map_append, List.sum_append]
    change _ = evaluate ((terms k).flatMap differentiate) + evaluate ((terms k).map (List.cons 0))
    rw [evaluate_flatMap, evaluate_cons_map, weightedLambda_zero]
    rfl

theorem generalizedLambda_two :
    generalizedLambda 2 = weightedLambda 1 + vonMangoldt * vonMangoldt := by
  rw [generalizedLambda_succ 1, generalizedLambda_one]
  rw [← weightedLambda_zero, logWeight_weightedLambda]

#print axioms generalizedLambda_succ
#print axioms generalizedLambda_decomposition
#print axioms generalizedLambda_two
end XiPrime8845.PRZZLambda
