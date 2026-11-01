import PRZZConvolutionSplit

/-! Full finite allocation of every labelled weighted Lambda factor.
Lists retain repeated terms (and hence their multiplicities). The identity
is for the original Mobius convolution at coprime arguments. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZCoefficientSeparation
open PRZZGCoefficient PRZZLambda PRZZConvolutionSplit PRZZCoprimeAllocation
set_option maxHeartbeats 2000000

def allocations : List ℕ → List (List ℕ × List ℕ)
  | [] => [([],[])]
  | j::js => (allocations js).map (fun t => (j::t.1,t.2)) ++
      (allocations js).map (fun t => (t.1,j::t.2))

def evaluate (ts : List (List ℕ × List ℕ)) (m n : ℕ) : ℝ :=
  (ts.map (fun t => coefficient t.1 m*coefficient t.2 n)).sum

private theorem left_step (ts : List (List ℕ × List ℕ)) (j m n : ℕ) :
    (∑ a ∈ m.divisorsAntidiagonal, evaluate ts a.1 n*weightedLambda j a.2) =
      evaluate (ts.map (fun t => (j::t.1,t.2))) m n := by
  induction ts with
  | nil => simp [evaluate]
  | cons t ts ih =>
    simp only [evaluate,List.map_cons,List.sum_cons] at ih ⊢
    simp only [add_mul,sum_add_distrib]
    rw [ih]
    congr 1
    rw [coefficient,mul_apply,sum_mul]
    apply sum_congr rfl
    intros; ring

private theorem right_step (ts : List (List ℕ × List ℕ)) (j m n : ℕ) :
    (∑ b ∈ n.divisorsAntidiagonal, evaluate ts m b.1*weightedLambda j b.2) =
      evaluate (ts.map (fun t => (t.1,j::t.2))) m n := by
  induction ts with
  | nil => simp [evaluate]
  | cons t ts ih =>
    simp only [evaluate,List.map_cons,List.sum_cons] at ih ⊢
    simp only [add_mul,sum_add_distrib]
    rw [ih]
    congr 1
    rw [coefficient,mul_apply,mul_sum]
    apply sum_congr rfl
    intros; ring

theorem coefficient_separation (js : List ℕ) (m n : ℕ) (hc : m.Coprime n) :
    coefficient js (m*n) = evaluate (allocations js) m n := by
  induction js generalizing m n with
  | nil => simpa [allocations,evaluate,coefficient] using mu_mul_coprime m n hc
  | cons j js ih =>
    rw [coefficient_cons_split j js m n hc]
    have hl : (∑ a ∈ m.divisorsAntidiagonal, coefficient js (a.1*n)*weightedLambda j a.2) =
        ∑ a ∈ m.divisorsAntidiagonal, evaluate (allocations js) a.1 n*weightedLambda j a.2 := by
      apply sum_congr rfl
      intro a ha
      rw [ih a.1 n (by
        have hh := (Nat.mem_divisorsAntidiagonal.mp ha).1
        rw [← hh] at hc
        exact hc.coprime_mul_right)]
    have hr : (∑ b ∈ n.divisorsAntidiagonal, coefficient js (m*b.1)*weightedLambda j b.2) =
        ∑ b ∈ n.divisorsAntidiagonal, evaluate (allocations js) m b.1*weightedLambda j b.2 := by
      apply sum_congr rfl
      intro b hb
      rw [ih m b.1 (by
        have hh := (Nat.mem_divisorsAntidiagonal.mp hb).1
        rw [← hh] at hc
        exact hc.coprime_mul_right_right)]
    rw [hl,hr,left_step,right_step]
    simp only [allocations,evaluate,List.map_append,List.sum_append]

/-- The source argument d*h*n1 is split without replacing its coefficient. -/
theorem source_coefficient_separation (js : List ℕ) (d h n1 : ℕ)
    (hc : (d*h).Coprime n1) :
    coefficient js (d*h*n1) =
      ((allocations js).map (fun t => coefficient t.1 (d*h)*coefficient t.2 n1)).sum :=
  coefficient_separation js (d*h) n1 hc

theorem allocations_length (js : List ℕ) : (allocations js).length = 2^js.length := by
  induction js with
  | nil => simp [allocations]
  | cons j js ih => simp [allocations,ih,pow_succ]; omega

#print axioms coefficient_separation
#print axioms source_coefficient_separation
#print axioms allocations_length
end XiPrime8845.PRZZCoefficientSeparation
