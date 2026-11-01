import PRZZFullHeathBrown
import PRZZNuBounds
import PRZZGAbsorption

/-! Uniform subpower envelopes for arbitrary groups of log-weighted
Heath-Brown atoms. Constants precede every short Mobius cutoff and every
coordinate mask. The degree list is fixed; balancing the groups is separate. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZGroupBounds
open PRZZ PRZZHeathBrown PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

inductive Atom where
  | mu (y : ℕ)
  | zeta
  | log
  | restrict (a : Atom) (s : Set ℕ)

def atom : Atom → ArithmeticFunction ℝ
  | .mu y => truncatedMu y
  | .zeta => ζ
  | .log => ArithmeticFunction.log
  | .restrict a s => by
      classical
      exact ⟨fun n => if n ∈ s then atom a n else 0, by simp⟩

theorem atom_weight_bound (J : ℕ) (a : Atom) (n : ℕ) (hn : 0 < n) :
    |weight J (atom a) n| ≤ (Real.log n)^J+(Real.log n)^(J+1) := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  classical
  induction a with
  | mu y =>
    have hm : |truncatedMu y n| ≤ 1 := by
      change |if n ≤ y then muReal n else 0| ≤ 1
      split_ifs <;> simp_all [abs_muReal_le_one]
    rw [weight_apply,abs_mul,abs_of_nonneg (pow_nonneg hl _)]
    exact (mul_le_mul_of_nonneg_left hm (pow_nonneg hl _)).trans (by nlinarith [pow_nonneg hl (J+1)])
  | zeta => simp [atom,weight_apply,ArithmeticFunction.zeta_apply,hn.ne',
      abs_of_nonneg (pow_nonneg hl J),pow_nonneg hl (J+1)]
  | log =>
    change |Real.log n^J*Real.log n| ≤ _
    rw [← pow_succ,abs_of_nonneg (pow_nonneg hl _)]
    exact le_add_of_nonneg_left (pow_nonneg hl J)
  | restrict a s ih =>
    change |Real.log n^J*(if n ∈ s then atom a n else 0)| ≤ _
    split_ifs with hs
    · exact ih
    · simp only [mul_zero,abs_zero]
      positivity

theorem atom_subpower (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a n, 0 < n → |weight J (atom a) n| ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hc⟩ := PRZZGAbsorption.log_pow_bound J ε hε
  obtain ⟨D,hD,hd⟩ := PRZZGAbsorption.log_pow_bound (J+1) ε hε
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro a n hn
  exact (atom_weight_bound J a n hn).trans ((add_le_add
    (hc n (by exact_mod_cast hn)) (hd n (by exact_mod_cast hn))).trans_eq (by ring))

/-- Divisor counting supplies the convolution loss, uniformly in f and g. -/
theorem convolution_bound (ε C D K : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 < n → |f n| ≤ C*(n:ℝ)^ε)
    (hg : ∀ n, 0 < n → |g n| ≤ D*(n:ℝ)^ε)
    (hK : ∀ n : ℕ, 0 < n → (n.divisors.card:ℝ) ≤ K*(n:ℝ)^ε)
    (n : ℕ) (hn : 0 < n) : |(f*g) n| ≤ C*D*K*(n:ℝ)^(3*ε) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have bound (a : ℕ) (ha : 0 < a) (han : a ≤ n) : (a:ℝ)^ε ≤ (n:ℝ)^ε :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast han) hε
  rw [mul_apply,Nat.sum_divisorsAntidiagonal' (fun x y => f x*g y)]
  calc
    _ ≤ ∑ d ∈ n.divisors, |f (n/d)*g d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, (C*(n:ℝ)^ε)*(D*(n:ℝ)^ε) := by
      apply sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdn := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)
      rw [abs_mul]
      exact mul_le_mul
        ((hf _ (Nat.div_pos hdn hd0)).trans (mul_le_mul_of_nonneg_left
          (bound _ (Nat.div_pos hdn hd0) (Nat.div_le_self _ _)) hC))
        ((hg d hd0).trans (mul_le_mul_of_nonneg_left (bound d hd0 hdn) hD))
        (abs_nonneg _) (by positivity)
    _ = (n.divisors.card:ℝ)*((C*(n:ℝ)^ε)*(D*(n:ℝ)^ε)) := by simp
    _ ≤ (K*(n:ℝ)^ε)*((C*(n:ℝ)^ε)*(D*(n:ℝ)^ε)) :=
      mul_le_mul_of_nonneg_right (hK n hn) (by positivity)
    _ = _ := by
      rw [show (3*ε) = ε+ε+ε by ring,Real.rpow_add hnR,Real.rpow_add hnR]
      ring

def group : List ℕ → (ℕ → Atom) → ArithmeticFunction ℝ
  | [], _ => 1
  | J::js, a => weight J (atom (a 0))*group js (fun i => a (i+1))

/-- One constant works for every choice of HB atoms and every mu cutoff. -/
theorem group_subpower (js : List ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a n, 0 < n → |group js a n| ≤ C*(n:ℝ)^ε := by
  induction js generalizing ε with
  | nil =>
    refine ⟨1,by norm_num,?_⟩
    intro a n hn
    by_cases h : n=1
    · simp [group,h]
    · simp [group,one_apply,h,Real.rpow_nonneg (by positivity : (0:ℝ)≤n)]
  | cons J js ih =>
    obtain ⟨C,hC,hc⟩ := atom_subpower J (ε/3) (by positivity)
    obtain ⟨D,hD,hd⟩ := ih (ε/3) (by positivity)
    obtain ⟨K,hK,hk⟩ := PRZZNuBounds.divisors_subpower (ε/3) (by positivity)
    refine ⟨C*D*K,by positivity,?_⟩
    intro a n hn
    simpa only [group,show 3*(ε/3)=ε by ring] using
      convolution_bound (ε/3) C D K (by positivity) hC.le hD.le
        (weight J (atom (a 0))) (group js (fun i => a (i+1))) (hc (a 0)) (hd _) hk n hn

/-- Coordinate zero extension and unit-modulus twists preserve the envelope.
This supplies the complex coefficient bounds used by DI. -/
theorem masked_twisted_group (js : List ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → Atom) (s : Set ℕ) (w : ℕ → ℂ),
      (∀ n, ‖w n‖ ≤ 1) → ∀ n, 0 < n →
        ‖s.indicator (fun n => (group js a n:ℂ)*w n) n‖ ≤ C*(n:ℝ)^ε := by
  classical
  obtain ⟨C,hC,h⟩ := group_subpower js ε hε
  refine ⟨C,hC,?_⟩
  intro a s w hw n hn
  by_cases hs : n ∈ s
  · simp only [Set.indicator_of_mem hs,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw n) (abs_nonneg _)).trans (by simpa using h a n hn)
  · simp only [Set.indicator_of_notMem hs,norm_zero]
    positivity

#print axioms atom_weight_bound
#print axioms atom_subpower
#print axioms convolution_bound
#print axioms group_subpower
#print axioms masked_twisted_group

/-- The constant precedes the rectangle size as well as its masks and twists. -/
theorem rectangle_envelope (js : List ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → Atom) (s : Set ℕ) (w : ℕ → ℂ),
      (∀ n, ‖w n‖ ≤ 1) → ∀ X : ℝ, 1 ≤ X → ∀ n ∈ Icc 1 ⌊X⌋₊,
        ‖s.indicator (fun n => (group js a n:ℂ)*w n) n‖ ≤ C*X^ε := by
  obtain ⟨C,hC,h⟩ := masked_twisted_group js ε hε
  refine ⟨C,hC,?_⟩
  intro a s w hw X hX n hn
  exact (h a s w hw n (mem_Icc.mp hn).1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity)
      ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))) hε.le) hC.le)

#print axioms rectangle_envelope
end XiPrime8845.PRZZGroupBounds
