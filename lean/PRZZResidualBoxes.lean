import PRZZResidualWeighted

/-! Actual dyadic masks supply both group supports to the weighted DI
residual. Every factor-two inflation is retained. Choosing Type II groups
for all source branches is separate from these exact support suppliers. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZResidualBoxes
open PRZZDyadicSupport PRZZResidualWeighted PRZZResidualCoprime
set_option maxHeartbeats 2000000

def lower (fs : List (ArithmeticFunction ℂ × ℕ)) : ℕ := 2^(fs.map Prod.snd).sum
def upper (fs : List (ArithmeticFunction ℂ × ℕ)) : ℕ :=
  2^((fs.map Prod.snd).sum+fs.length)

theorem support (N : ℕ) (fs : List (ArithmeticFunction ℂ × ℕ)) :
    ∀ n, upper fs < n → dyadicGroup N fs n = 0 := by
  intro n hn
  by_contra hz
  exact (not_le_of_gt hn) (group_support N fs n hz).2

/-- Balancing the lower products gives the upper box with its precise
2^length inflation, rather than claiming the same upper bound. -/
theorem balanced_box (fs : List (ArithmeticFunction ℂ × ℕ)) (U W : ℝ)
    (hlo : W ≤ (lower fs:ℝ)) (hhi : (lower fs:ℝ) ≤ U/W) :
    W ≤ (upper fs:ℝ) ∧ (upper fs:ℝ) ≤ 2^fs.length*(U/W) := by
  have he : upper fs = 2^fs.length*lower fs := upper_box_factor fs
  rw [he,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hp : (1:ℝ) ≤ 2^fs.length := one_le_pow₀ (by norm_num)
  constructor
  · exact hlo.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hp)
  · exact mul_le_mul_of_nonneg_left hhi (by positivity)

theorem dyadic_eq (N d : ℕ) (left right : List (ArithmeticFunction ℂ × ℕ))
    (hE : upper left ≤ N) (hF : upper right ≤ N)
    (V A : ℝ) (h : ℕ) (r nu w : ℕ → ℂ) :
    grouped N d V A h r nu (dyadicGroup N left) (dyadicGroup N right) w =
      PRZZWeightedDI.weighted N V (upper right) A (upper left) h r
        (PRZZResidualCoprime.restrict d (dyadicGroup N right)) nu
        (PRZZResidualCoprime.restrict d (dyadicGroup N left)) w := by
  rw [grouped_eq]
  apply weighted_shrink N _ _ hE hF
  · intro n hn
    simp [PRZZResidualCoprime.restrict,support N left n hn]
  · intro n hn
    simp [PRZZResidualCoprime.restrict,support N right n hn]

/-- No support envelope is assumed: it comes from the finite dyadic
restrictions. Scalar coefficient and analytic variation costs remain visible. -/
theorem dyadic_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N d : ℕ,
      ∀ left right : List (ArithmeticFunction ℂ × ℕ),
      upper left ≤ N → upper right ≤ N →
      ∀ V A : ℝ, 1 ≤ V → 1 ≤ A → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r nu w : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊V⌋₊, ‖r c‖ ≤ R) →
      (∀ n ∈ Icc 1 (upper right), ‖dyadicGroup N right n‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) →
      (∀ n ∈ Icc 1 (upper left), ‖dyadicGroup N left n‖ ≤ Q) →
      ‖grouped N d V A h r nu (dyadicGroup N left) (dyadicGroup N right) w‖ ≤
        ((1+2*Real.log ((upper right:ℝ)+1))*(R*S*(P*Q)*K*
          ((V*upper right*A*upper left)^eps*PRZZDISeven.seven h (upper left) A
            ((upper left:ℝ)*upper right) V)))*PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨K,hK,hb⟩ := grouped_seven hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N d left right hE hF V A hV hA h hh R S P Q hR hS hP hQ r nu w hr hg hn hf
  exact hb N d (upper left) (upper right) (by unfold upper; exact Nat.succ_le_of_lt (by positivity)) hE
    (by unfold upper; exact Nat.succ_le_of_lt (by positivity)) hF V A hV hA h hh R S P Q hR hS hP hQ r nu w _ _
    (support N left) (support N right) hr hg hn hf

#print axioms support
#print axioms balanced_box
#print axioms dyadic_eq
#print axioms dyadic_seven
end XiPrime8845.PRZZResidualBoxes
