import PRZZResidualCoprime
import PRZZWeightedDI

/-! Exact weighted residual to a coprime-masked DI rectangle. Product
weights are not separated for free: the norm estimate charges variation. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZResidualWeighted
open PRZZKloostermanInputs PRZZResidualCoprime PRZZGroupedConvolution PRZZWeightedDI
set_option maxHeartbeats 3000000

def grouped (N d : ℕ) (V A : ℝ) (h : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) : ℂ :=
  ∑ c ∈ (Icc 1 ⌊V⌋₊).filter (fun c => c.Coprime h), ∑ a ∈ Icc 1 ⌊A⌋₊,
    ∑ n ∈ Icc 1 N, if d.Coprime n ∧ n.Coprime c then
      w n*(r c*nu a*e ((a:ℝ)*inverseResidue c (h*n)/c)*(f*g) n) else 0

theorem grouped_eq (N d : ℕ) (V A : ℝ) (h : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) :
    grouped N d V A h r nu f g w =
      weighted N V N A N h r (restrict d g) nu (restrict d f) w := by
  have he : grouped N d V A h r nu f g w =
      ∑ c ∈ (Icc 1 ⌊V⌋₊).filter (fun c => c.Coprime h), ∑ a ∈ Icc 1 ⌊A⌋₊,
        ∑ n ∈ Icc 1 N,
          (if n.Coprime c then w n*(r c*nu a*e ((a:ℝ)*inverseResidue c (h*n)/c)) else 0)*
            (restrict d f*restrict d g) n := by
    simp_rw [← restrict_mul]
    unfold grouped
    apply sum_congr rfl; intro c hc
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro n hn
    change (if d.Coprime n ∧ n.Coprime c then _ else 0) =
      (if n.Coprime c then _ else 0)*(if d.Coprime n then (f*g) n else 0)
    split_ifs <;> simp_all [mul_assoc]
  rw [he]
  simp_rw [weighted_convolution]
  unfold weighted
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  split_ifs with hr
  · simp only [Nat.coprime_mul_iff_right]
    conv_lhs => enter [2,a]; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    by_cases hmc : m.Coprime c
    · rw [if_pos ⟨hr,hmc.symm⟩]
      simp_rw [Nat.coprime_mul_iff_left]
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro n hn
      by_cases hnc : n.Coprime c <;> by_cases hcut : n*m ≤ N <;>
        simp [hnc,hmc,hcut,Nat.coprime_mul_iff_left,mul_assoc] <;> ring
      rw [if_pos ⟨hnc,hmc⟩,if_pos hnc]
    · simp [Nat.coprime_mul_iff_left,hmc,show ¬c.Coprime m from fun h => hmc h.symm]
  · simp [hr,Nat.coprime_mul_iff_right]

theorem weighted_shrink (N E F : ℕ) (hE : E ≤ N) (hF : F ≤ N)
    (V A : ℝ) (h : ℕ) (r beta nu alpha w : ℕ → ℂ)
    (ha : ∀ n, E < n → alpha n = 0) (hb : ∀ n, F < n → beta n = 0) :
    weighted N V N A N h r beta nu alpha w = weighted N V F A E h r beta nu alpha w := by
  unfold weighted
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  trans ∑ f ∈ Icc 1 F, if c.Coprime (h*f) then
    ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ e ∈ Icc 1 N, if e.Coprime c then
      if e*f ≤ N then w (e*f)*(r c*beta f*(nu a*alpha e)*
        PRZZKloostermanInputs.e ((a:ℝ)*inverseResidue c (h*e*f)/c)) else 0 else 0 else 0
  · symm
    apply sum_subset (Icc_subset_Icc le_rfl hF)
    intro f hf hnot
    have hz := hb f (by have := (mem_Icc.mp hf).1; simpa [mem_Icc,this] using hnot)
    simp [hz]
  · apply sum_congr rfl; intro f hf
    split_ifs with hc
    · apply sum_congr rfl; intro a ha'
      symm
      apply sum_subset (Icc_subset_Icc le_rfl hE)
      intro e he hnot
      have hz := ha e (by have := (mem_Icc.mp he).1; simpa [mem_Icc,this] using hnot)
      simp [hz]
    · rfl

theorem grouped_seven (hDI : DeshouillersIwaniecLemma1) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N d E F : ℕ, 1 ≤ E → E ≤ N → 1 ≤ F → F ≤ N →
      ∀ V A : ℝ, 1 ≤ V → 1 ≤ A → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ (r nu w : ℕ → ℂ) (alpha beta : ArithmeticFunction ℂ),
      (∀ n, E < n → alpha n = 0) → (∀ n, F < n → beta n = 0) →
      (∀ c ∈ Icc 1 ⌊V⌋₊, ‖r c‖ ≤ R) → (∀ f ∈ Icc 1 F, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) → (∀ e ∈ Icc 1 E, ‖alpha e‖ ≤ Q) →
      ‖grouped N d V A h r nu alpha beta w‖ ≤
        ((1+2*Real.log ((F:ℝ)+1))*(R*S*(P*Q)*K*
          ((V*F*A*E)^eps*PRZZDISeven.seven h E A ((E:ℝ)*F) V)))*
            PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨K,hK,hb⟩ := weighted_seven hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N d E F hE hEN hF hFN V A hV hA h hh R S P Q hR hS hP hQ r nu w alpha beta
    hsa hsb hr hf hn he
  rw [grouped_eq,weighted_shrink N E F hEN hFN V A h r (restrict d beta) nu (restrict d alpha) w
    (fun n hh => by simp [PRZZResidualCoprime.restrict,hsa n hh])
    (fun n hh => by simp [PRZZResidualCoprime.restrict,hsb n hh])]
  simpa only [Nat.floor_natCast] using hb N V F A E hV (by exact_mod_cast hF) hA
    (by exact_mod_cast hE) h hh R S P Q hR hS hP hQ r (restrict d beta) nu (restrict d alpha) w hr
    (fun n hn' => (restrict_norm d n beta).trans (hf n (by simpa only [Nat.floor_natCast] using hn')))
    hn (fun n hn' => (restrict_norm d n alpha).trans (he n (by simpa only [Nat.floor_natCast] using hn')))

#print axioms grouped_eq
#print axioms weighted_shrink
#print axioms grouped_seven
end XiPrime8845.PRZZResidualWeighted
