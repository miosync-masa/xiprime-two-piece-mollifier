import PRZZThreeCaseLoss
import PRZZSourceCutoffs

/-! The precise price of using a frequency envelope larger than the local
product scale. This price cannot be dropped when a Fourier cutoff grows.
The row theorem includes small scale, Type I and DI; it does not assert
that the global signed-grid envelope preserves the local outer masses. -/
noncomputable section
namespace XiPrime8845.PRZZLocalFrequencyLoss
set_option maxHeartbeats 3000000

def cost (A T X V : ℝ) : ℝ := max 1 (A*T/(X*V))

theorem cost_ge_one (A T X V : ℝ) : 1 ≤ cost A T X V := le_max_left _ _

theorem frequency_le (A T X V : ℝ) (hT : 0 < T) (hX : 0 < X) (hV : 0 < V) :
    A ≤ cost A T X V*(X*V/T) := by
  have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (A*T/(X*V)))
    (show 0 ≤ X*V/T by positivity)
  have he : A*T/(X*V)*(X*V/T) = A := by field_simp
  rw [he] at hh
  exact hh

/-- Necessary and sufficient local frequency condition, not an estimate
premise manufactured from arbitrary D,H. -/
theorem cost_le_iff (A T X V lam : ℝ) (hT : 0 < T) (hX : 0 < X) (hV : 0 < V)
    (hlam : 1 ≤ lam) :
    cost A T X V ≤ lam ↔ A ≤ lam*(X*V/T) := by
  unfold cost
  rw [max_le_iff]
  have hh : A*T/(X*V) ≤ lam ↔ A ≤ lam*(X*V/T) := by
    rw [div_le_iff₀ (mul_pos hX hV),
      show lam*(X*V/T) = lam*(X*V)/T by ring,le_div_iff₀ hT]
  exact ⟨fun h => hh.mp h.2,fun h => ⟨hlam,hh.mpr h⟩⟩

/-- The optimal N,T target with every excess-frequency loss exposed.
Constants precede the row indices and height. -/
theorem normalized_row_with_cost (Cs Ci Cg Cd Cr Cp Cv eps eta rho beta delta : ℝ)
    (K : ℕ) (ks : List ℕ)
    (hs : 0 ≤ Cs) (hi : 0 ≤ Ci) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd)
    (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ beta)
    (hmargin : (6+rho)*eta+(3+rho)*eps+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N j l : ℕ, ∀ T A d : ℝ,
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → d ≤ T →
      (2:ℝ)^j ≤ N → (2:ℝ)^l ≤ N →
      let X : ℝ := (2:ℝ)^j/2^((ks.length+1)*(2*K))
      let V : ℝ := (2:ℝ)^l
      d^eta*(N:ℝ)^beta*T^eta*(Real.log T)^2*
        (T/(d*X*V)*(PRZZActualCaseSum.smallBudget Cs T A eta l+
          PRZZActualCaseSum.largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks)) ≤
        C*T^delta*cost A T X V*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := PRZZThreeCaseLoss.normalized_row_absorbed
    Cs Ci Cg Cd Cr Cp Cv eps eta rho beta delta K ks
    hs hi hg hd hr hp hv he hn hrho hb hmargin
  refine ⟨C,hC,?_⟩
  intro N j l T A d hN hNT hlog hA hAT hd0 hdT hj hl
  dsimp only
  apply h N j l T A d _ hN hNT hlog hA hAT hd0 hdT (cost_ge_one _ _ _ _) hj hl
  exact frequency_le _ _ _ _ (by linarith) (by positivity) (by positivity)

/-- The local cost spends kappa of the height exponent. In particular,
cost <= 1 spends no additional height power. -/
theorem absorb_cost (C T delta kappa A X V U : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T) (hU : 0 ≤ U)
    (hcost : cost A T X V ≤ T^kappa) :
    C*T^delta*cost A T X V*U ≤ C*T^(delta+kappa)*U := by
  calc
    _ ≤ C*T^delta*T^kappa*U := by gcongr
    _ = _ := by rw [Real.rpow_add hT]; ring

/-- Concrete source cutoffs pay only eD+eH in the local frequency cost.
Both original cutoff witnesses are required, and empty index sets are
kept as the zero branch. This is not a claim for H=J+1. -/
theorem source_empty_or_cost (N d j l n m : ℕ) (T M Q1 Q2 eD eH c : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M)
    (hc : 1 ≤ c) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (he : 0 ≤ eD+eH)
    (hs1 : Function.support F1 ⊆ Set.Icc Q1 (2*Q1))
    (hs2 : Function.support F2 ⊆ Set.Icc Q2 (2*Q2))
    (hn : n ∈ PRZZDyadic.cell N j) (hm : m ∈ PRZZDyadic.cell N l)
    (hf1 : F1 ((d:ℝ)*n) ≠ 0) (hf2 : F2 ((d:ℝ)*m) ≠ 0) :
    PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T M Q1 eD)
      (PRZZSourceCutoffs.poissonCutoff d T M Q2 eH) = ∅ ∨
    cost (PRZZActualSignedBranches.frequencyBound d
      (PRZZSourceCutoffs.deltaCutoff T M Q1 eD)
      (PRZZSourceCutoffs.poissonCutoff d T M Q2 eH))
      T ((2:ℝ)^j/c) ((2:ℝ)^l) ≤ 8*c*T^(eD+eH) := by
  have ht : 0 < T := by linarith
  have hc0 : 0 < c := by linarith
  have htPow := Real.one_le_rpow hT he
  rcases PRZZSourceCutoffs.empty_or_frequency N d T M Q1 Q2 eD eH hd ht hM with hz | hh
  · exact Or.inl hz
  · apply Or.inr
    apply (cost_le_iff _ _ _ _ _ ht (by positivity) (by positivity) (by nlinarith)).mpr
    have hf := PRZZActualCasePowers.cutoff_frequency N d j l n m Q1 Q2 T
      (PRZZActualSignedBranches.frequencyBound d
        (PRZZSourceCutoffs.deltaCutoff T M Q1 eD)
        (PRZZSourceCutoffs.poissonCutoff d T M Q2 eH))
      (2*T^(eD+eH)) c F1 F2 hd ht hc0 hQ1 hQ2 (by positivity)
      hs1 hs2 hn hm hf1 hf2 hh.2
    convert hf using 1 <;> ring

/-- A fixed inflation is part of C, whereas kappa is explicitly spent
from the height exponent. -/
theorem absorb_scaled_cost (C c T delta kappa A X V U : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T) (hU : 0 ≤ U)
    (hcost : cost A T X V ≤ c*T^kappa) :
    C*T^delta*cost A T X V*U ≤ (C*c)*T^(delta+kappa)*U := by
  calc
    _ ≤ C*T^delta*(c*T^kappa)*U := by gcongr
    _ = _ := by rw [Real.rpow_add hT]; ring

/-- Even the small-scale summand of the current positive scalar envelope
is unbounded in J at fixed height. Hence an all-large-J upper bound from
that envelope cannot be made J-uniform by logarithmic absorption. -/
theorem small_budget_unbounded (Cs T eta : ℝ) (l m : ℕ)
    (hCs : 0 < Cs) (hT : 0 < T) (heta : 0 ≤ eta) (hm : 1 ≤ m)
    (B : ℝ) (J0 : ℕ) :
    ∃ J : ℕ, J0 ≤ J ∧ B <
      PRZZActualCaseSum.smallBudget Cs T ((m:ℝ)*((J:ℝ)+1)) eta l := by
  let b : ℝ := Cs*T^eta*(2:ℝ)^(l+1)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt (max (J0:ℝ) (B/b))
  have hj0 : J0 ≤ J := by exact_mod_cast (le_max_left _ _).trans hJ.le
  have hjb : B/b < (J:ℝ) := (le_max_right _ _).trans_lt hJ
  have hB : B < b*(J:ℝ) := by
    have hh := (div_lt_iff₀ hb).mp hjb
    nlinarith only [hh]
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hA : 1 ≤ (m:ℝ)*((J:ℝ)+1) := by nlinarith
  have hpow := Real.one_le_rpow hA heta
  have hlin : b*((J:ℝ)+1) ≤
      PRZZActualCaseSum.smallBudget Cs T ((m:ℝ)*((J:ℝ)+1)) eta l := by
    unfold PRZZActualCaseSum.smallBudget
    calc
      _ ≤ b*((m:ℝ)*((J:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith : (J:ℝ)+1 ≤ (m:ℝ)*((J:ℝ)+1)) hb.le
      _ ≤ b*(((m:ℝ)*((J:ℝ)+1))^eta*((m:ℝ)*((J:ℝ)+1))) := by
        apply mul_le_mul_of_nonneg_left _ hb.le
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (m:ℝ)*((J:ℝ)+1))
      _ = _ := by dsimp [b]; ring
  exact ⟨J,hj0,by linarith⟩

/-- Apply the obstruction to the very frequencyBound used in gridEnvelope.
The exceptional case ceil(D/d)=0 is explicitly excluded. -/
theorem actual_frequency_unbounded (Cs T eta D : ℝ) (d l : ℕ)
    (hCs : 0 < Cs) (hT : 0 < T) (heta : 0 ≤ eta)
    (hD : ⌈D/d⌉.natAbs ≠ 0) (B : ℝ) (J0 : ℕ) :
    ∃ J : ℕ, J0 ≤ J ∧ B < PRZZActualCaseSum.smallBudget Cs T
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1)) eta l := by
  obtain ⟨J,hj,hh⟩ := small_budget_unbounded Cs T eta l ⌈D/d⌉.natAbs
    hCs hT heta (by omega) B J0
  refine ⟨J,hj,?_⟩
  have hfloor : ⌊(J:ℝ)+1⌋₊ = J+1 := by
    apply (Nat.floor_eq_iff (by positivity : 0 ≤ (J:ℝ)+1)).mpr
    push_cast
    constructor <;> linarith
  simpa only [PRZZActualSignedBranches.frequencyBound,hfloor,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh

#print axioms cost_ge_one
#print axioms frequency_le
#print axioms cost_le_iff
#print axioms normalized_row_with_cost
#print axioms absorb_cost
#print axioms source_empty_or_cost
#print axioms absorb_scaled_cost
#print axioms small_budget_unbounded
#print axioms actual_frequency_unbounded
end XiPrime8845.PRZZLocalFrequencyLoss
