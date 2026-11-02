import PRZZActualCasePowers
import PRZZSourceWOuter

/-! Actual Gaussian outer mass paired with the literal three-case row
budget before summation. Local frequency and shift separation are explicit;
this does not yet identify the integral of every signed row with this box. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.PRZZActualRowOuter
open PRZZActualCaseSum PRZZOptimalPowers PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem mass_row_bound (Cs Ci Cg Cd Cr Cp Cv eps eta T A lam M S r L : ℝ)
    (N d K j l : ℕ) (ks : List ℕ) (alpha beta : ℂ)
    (hCs : 0 ≤ Cs) (hCi : 0 ≤ Ci) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hCr : 0 ≤ Cr) (hCp : 0 ≤ Cp) (hCv : 0 ≤ Cv)
    (hN : 1 ≤ (N:ℝ)) (hNT : (N:ℝ) ≤ T) (hd : 0 < d) (hA : 0 ≤ A)
    (hl : 1 ≤ lam) (hj : (2:ℝ)^j ≤ N) (hlN : (2:ℝ)^l ≤ N)
    (hM : 0 < M) (hS : 0 ≤ S) (hr : 0 < r) (hL : 0 ≤ L)
    (hlog : 1 ≤ Real.log T) (hsep : r ≤ ‖alpha+beta‖)
    (hscale : |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T)
    (hshift : |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T)
    (hfreq : A ≤ lam*(((2:ℝ)^j/2^((ks.length+1)*(2*K)))*(2:ℝ)^l/T)) :
    let c : ℝ := 2^((ks.length+1)*(2*K))
    let X : ℝ := (2:ℝ)^j/c
    let V : ℝ := (2:ℝ)^l
    let I := Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps
    let J := PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 *((2*c)*(2*c^2)^2)
    let Cw := 24*((1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*Real.exp ((L+Real.log 4)*S))
    (∫ p, ‖common d T M X V (sourceW ((alpha+beta)/(Real.log T:ℂ)))
      ((alpha+beta)/(Real.log T:ℂ)) p‖)*
      (smallBudget Cs T A eta l+largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks) ≤
        Cw*(2*Cs*T^eta*A^eta+11*I+22*J)*lam*target N T/d := by
  dsimp only
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  have hm := PRZZSourceWOuter.actual_mass d T M
    ((2:ℝ)^j/2^((ks.length+1)*(2*K))) ((2:ℝ)^l) L S r alpha beta
    hd hT hM (by positivity) (by positivity) hlog hL hS hr hsep hscale hshift
  have hb := PRZZActualCasePowers.row_normalized Cs Ci Cg Cd Cr Cp Cv eps eta T A d lam
    N K j l ks hCs hCi hCg hCd hCr hCp hCv hN hNT (by exact_mod_cast hd) hA hl hj hlN hfreq
  dsimp only at hb
  have hnlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith)
  have hbudget : 0 ≤ smallBudget Cs T A eta l+
      largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks := by
    unfold smallBudget largeBudget PRZZCommonCellBound.budget
      PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  have hfirst := mul_le_mul_of_nonneg_right hm hbudget
  have hsecond := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 24*((1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*Real.exp ((L+Real.log 4)*S)) by positivity)
  exact (hfirst.trans_eq (by ring)).trans (hsecond.trans_eq (by ring))

#print axioms mass_row_bound
end XiPrime8845.PRZZActualRowOuter
