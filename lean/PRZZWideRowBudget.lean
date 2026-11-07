import PRZZNonemptyRowBudget

/-! Actual profile widths Q/2..3Q supply the row frequency scale.
The original local outer mass is retained, with small/Type I/DI budgets.
Only a fixed factor changes from the narrow-support normalization. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace XiPrime8845.PRZZWideRowBudget
open PRZZDyadicEnvelope PRZZActualCaseSum PRZZOptimalPowers PRZZNonemptyRowBudget
set_option maxHeartbeats 5000000

theorem row_scale (N d j n : ℕ) (Q : ℝ) (F : ℝ → ℂ)
    (hs : Function.support F ⊆ Set.Icc (Q/2) (3*Q))
    (hn : n ∈ PRZZDyadic.cell N j) (hf : F ((d:ℝ)*n) ≠ 0) :
    Q ≤ 4*(d:ℝ)*(2:ℝ)^j := by
  have hh := (hs hf).1
  have hcell := (PRZZDyadic.mem_cell N j n).mp hn
  have hhi : (n:ℝ) < 2*(2:ℝ)^j := by
    have he : (n:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast hcell.2.2
    simpa only [pow_succ,mul_comm] using he
  nlinarith [mul_le_mul_of_nonneg_left hhi.le (Nat.cast_nonneg d)]

theorem cutoff_frequency (N d j l n m : ℕ) (Q1 Q2 T A lam c : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 0 < T) (hc : 0 < c)
    (_hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hlam : 0 ≤ lam)
    (hs1 : Function.support F1 ⊆ Set.Icc (Q1/2) (3*Q1))
    (hs2 : Function.support F2 ⊆ Set.Icc (Q2/2) (3*Q2))
    (hn : n ∈ PRZZDyadic.cell N j) (hm : m ∈ PRZZDyadic.cell N l)
    (hf1 : F1 ((d:ℝ)*n) ≠ 0) (hf2 : F2 ((d:ℝ)*m) ≠ 0)
    (hfreq : A ≤ lam*(Q1*Q2/((d:ℝ)^2*T))) :
    A ≤ (16*c*lam)*(((2:ℝ)^j/c)*(2:ℝ)^l/T) := by
  have h1 := row_scale N d j n Q1 F1 hs1 hn hf1
  have h2 := row_scale N d l m Q2 F2 hs2 hm hf2
  have hp := mul_le_mul h1 h2 hQ2 (by positivity)
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  apply hfreq.trans
  calc
    _ ≤ lam*((4*(d:ℝ)*(2:ℝ)^j)*(4*(d:ℝ)*(2:ℝ)^l)/((d:ℝ)^2*T)) := by gcongr
    _ = _ := by field_simp; ring

theorem nonempty_row_absorbed (Cs Ci Cg Cd Cr Cp Cv eps eta rho b delta L S r : ℝ)
    (K : ℕ) (ks : List ℕ)
    (hs : 0 ≤ Cs) (hi : 0 ≤ Ci) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd)
    (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hrpos : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d j l n : ℕ) (T M A lam Q1 Q2 x t : ℝ)
      (alpha beta z1 z2 : ℂ) (a a' : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (v : ℤ),
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → (d:ℝ) ≤ T → 1 ≤ lam → 0 < M →
      0 ≤ Q1 → 0 ≤ Q2 →
      Function.support F1 ⊆ Set.Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Set.Icc (Q2/2) (3*Q2) →
      PRZZSupportedBranches.row N d j l a a' F1 F2 FM z1 z2 x t v n ≠ 0 →
      A ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) → r ≤ ‖alpha+beta‖ →
      |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      (d:ℝ)^eta*(N:ℝ)^b*T^eta*
        (∫ p, ‖common d T M ((2:ℝ)^j) ((2:ℝ)^l)
          (sourceW ((alpha+beta)/(Real.log T:ℂ))) ((alpha+beta)/(Real.log T:ℂ)) p‖)*
        (smallBudget Cs T A eta l+largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks) ≤
          C*T^delta*lam*target N T/d := by
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hc : 1 ≤ c := one_le_pow₀ (by norm_num)
  obtain ⟨Cw,hw,hmass⟩ := original_mass L S r hL hS hrpos
  obtain ⟨Cb,hcb,hrow⟩ := PRZZThreeCaseLoss.normalized_row_absorbed
    Cs Ci Cg Cd Cr Cp Cv eps eta rho b delta K ks hs hi hg hd hr hp hv he hn hrho hb hmargin
  refine ⟨Cw*Cb*(16*c),by positivity,?_⟩
  intro N d j l n T M A lam Q1 Q2 x t alpha beta z1 z2 a a' F1 F2 FM v
    hN hNT hlog hA hAT hd0 hdT hlam hM hQ1 hQ2 hF1 hF2 hnon hf hsep hscale hshift
  have hT : 0 < T := by linarith
  obtain ⟨hnj,hfn,m,hml,hfm⟩ := PRZZActualCasePowers.row_nonzero_cutoffs
    N d j l n a a' F1 F2 FM z1 z2 x t v hnon
  have hj : (2:ℝ)^j ≤ N := by
    have hh := (PRZZDyadic.mem_cell N j n).mp hnj
    exact_mod_cast hh.2.1.trans (Finset.mem_Icc.mp hh.1).2
  have hl : (2:ℝ)^l ≤ N := by
    have hh := (PRZZDyadic.mem_cell N l m).mp hml
    exact_mod_cast hh.2.1.trans (Finset.mem_Icc.mp hh.1).2
  have hfreq := cutoff_frequency N d j l n m Q1 Q2 T A lam c
    F1 F2 hd0 hT (by positivity) hQ1 hQ2 (by linarith) hF1 hF2 hnj hml hfn hfm hf
  have hm := hmass d j l T M c alpha beta hd0 hT hM hc hlog hsep hscale hshift
  have hh := hrow N j l T A d (16*c*lam) hN hNT hlog hA hAT
    (by exact_mod_cast hd0) hdT (by nlinarith) hj hl hfreq
  have hlogN : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith)
  have hbudget : 0 ≤ smallBudget Cs T A eta l+
      largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks := by
    unfold smallBudget largeBudget PRZZCommonCellBound.budget
      PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (show 0 ≤ (d:ℝ)^eta*(N:ℝ)^b*T^eta by positivity)) hbudget
  have h2 := mul_le_mul_of_nonneg_left hh hw.le
  apply h1.trans
  convert h2 using 1 <;> (try dsimp only [c]) <;> ring

#print axioms row_scale
#print axioms cutoff_frequency
#print axioms nonempty_row_absorbed
end XiPrime8845.PRZZWideRowBudget

