import PRZZThreeCaseLoss
import PRZZSourceWOuter
import PRZZDyadicBudget

/-! Original dyadic row masses, rather than enlarged HB windows. Nonzero
literal rows supply cutoff witnesses. Source frequency bounds and shift
separation remain explicit: arbitrary D,H do not supply these conditions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace XiPrime8845.PRZZNonemptyRowBudget
open PRZZDyadicEnvelope PRZZActualCaseSum PRZZOptimalPowers
set_option maxHeartbeats 4000000

/-- Compare scalar masses, not the two boxes. The original box has X=2^j;
the arithmetic normalization has X=2^j/c. Constants precede all row data. -/
theorem original_mass (L S r : ℝ) (hL : 0 ≤ L) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d j l : ℕ) (T M c : ℝ) (alpha beta : ℂ),
      0 < d → 0 < T → 0 < M → 1 ≤ c → 1 ≤ Real.log T →
      r ≤ ‖alpha+beta‖ →
      |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      (∫ p, ‖common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        (sourceW ((alpha+beta)/(Real.log T:ℂ))) ((alpha+beta)/(Real.log T:ℂ)) p‖) ≤
        C*(Real.log T)^2*(T/((d:ℝ)*((2:ℝ)^j/c)*(2:ℝ)^l)) := by
  let b := 2/(Real.sqrt Real.pi*r^2)
  refine ⟨24*(1+b)*Real.exp ((L+Real.log 4)*S),by dsimp [b]; positivity,?_⟩
  intro d j l T M c alpha beta hd hT hM hc hlog hsep hscale hshift
  have hm := PRZZSourceWOuter.actual_mass d T M ((2:ℝ)^j) ((2:ℝ)^l)
    L S r alpha beta hd hT hM (by positivity) (by positivity) hlog hL hS hr hsep hscale hshift
  have hs : 1 ≤ (Real.log T)^2 := by nlinarith
  have he : 1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2) ≤ (1+b)*(Real.log T)^2 := by
    calc
      _ = 1+b*(Real.log T)^2 := by dsimp [b]; ring
      _ ≤ (Real.log T)^2+b*(Real.log T)^2 := add_le_add hs le_rfl
      _ = _ := by ring
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hx : (2:ℝ)^j/c ≤ (2:ℝ)^j := div_le_self (by positivity) hc
  calc
    _ ≤ 24*((1+b)*(Real.log T)^2*Real.exp ((L+Real.log 4)*S))*T/((d:ℝ)*(2:ℝ)^j*(2:ℝ)^l) := by
      apply hm.trans
      gcongr
    _ ≤ 24*((1+b)*(Real.log T)^2*Real.exp ((L+Real.log 4)*S))*T/((d:ℝ)*((2:ℝ)^j/c)*(2:ℝ)^l) := by
      gcongr
    _ = _ := by ring

/-- The original row mass times all three actual budgets, with the local
frequency premise supplied by a nonzero source row. No shifted box identity
or assumed outer-integral bound is used. -/
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
      Function.support F1 ⊆ Set.Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Set.Icc Q2 (2*Q2) →
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
  refine ⟨Cw*Cb*(4*c),by positivity,?_⟩
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
  have hfreq := PRZZActualCasePowers.cutoff_frequency N d j l n m Q1 Q2 T A lam c
    F1 F2 hd0 hT (by positivity) hQ1 hQ2 (by linarith) hF1 hF2 hnj hml hfn hfm hf
  have hm := hmass d j l T M c alpha beta hd0 hT hM hc hlog hsep hscale hshift
  have hh := hrow N j l T A d (4*c*lam) hN hNT hlog hA hAT
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

#print axioms original_mass
#print axioms nonempty_row_absorbed

/-- Sum the normalized row bounds over the two complete dyadic grids and
the labelled allocation list (duplicates are retained). The allocation
constants are fixed before height; gamma is the explicitly spent slack.
This sums supplied row bounds, not unidentified original integrals. -/
theorem allocation_dyadic_absorbed {ι : Type*} (qs : List ι) (w : ι → ℝ)
    (hw : ∀ q ∈ qs, 0 ≤ w q) (delta gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T d lam : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 < d → 0 ≤ lam →
      (∑ _j ∈ Finset.range (Nat.log 2 N+1),
        ∑ _l ∈ Finset.range (Nat.log 2 N+1),
          (qs.map (fun q => w q*T^delta*lam*target N T/d)).sum) ≤
        C*T^(delta+gamma)*lam*target N T/d := by
  obtain ⟨D,hD,hgrid⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hgamma
  let W := (qs.map w).sum
  have hW : 0 ≤ W := List.sum_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hw q hq)
  refine ⟨W*D+1,by positivity,?_⟩
  intro N T d lam hN hNT hlog hd hlam
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one
    ((by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT)
  have he : (qs.map (fun q => w q*T^delta*lam*target N T/d)).sum =
      W*T^delta*lam*target N T/d := by
    dsimp only [W]
    clear hw hW W
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn : 0 ≤ T^delta*lam*target N T/d := by unfold target; positivity
  have hh := mul_le_mul_of_nonneg_right (hgrid N hN T hNT hlog 2 le_rfl)
    (mul_nonneg hW hn)
  have ht : 0 ≤ T^(delta+gamma)*lam*target N T/d := by unfold target; positivity
  rw [Real.rpow_add hT] at ht ⊢
  push_cast
  ring_nf at hh ht ⊢
  linarith only [hh,ht]

#print axioms allocation_dyadic_absorbed
end XiPrime8845.PRZZNonemptyRowBudget
