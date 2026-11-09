import PRZZResolvedTailMass
import PRZZCappedPrefactor

/-! Actual Fourier tails with a common cap selected before arbitrary
coefficients and height. The real dual Gamma quotient, scaled powers,
native residue and the arithmetic denominator 1/d are retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Finset
namespace XiPrime8845.PRZZCappedTailMass
open PRZZMellinSeparation PRZZResolvedTailMass
set_option maxHeartbeats 7000000

def coeff (F G : ℝ → ℂ) (c : ℕ → ℂ) (d : ℕ) (Q V T : ℝ)
    (A B : ℂ) (z : PRZZAStar.Index) : ℂ :=
  PRZZUnfrozenPoisson.arithmetic c
    (scaledCutoff F Q) (scaledCutoff G V) d (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) z /
      ((z.1.1:ℂ)*(z.1.2:ℂ))

theorem pair_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (dual : Bool) (c : ℕ → ℂ) (N d j l : ℕ) (Q V t : ℝ) (A B : ℂ)
        (w : ℤ × ℕ) (s : Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → t ∈ Icc T (2*T) → ‖A‖ ≤ S → ‖B‖ ≤ S →
      s ⊆ PRZZPrefactorMass.pairs N d j l →
      (∑ p ∈ s, ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
        exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖) ≤
        C/d := by
  obtain ⟨C,hC,h⟩ := PRZZCappedPrefactor.pair_mass F G hF hG hcF hcG
  refine ⟨C*Real.exp (2*S)*Real.exp (4*S+7)*(Hcap^2+1),by positivity,?_⟩
  filter_upwards [branch_cap S hS,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hcap hlog
  intro dual c N d j l Q V t A B w s hcoef hN hd hNT ht hA hB hsub
  have hL : 0 < Real.log T := by linarith
  have hz (Z : ℂ) (hZ : ‖Z‖ ≤ S) : |(Z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    exact div_le_div_of_nonneg_right hZ hL.le
  have hm := h c Hcap N d j l T Q V S (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) w
    hHcap hcoef hN hd hNT hL hS (hz B hB) (hz A hA)
  have hc : (∑ p ∈ s, ‖coeff F G c d Q V T A B (p,w)‖) ≤
      C*Real.exp (2*S)*Hcap^2/d := by
    apply le_trans _ hm
    have he (p : ℕ × ℕ) : ‖coeff F G c d Q V T A B (p,w)‖ =
        ‖PRZZAStar.prefactor c
          (scaledCutoff F Q) (scaledCutoff G V) d (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ))
            (p,w)/((p.1:ℂ)*(p.2:ℂ))‖ :=
      PRZZUnfrozenPoisson.arithmetic_mass_eq _ _ _ d _ _ (p,w)
    simp_rw [he]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp hps =>
      norm_nonneg (PRZZAStar.prefactor c
        (scaledCutoff F Q) (scaledCutoff G V) d (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ))
          (p,w)/((p.1:ℂ)*(p.2:ℂ))))
  have hterm : ∀ p ∈ s, ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
        exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖ ≤
      ‖coeff F G c d Q V T A B (p,w)‖*Real.exp (4*S+7) := by
    intro p hp
    have hv := (PRZZDyadic.mem_cell N l p.2).mp
      (mem_product.mp (mem_filter.mp (hsub hp)).1).2
    have hv1 : (1:ℝ) ≤ p.2 := by exact_mod_cast (mem_Icc.mp hv.1).1
    have hvT : (p.2:ℝ) ≤ T :=
      (by exact_mod_cast (mem_Icc.mp hv.1).2 : (p.2:ℝ) ≤ N).trans hNT
    have he : branch dual A B T t * coeff F G c d Q V T A B (p,w) *
        exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ)) =
      coeff F G c d Q V T A B (p,w) *
        (branch dual A B T t * exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))) := by ring
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_left (hcap dual A B t p.2 hA hB ht hv1 hvT) (norm_nonneg _)
  apply (sum_le_sum hterm).trans
  rw [← sum_mul]
  calc
    _ ≤ (C*Real.exp (2*S)*Hcap^2/d)*Real.exp (4*S+7) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = (C*Real.exp (2*S)*Real.exp (4*S+7))*Hcap^2/d := by ring
    _ ≤ _ := by gcongr; nlinarith

theorem tails_absorbed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH A0 : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (dual : Bool) (N d j l : ℕ) (M Q V Q1 t : ℝ) (A B : ℂ)
        (w : ℤ × ℕ) (s : Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ 3*M → M ≤ T^b → 0 < Q1 →
      t ∈ Icc T (2*T) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      s ⊆ PRZZPrefactorMass.pairs N d j l →
      Function.support (scaledCutoff F Q) ⊆ Icc (Q1/2) (3*Q1) →
      |(w.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      (∑ p ∈ s, ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
        PRZZUnitTailMass.tail W M T eH t A B w.1 w.2
          (PRZZCentralTail.residue (p,w)/p.2) p‖) ≤ K*T^(-A0)/d := by
  obtain ⟨Cm,hCm,hmass⟩ := pair_mass F G hF hG hcF hcG Hcap hHcap S hS
  obtain ⟨Ct,hCt,htail⟩ := PRZZResolvedTail.arithmetic_row W hW hsW
    a b S r eD eH (A0+1) ha hb hS hr heD he
  obtain ⟨Cl,hCl,hlog⟩ := PRZZOptimalOuter.power_log_absorbed
    (0:ℕ) (-(A0+1)) (-A0) (by linarith)
  refine ⟨Cm*Ct*Cl+1,by positivity,?_⟩
  filter_upwards [hmass,eventually_ge_atTop (36:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hm hT hL
  intro c dual N d j l M Q V Q1 t A B w s hcoef hN hd hNT hM hMT hQ ht hA hB hsep hsub hs1 hg
  have hdR : (0:ℝ) < d := by exact_mod_cast (Nat.zero_lt_one.trans_le hd)
  have hh0 := hm dual c N d j l Q V t A B w s hcoef hN hd hNT ht hA hB hsub
  have hh : (∑ p ∈ s, ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
      exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖) ≤
      Cm*(Real.log N)^(0:ℕ)/d := by simpa using hh0
  have hp : ∀ p ∈ s, ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
      PRZZUnitTailMass.tail W M T eH t A B w.1 w.2
        (PRZZCentralTail.residue (p,w)/p.2) p‖ ≤
      ‖branch dual A B T t * coeff F G c d Q V T A B (p,w) *
        exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖ *
          (Ct*T^(-(A0+1))) := by
    intro p hp
    have hbox := mem_product.mp (mem_filter.mp (hsub hp)).1
    have hu := mem_Icc.mp ((PRZZDyadic.mem_cell N j p.1).mp hbox.1).1
    have hv := mem_Icc.mp ((PRZZDyadic.mem_cell N l p.2).mp hbox.2).1
    have hrow := htail T M t d Q1 d (p,w) A B
      c (scaledCutoff F Q) (scaledCutoff G V)
      hT hL hM hMT (Nat.zero_lt_one.trans_le hu.1) (Nat.zero_lt_one.trans_le hv.1)
      ((by exact_mod_cast hv.2 : (p.2:ℝ) ≤ N).trans hNT) ht hA hB hsep rfl hdR hQ hs1 hg
    simpa only [coeff,PRZZUnitTailMass.tail,norm_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left hrow (norm_nonneg (branch dual A B T t))
  have hsum := sum_le_sum hp
  rw [← sum_mul] at hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_right hh (by positivity))
  have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogs : (Real.log N)^(0:ℕ) ≤
      (Real.log T)^(0:ℕ) := by gcongr
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogs hCm.le) hdR.le)
      (by positivity))
  have hl := mul_le_mul_of_nonneg_left (hlog T (by linarith))
    (show 0 ≤ Cm*Ct/(d:ℝ) by positivity)
  have hz : 0 ≤ T^(-A0)/(d:ℝ) := by positivity
  have hl' : Cm*(Real.log T)^(0:ℕ)/(d:ℝ)*
      (Ct*T^(-(A0+1))) ≤ (Cm*Ct*Cl)*T^(-A0)/(d:ℝ) := by
    calc
      _ = (Cm*Ct/(d:ℝ))*(T^(-(A0+1))*(Real.log T)^(0:ℕ)) := by ring
      _ ≤ (Cm*Ct/(d:ℝ))*(Cl*T^(-A0)) := hl
      _ = _ := by ring
  apply hbound'.trans (hl'.trans _)
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right
    (show Cm*Ct*Cl ≤ Cm*Ct*Cl+1 by linarith) hz

#print axioms pair_mass
#print axioms tails_absorbed
end XiPrime8845.PRZZCappedTailMass
