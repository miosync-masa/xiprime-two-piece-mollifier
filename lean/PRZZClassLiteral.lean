import PRZZMixedLiteral

/-! The class-uniform mixed HB row budget is integrated in the original
literal geometry and absorbed at the optimal PRZZ N,T powers. Source
frequency, support scales and separated shifts remain explicit. This is
not yet a mixed AFE residual estimate or a full moment theorem. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZClassLiteral
open PRZZMellinSeparation PRZZOriginalRowWindow PRZZRowIntegralBudget
open PRZZActualAggregate PRZZCoefficientSeparation PRZZActiveRows
open PRZZMixedLiteral
set_option maxHeartbeats 10000000

theorem literal_absorbed
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta b rho delta gamma S Z L Souter r : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hrho : 0 ≤ rho)
    (hgamma : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hSo : 0 ≤ Souter) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ (N d : ℕ) (T Q D H M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ T^rho →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) →
      1 ≤ lam → 0 < M → 0 ≤ Q1 → 0 ≤ Q2 →
      Function.support (scaledCutoff F0 Q) ⊆ Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Icc Q2 (2*Q2) → Function.support FM ⊆ Icc (M/2) (3*M) →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖A/(Real.log T:ℂ)‖ ≤ Z →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖PRZZMixedLiteral.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))) Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C0,hC0,hw,hrows⟩ := PRZZClassRows.basis_bound hWeil hDI K hK js ks eps eta b S Z
    heps heta hb hS hZ width jets hjets
  obtain ⟨Cr,hCr,habs⟩ := active_budget_absorbed C0 w caps js K eps eta rho b delta L Souter r
    hC0 hw heps.le heta.le hrho hb.le hL hSo hr hmargin
  obtain ⟨Dg,hDg,hgrid⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hgamma
  refine ⟨(1/(2*Real.pi))*Cr*Dg,by positivity,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d T Q D H M lam Q1 Q2 A B Phi hN hd hT hNT hdT hlog hfreq hfreqT hfreqS
    hlam hM hQ1 hQ2 hF1 hF2 hsM ha hz hb' hsep hshift hscale hPhi hsP
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let a' := fun n => (PRZZGCoefficient.coefficient ks n:ℂ)
  have hFM : Continuous FM := hfM.smooth.continuous
  have hF1fold := (left_support a (scaledCutoff F0 Q)).trans hF1
  have hF2fold := (right_support a' F2).trans hF2
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  let W := PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  have hW : ContinuousOn W (Ioi 0) := PRZZSourceWOuter.sourceW_continuous _
    (div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (Real.log_pos hT).ne'))
  have hpoint (j l : ℕ) (hl : l ∈ range (Nat.log 2 N+1)) :
      ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T (fun _ => 1) (leftFold a (scaledCutoff F0 Q)) (rightFold a' F2) FM W Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*Cr*T^delta*lam*PRZZOptimalPowers.target N T/d*J := by
    by_cases hactive : Active N d j l D H (fun _ => 1) (leftFold a (scaledCutoff F0 Q)) (rightFold a' F2) FM alpha beta
    · have hi := row_integral_bound N d j l D H T M
        (rowBudget C0 w caps js eps eta b T (PRZZActualSignedBranches.frequencyBound d D H) N d K j l)
        a a' (scaledCutoff F0 Q) F2 FM W Phi alpha beta hN hd (by linarith) hM hFM hW hPhi hsM hsP
        (rowBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC0.le (fun q => (hw q).le)
          (by linarith) (by positivity)) (by
          intro p hp t
          exact hrows F0 F2 FM hf0 hf2 hfM N d j l T Q D H p.1 p.2 t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb')
      have hh := habs N d j l D H T M (PRZZActualSignedBranches.frequencyBound d D H) lam Q1 Q2
        A B alpha beta (fun _ => 1) (leftFold a (scaledCutoff F0 Q)) (rightFold a' F2) FM (by exact_mod_cast hN) hNT hlog
        (by positivity) hfreqT hd hdT hlam hM hQ1 hQ2 hF1fold hF2fold hactive hfreqS hsep (hscale l hl) hshift
      have he : alpha+beta = (A+B)/(Real.log T:ℂ) := by dsimp [alpha,beta]; ring
      rw [he] at hi
      have hh' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (show 0 ≤ 1/(2*Real.pi) by positivity)) hJ
      apply hi.trans
      convert hh' using 1 <;> dsimp only [J,W] <;> ring
    · rw [inactive_integral N d j l D H T M (fun _ => 1) (leftFold a (scaledCutoff F0 Q)) (rightFold a' F2) FM W Phi alpha beta
        hN hd (by linarith) hM hFM hW hPhi hsM hsP hactive,norm_zero]
      unfold PRZZOptimalPowers.target
      positivity
  rw [literal_fold, PRZZLiteralRows.literal_rows N d D H T M (fun _ => 1) (leftFold a (scaledCutoff F0 Q)) (rightFold a' F2) FM W Phi alpha beta
    hN (by linarith) hM hFM hW hPhi.continuous hsM hsP]
  calc
    _ ≤ ∑ _j ∈ range (Nat.log 2 N+1), ∑ _l ∈ range (Nat.log 2 N+1),
        (1/(2*Real.pi))*Cr*T^delta*lam*PRZZOptimalPowers.target N T/d*J :=
      (norm_sum_le _ _).trans (sum_le_sum (fun j hj =>
        (norm_sum_le _ _).trans (sum_le_sum (fun l hl => hpoint j l hl))))
    _ ≤ _ := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      have ht : 0 < T := by linarith
      have hh := mul_le_mul_of_nonneg_right (hgrid N hN T (by linarith) hlog 2 le_rfl)
        (show 0 ≤ (1/(2*Real.pi))*Cr*T^delta*lam*PRZZOptimalPowers.target N T/d*J by
          unfold PRZZOptimalPowers.target; positivity)
      rw [Real.rpow_add ht]
      push_cast
      convert hh using 1 <;> (try dsimp only [J]) <;> first | rfl | ring


theorem literal_uniform_mass
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta b rho delta gamma S Z L Souter r : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hrho : 0 ≤ rho)
    (hgamma : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hSo : 0 ≤ Souter) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ (N d : ℕ) (T Q D H M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ T^rho →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) →
      1 ≤ lam → 0 < M → 0 ≤ Q1 → 0 ≤ Q2 →
      Function.support (scaledCutoff F0 Q) ⊆ Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Icc Q2 (2*Q2) → Function.support FM ⊆ Icc (M/2) (3*M) →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖A/(Real.log T:ℂ)‖ ≤ Z →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖PRZZMixedLiteral.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))) Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := literal_absorbed hWeil hDI K hK js ks eps eta b rho delta gamma S Z L Souter r
    heps heta hb hrho hgamma hS hZ hL hSo hr hmargin width jets hjets
  let Hphi := PRZZProfileMellin.massCap widthPhi jetsPhi
  have hHphi : 0 ≤ Hphi := PRZZProfileMellin.massCap_nonneg widthPhi hwPhi jetsPhi hjPhi
  refine ⟨C*(Hphi+1),by positivity,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d T Q D H M lam Q1 Q2 A B Phi hN hd hT hNT hdT hlog hfreq hfreqT hfreqS
    hlam hM hQ1 hQ2 hF1 hF2 hsM ha hz hb' hsep hshift hscale hPhi hsP
  have hh := h F0 F2 FM hf0 hf2 hfM N d T Q D H M lam Q1 Q2 A B Phi hN hd hT hNT hdT hlog
    hfreq hfreqT hfreqS hlam hM hQ1 hQ2 hF1 hF2 hsM ha hz hb' hsep hshift hscale hPhi.smooth hsP
  have hm := PRZZProfileMellin.member_mass widthPhi jetsPhi hjPhi Phi hPhi
  let X := T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d
  have hX : 0 ≤ X := by dsimp [X,PRZZOptimalPowers.target]; positivity
  have hi : ‖PRZZMixedLiteral.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))) Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*X*(∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
    convert hh using 1
    dsimp only [X]
    ring
  apply hi.trans
  apply (mul_le_mul_of_nonneg_left hm (mul_nonneg hC.le hX)).trans
  change C*X*Hphi ≤ _
  have he : C*(Hphi+1)*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d = C*(Hphi+1)*X := by
    dsimp [X]; ring
  rw [he]
  nlinarith [mul_nonneg hC.le hX]

#print axioms literal_uniform_mass

#print axioms literal_absorbed
end XiPrime8845.PRZZClassLiteral
