import PRZZActiveRows
import PRZZWideRowBudget
import PRZZUniformAggregate

/-! Localized optimal literal bounds for the actual wide scaled profiles.
All case caps precede both profile scales and height. Empty original rows
are removed before the positive row envelopes, not after branch norms. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZWideActiveRows
open PRZZRowMellinBranches PRZZOriginalRowWindow PRZZRowIntegralBudget PRZZActiveRows
open PRZZActualAggregate PRZZCoefficientSeparation PRZZMellinSeparation
open PRZZAllSignedSources PRZZSupportedSplit PRZZGCoefficient
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
private theorem sum_scale {ι : Type*} (qs : List ι) (f : ι → ℝ) (r : ℝ) :
    (qs.map (fun q => f q*r)).sum = (qs.map f).sum*r := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- Apply nonempty_row_absorbed to every labelled allocation using ONE
original active-row witness. No nonvanishing of individual branches is
assumed. All constants precede the height and cutoff configuration. -/
theorem active_budget_absorbed (C0 : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ) (K : ℕ)
    (eps eta rho b delta L S r : ℝ) (hC0 : 0 < C0) (hw : ∀ q, 0 < w q)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d j l : ℕ) (D H T M A lam Q1 Q2 : ℝ)
      (alpha beta z1 z2 : ℂ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ),
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → (d:ℝ) ≤ T → 1 ≤ lam → 0 < M →
      0 ≤ Q1 → 0 ≤ Q2 → Function.support F1 ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) →
      Active N d j l D H a F1 F2 FM z1 z2 →
      A ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) → r ≤ ‖alpha+beta‖ →
      |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      (∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        (PRZZDyadicEnvelope.sourceW ((alpha+beta)/(Real.log T:ℂ)))
        ((alpha+beta)/(Real.log T:ℂ)) p‖)*
        rowBudget C0 w caps js eps eta b T A N d K j l ≤
      C*T^delta*lam*PRZZOptimalPowers.target N T/d := by
  have supplier (q : List ℕ × List ℕ) := PRZZWideRowBudget.nonempty_row_absorbed
    (caps q).small (caps q).typeI (caps q).g (caps q).di (caps q).right (caps q).phase
    (caps q).variation eps eta rho b delta L S r K q.2
    (caps q).positive.1.le (caps q).positive.2.1.le (caps q).positive.2.2.1.le
    (caps q).positive.2.2.2.1.le (caps q).positive.2.2.2.2.1.le
    (caps q).positive.2.2.2.2.2.1.le (caps q).positive.2.2.2.2.2.2.le
    he hn hrho hb hL hS hr hmargin
  choose c hc hbound using supplier
  let B := ((allocations js).map (fun q => w q*c q)).sum
  have hB : 0 ≤ B := List.sum_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (hw q).le (hc q).le)
  refine ⟨C0*B+1,by positivity,?_⟩
  intro N d j l D H T M A lam Q1 Q2 alpha beta z1 z2 a F1 F2 FM
    hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hactive hfreq hsep hscale hshift
  obtain ⟨x,t,v,n,hrow⟩ := active_witness N d j l D H a F1 F2 FM z1 z2 hactive
  let mass := ∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
    (PRZZDyadicEnvelope.sourceW ((alpha+beta)/(Real.log T:ℂ)))
    ((alpha+beta)/(Real.log T:ℂ)) p‖
  let U := T^delta*lam*PRZZOptimalPowers.target N T/d
  have hT : 0 < T := by linarith
  have hU : 0 ≤ U := by dsimp [U,PRZZOptimalPowers.target]; positivity
  have hq (q : List ℕ × List ℕ) :
      mass*((d:ℝ)^eta*(N:ℝ)^b*T^eta*row (caps q) eps eta T A N K j l q.2) ≤ c q*U := by
    have hh := hbound q N d j l n T M A lam Q1 Q2 x t alpha beta z1 z2 a a F1 F2 FM v
      hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hrow hfreq hsep hscale hshift
    convert hh using 1 <;> (try dsimp only [mass,U,row]) <;> ring
  have hh : ((allocations js).map (fun q =>
      mass*((d:ℝ)^eta*(N:ℝ)^b*T^eta*row (caps q) eps eta T A N K j l q.2)*w q)).sum ≤ B*U := by
    rw [← sum_scale]
    apply List.sum_le_sum
    intro q hqmem
    exact (mul_le_mul_of_nonneg_right (hq q) (hw q).le).trans_eq (by ring)
  have hsum := mul_le_mul_of_nonneg_left hh hC0.le
  have heq : mass*rowBudget C0 w caps js eps eta b T A N d K j l =
      C0*((allocations js).map (fun q =>
        mass*((d:ℝ)^eta*(N:ℝ)^b*T^eta*row (caps q) eps eta T A N K j l q.2)*w q)).sum := by
    unfold rowBudget
    have he (q : List ℕ × List ℕ) :
        mass*((d:ℝ)^eta*(N:ℝ)^b*T^eta*row (caps q) eps eta T A N K j l q.2)*w q =
        (w q*T^eta*row (caps q) eps eta T A N K j l q.2)*(mass*(d:ℝ)^eta*(N:ℝ)^b) := by ring
    simp_rw [he]
    rw [sum_scale]
    ring
  change mass*rowBudget C0 w caps js eps eta b T A N d K j l ≤ _
  rw [heq]
  have hh' : C0*((allocations js).map (fun q =>
        mass*((d:ℝ)^eta*(N:ℝ)^b*T^eta*row (caps q) eps eta T A N K j l q.2)*w q)).sum ≤
      (C0*B+1)*U := by nlinarith only [hsum,hU]
  exact hh'.trans_eq (by dsimp [U]; ring)


theorem signedRow_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 QM : ℝ, ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedRow N d j l D H (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 Q2) (scaledCutoff FM QM) alpha betaShift x y t‖ ≤
      rowBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    PRZZUniformAggregate.actual_blocks hWeil hDI K hK q.2 js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 QM N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let F2 := scaledCutoff F2 Q2
  let FM := scaledCutoff FM QM
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [signedRow_blocks N d j l K hd (by omega)]
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 js D H x y t (scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q Q2 QM N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  rw [sum_scale] at hh
  exact hh.trans_eq (by dsimp [rowBudget,A]; ring)


theorem literal_absorbed
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b rho delta gamma S Z L Souter r : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hrho : 0 ≤ rho)
    (hgamma : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hSo : 0 ≤ Souter) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hFM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ C : ℝ, 0 < C ∧ ∀ R2 RM : ℝ, ∀ (N d : ℕ) (T Q D H M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ T^rho →
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) →
      1 ≤ lam → 0 < M → 0 ≤ Q1 → 0 ≤ Q2 →
      Function.support (scaledCutoff F0 Q) ⊆ Icc (Q1/2) (3*Q1) →
      Function.support (scaledCutoff F2 R2) ⊆ Icc (Q2/2) (3*Q2) → Function.support (scaledCutoff FM RM) ⊆ Icc (M/2) (3*M) →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖A/(Real.log T:ℂ)‖ ≤ Z →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖PRZZAStar.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 R2) (scaledCutoff FM RM) (PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))) Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C0,hC0,hw,hrows⟩ := signedRow_uniform hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 FM hf hc hF hcF hFM hcM
  obtain ⟨Cr,hCr,habs⟩ := active_budget_absorbed C0 w caps js K eps eta rho b delta L Souter r
    hC0 hw heps.le heta.le hrho hb.le hL hSo hr hmargin
  obtain ⟨Dg,hDg,hgrid⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hgamma
  refine ⟨(1/(2*Real.pi))*Cr*Dg,by positivity,?_⟩
  intro R2 RM N d T Q D H M lam Q1 Q2 A B Phi hN hd hT hNT hdT hlog hfreq hfreqT hfreqS
    hlam hM hQ1 hQ2 hF1 hF2 hsM ha hz hb' hsep hshift hscale hPhi hsP
  let F2 := scaledCutoff F2 R2
  let FM := scaledCutoff FM RM
  have hFM : Continuous FM := hFM.comp (continuous_const.mul continuous_id)
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  let W := PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  have hW : ContinuousOn W (Ioi 0) := PRZZSourceWOuter.sourceW_continuous _
    (div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (Real.log_pos hT).ne'))
  have hpoint (j l : ℕ) (hl : l ∈ range (Nat.log 2 N+1)) :
      ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a (scaledCutoff F0 Q) F2 FM W Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*Cr*T^delta*lam*PRZZOptimalPowers.target N T/d*J := by
    by_cases hactive : Active N d j l D H a (scaledCutoff F0 Q) F2 FM alpha beta
    · have hi := row_integral_bound N d j l D H T M
        (rowBudget C0 w caps js eps eta b T (PRZZActualSignedBranches.frequencyBound d D H) N d K j l)
        a (scaledCutoff F0 Q) F2 FM W Phi alpha beta hN hd (by linarith) hM hFM hW hPhi hsM hsP
        (rowBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC0.le (fun q => (hw q).le)
          (by linarith) (by positivity)) (by
          intro p hp t
          exact hrows R2 RM N d j l T Q D H p.1 p.2 t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb')
      have hh := habs N d j l D H T M (PRZZActualSignedBranches.frequencyBound d D H) lam Q1 Q2
        A B alpha beta a (scaledCutoff F0 Q) F2 FM (by exact_mod_cast hN) hNT hlog
        (by positivity) hfreqT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hactive hfreqS hsep (hscale l hl) hshift
      have he : alpha+beta = (A+B)/(Real.log T:ℂ) := by dsimp [alpha,beta]; ring
      rw [he] at hi
      have hh' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (show 0 ≤ 1/(2*Real.pi) by positivity)) hJ
      apply hi.trans
      convert hh' using 1 <;> dsimp only [J,W] <;> ring
    · rw [inactive_integral N d j l D H T M a (scaledCutoff F0 Q) F2 FM W Phi alpha beta
        hN hd (by linarith) hM hFM hW hPhi hsM hsP hactive,norm_zero]
      unfold PRZZOptimalPowers.target
      positivity
  rw [PRZZLiteralRows.literal_rows N d D H T M a (scaledCutoff F0 Q) F2 FM W Phi alpha beta
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


/-- The localized positive budget itself: original inactive rows contribute
zero, while each active row keeps its own outer mass. -/
def activeBudget (C0 : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ) (K N d : ℕ)
    (eps eta b D H T M A : ℝ) (alpha beta z1 z2 : ℂ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) : ℝ :=
  ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
    if Active N d j l D H a F1 F2 FM z1 z2 then
      (∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        (PRZZDyadicEnvelope.sourceW ((alpha+beta)/(Real.log T:ℂ)))
        ((alpha+beta)/(Real.log T:ℂ)) p‖)*
        rowBudget C0 w caps js eps eta b T A N d K j l else 0

theorem active_total_absorbed (C0 : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ) (K : ℕ)
    (eps eta rho b delta gamma L S r : ℝ) (hC0 : 0 < C0) (hw : ∀ q, 0 < w q)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ b)
    (hgamma : 0 < gamma) (hL : 0 ≤ L) (hS : 0 ≤ S) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d : ℕ) (D H T M A lam Q1 Q2 : ℝ)
      (alpha beta z1 z2 : ℂ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ),
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → (d:ℝ) ≤ T → 1 ≤ lam → 0 < M →
      0 ≤ Q1 → 0 ≤ Q2 → Function.support F1 ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) →
      A ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) → r ≤ ‖alpha+beta‖ →
      (∀ l ∈ range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      activeBudget C0 w caps js K N d eps eta b D H T M A alpha beta z1 z2 a F1 F2 FM ≤
        C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d := by
  obtain ⟨Cr,hCr,hrb⟩ := active_budget_absorbed C0 w caps js K eps eta rho b delta L S r
    hC0 hw he hn hrho hb hL hS hr hmargin
  obtain ⟨Dg,hDg,hgrid⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hgamma
  refine ⟨Cr*Dg,by positivity,?_⟩
  intro N d D H T M A lam Q1 Q2 alpha beta z1 z2 a F1 F2 FM
    hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hfreq hsep hscale hshift
  have hNnat : 1 ≤ N := by exact_mod_cast hN
  have ht : 0 < T := by linarith
  have hpoint (j l : ℕ) (hl : l ∈ range (Nat.log 2 N+1)) :
      (if Active N d j l D H a F1 F2 FM z1 z2 then
        (∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
          (PRZZDyadicEnvelope.sourceW ((alpha+beta)/(Real.log T:ℂ)))
          ((alpha+beta)/(Real.log T:ℂ)) p‖)*
          rowBudget C0 w caps js eps eta b T A N d K j l else 0) ≤
        Cr*T^delta*lam*PRZZOptimalPowers.target N T/d := by
    split_ifs with hactive
    · exact hrb N d j l D H T M A lam Q1 Q2 alpha beta z1 z2 a F1 F2 FM
        hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hactive hfreq hsep (hscale l hl) hshift
    · unfold PRZZOptimalPowers.target; positivity
  calc
    _ ≤ ∑ _j ∈ range (Nat.log 2 N+1), ∑ _l ∈ range (Nat.log 2 N+1),
        Cr*T^delta*lam*PRZZOptimalPowers.target N T/d :=
      sum_le_sum (fun j hj => sum_le_sum (fun l hl => hpoint j l hl))
    _ ≤ _ := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      have hh := mul_le_mul_of_nonneg_right (hgrid N hNnat T (by linarith) hlog 2 le_rfl)
        (show 0 ≤ Cr*T^delta*lam*PRZZOptimalPowers.target N T/d by
          unfold PRZZOptimalPowers.target; positivity)
      rw [Real.rpow_add ht]
      push_cast
      convert hh using 1 <;> first | rfl | ring

#print axioms active_total_absorbed
#print axioms active_budget_absorbed
#print axioms signedRow_uniform
#print axioms literal_absorbed
end XiPrime8845.PRZZWideActiveRows

