import PRZZRowIntegralBudget

/-! Empty rows are removed before taking branch norms. Activity refers to
the original signed row, not to an individual HB summand. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZActiveRows
open PRZZRowMellinBranches PRZZOriginalRowWindow PRZZRowIntegralBudget
open PRZZActualAggregate PRZZCoefficientSeparation PRZZMellinSeparation
set_option maxHeartbeats 4000000

def Active (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) : Prop :=
  ∃ x y t, signedRow N d j l D H a F1 F2 FM alpha beta x y t ≠ 0

theorem active_witness (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ)
    (ha : Active N d j l D H a F1 F2 FM alpha beta) :
    ∃ x t v n, PRZZSupportedBranches.row N d j l a a F1 F2 FM alpha beta x t v n ≠ 0 := by
  classical
  obtain ⟨x,y,t,ht⟩ := ha
  by_contra hn
  push Not at hn
  apply ht
  unfold signedRow
  apply sum_eq_zero
  intro v hv
  have he := PRZZSupportedBranches.mixed_row N d j l a a F1 F2 FM alpha beta x t v
  rw [PRZZHBRectangles.mixed_diagonal] at he
  rw [he]
  simp [hn]

theorem inactive_integral (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (ha : ¬ Active N d j l D H a F1 F2 FM alpha beta) :
    (∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)) = 0 := by
  have hz : ∀ x y t, signedRow N d j l D H a F1 F2 FM alpha beta x y t = 0 := by
    simpa only [Active,not_exists,not_not] using ha
  have h := row_integral_bound N d j l D H T M 0 a F1 F2 FM W Phi alpha beta
    hN hd hT hM hFM hW hPhi hsM hsP le_rfl (by intros; simp [hz])
  simpa using h

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
      0 ≤ Q1 → 0 ≤ Q2 → Function.support F1 ⊆ Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Icc Q2 (2*Q2) →
      Active N d j l D H a F1 F2 FM z1 z2 →
      A ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) → r ≤ ‖alpha+beta‖ →
      |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      (∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        (PRZZDyadicEnvelope.sourceW ((alpha+beta)/(Real.log T:ℂ)))
        ((alpha+beta)/(Real.log T:ℂ)) p‖)*
        rowBudget C0 w caps js eps eta b T A N d K j l ≤
      C*T^delta*lam*PRZZOptimalPowers.target N T/d := by
  have supplier (q : List ℕ × List ℕ) := PRZZNonemptyRowBudget.nonempty_row_absorbed
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

#print axioms active_witness
#print axioms inactive_integral
#print axioms active_budget_absorbed

/-- Optimized N,T powers for literal A*, conditional on the stated source
frequency and scale ranges. Empty original rows are discarded before the
positive arithmetic envelopes are summed. Weil and DI remain Prop inputs. -/
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
    ∃ C : ℝ, 0 < C ∧ ∀ (N d : ℕ) (T Q D H M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
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
      ‖PRZZAStar.literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW ((A+B)/(Real.log T:ℂ))) Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C0,hC0,hw,hrows⟩ := signedRow_bound hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 FM hf hc hF hcF hFM hcM
  obtain ⟨Cr,hCr,habs⟩ := active_budget_absorbed C0 w caps js K eps eta rho b delta L Souter r
    hC0 hw heps.le heta.le hrho hb.le hL hSo hr hmargin
  obtain ⟨Dg,hDg,hgrid⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hgamma
  refine ⟨(1/(2*Real.pi))*Cr*Dg,by positivity,?_⟩
  intro N d T Q D H M lam Q1 Q2 A B Phi hN hd hT hNT hdT hlog hfreq hfreqT hfreqS
    hlam hM hQ1 hQ2 hF1 hF2 hsM ha hz hb' hsep hshift hscale hPhi hsP
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
          exact hrows N d j l T Q D H p.1 p.2 t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb')
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

#print axioms literal_absorbed
end XiPrime8845.PRZZActiveRows
