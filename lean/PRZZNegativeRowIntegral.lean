import PRZZNegativeRowWindow
import PRZZRowIntegralBudget
import PRZZWindowScaleSupply

/-! The negative modulated row is the reflected arithmetic row inside
its ORIGINAL positive spatial box. The two phase signs are transported
by the delta involution, not by conjugating the coefficients or shifts. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZNegativeRowIntegral
open PRZZAStar PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation PRZZAStarMellin
open PRZZNegativeArithmetic PRZZNegativeMellin PRZZNegativeRowWindow
open PRZZOriginalRowWindow (rowIndices)
open PRZZRowMellinBranches (signedRow)
set_option maxHeartbeats 8000000

theorem row_amplitude (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    (∑ z ∈ rowIndices N d j l D H,
      amplitudeMinus d a F1 F2 FM W alpha beta x y z*twist z.1.1 t*twist z.1.2 t) =
      (W (2*Real.pi*x/y)/((d:ℂ)*(x:ℂ)^(alpha+beta)))*
        PRZZNegativeLocalRows.row N d j l D H a F1 F2 FM alpha beta x y t := by
  classical
  let ps := (pairs N d).filter (fun i => i.1 ∈ PRZZDyadic.cell N j ∧ i.2 ∈ PRZZDyadic.cell N l)
  have hidx : rowIndices N d j l D H = ps.product (frequencies d D H) := by
    ext z
    simp [rowIndices,ps,indices,pairs,frequencies,and_assoc,and_left_comm,and_comm]
  have hr (v : ℤ) : PRZZAStarRectangles.rectangle N d j l a F1 F2 (reflect FM) alpha beta (-x) t v =
      ∑ i ∈ ps, pairCoeff d a F1 F2 (reflect FM) alpha beta (-x) t i *
        PRZZKloostermanInputs.e (-(v:ℝ)*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2) := by
    simp only [ps,pairs,PRZZAStarRectangles.rectangle,PRZZDyadic.cell,
      sum_filter,Finset.product_eq_sprod,Finset.sum_product,mem_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hj : Nat.log 2 n = j
    · simp only [hj,if_true,hn,true_and]
      apply sum_congr rfl
      intro m hm
      by_cases hl : Nat.log 2 m = l <;>
        by_cases hc : n.Coprime m ∧ d*n ≤ N ∧ d*m ≤ N <;> simp [hm,hl,hc]
    · simp [hj,hn]
  have hexp : PRZZNegativeLocalRows.row N d j l D H a F1 F2 FM alpha beta x y t =
      ∑ i ∈ ps, ∑ q ∈ frequencies d D H,
        pairCoeff d a F1 F2 FM alpha beta x t i*
          (PRZZKloostermanInputs.e ((q.2:ℝ)*x)*PRZZKloostermanInputs.e ((q.1:ℝ)*y/(2*Real.pi)))*
          PRZZKloostermanInputs.e ((q.2:ℝ)*(q.1:ℝ)*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2) := by
    unfold PRZZNegativeLocalRows.row signedRow
    simp_rw [hr]
    rw [← PRZZNuCoefficient.separate]
    apply sum_congr rfl
    intro i hi
    rw [← flip_sum d D H]
    apply sum_congr rfl
    intro q hq
    have hc : pairCoeff d a F1 F2 (reflect FM) alpha beta (-x) t i =
        pairCoeff d a F1 F2 FM alpha beta x t i := by simp [pairCoeff,reflect]
    have ho : PRZZNuCoefficient.oscillation (-x) (-y) (PRZZNegativeArithmetic.flip q) =
        PRZZKloostermanInputs.e ((q.2:ℝ)*x)*PRZZKloostermanInputs.e ((q.1:ℝ)*y/(2*Real.pi)) := by
      simp [PRZZNuCoefficient.oscillation,PRZZNegativeArithmetic.flip]
    have hp : -((freq (PRZZNegativeArithmetic.flip q):ℝ))*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2 =
        (q.2:ℝ)*(q.1:ℝ)*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2 := by
      simp [freq,PRZZNegativeArithmetic.flip]
    rw [hc,ho,hp]
  rw [hexp,hidx]
  simp only [product_eq_sprod,sum_product,mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro q hq
  simp only [amplitudeMinus,PRZZFilteredResidual.signedPrefactor,PRZZUnfrozenPoisson.arithmetic,
    pairCoeff,Int.cast_neg,Int.cast_natCast,neg_mul,neg_neg,div_eq_mul_inv,mul_inv_rev]
  ring

theorem row_localized (N d j l : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (p : ℝ × ℝ) (t : ℝ) :
    (∑ z ∈ rowIndices N d j l D H,
      localizedMinus N d T A B a F1 F2 FM W Phi alpha beta z p t) =
      (PRZZAStarWindow.window N T A B).indicator
        (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))) p *
      mellin Phi (t*I)*twist (p.1*p.2/T) t *
      PRZZNegativeLocalRows.row N d j l D H a F1 F2 FM alpha beta p.1 p.2 t := by
  by_cases hp : p ∈ PRZZAStarWindow.window N T A B
  · simp only [localizedMinus,PRZZActualMellin.localized,Set.indicator_of_mem hp]
    simp_rw [show ∀ z : Index, modulation z p.1 *
        (amplitude d a F1 F2 FM W alpha beta p.1 p.2 z*mellin Phi (t*I)*
          (twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t)) =
        amplitudeMinus d a F1 F2 FM W alpha beta p.1 p.2 z*mellin Phi (t*I)*
          (twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t) by
        intro z; rw [← amplitude_modulation]; ring]
    have he := row_amplitude N d j l D H a F1 F2 FM W alpha beta p.1 p.2 t
    calc
      _ = (mellin Phi (t*I)*twist (p.1*p.2/T) t)*
          ∑ z ∈ rowIndices N d j l D H,
            amplitudeMinus d a F1 F2 FM W alpha beta p.1 p.2 z*twist z.1.1 t*twist z.1.2 t := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = _ := by rw [he]; ring
  · simp [localizedMinus,PRZZActualMellin.localized,hp]


theorem row_integral_bound (N d j l : ℕ) (D H T M B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) (hB : 0 ≤ B)
    (hb : ∀ p ∈ PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l), ∀ t : ℝ,
      ‖PRZZNegativeLocalRows.row N d j l D H a F1 F2 FM alpha beta p.1 p.2 t‖ ≤ B*(1+|t|)) :
    ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        W (alpha+beta) p‖)*B*(∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let s := PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l)
  let c := PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l) W (alpha+beta)
  let f := fun p t => s.indicator (fun p =>
    ∑ z ∈ rowIndices N d j l D H,
      localizedMinus N d T (M/2) (3*M) a F1 F2 FM W Phi alpha beta z p t) p
  have hc : Integrable c := PRZZDyadicEnvelope.common_integrable d T M _ _ W (alpha+beta)
    hd hT hM (by positivity) (by positivity) hW
  have hm : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hpoint (p : ℝ × ℝ) (t : ℝ) :
      ‖f p t‖ ≤ ‖c p‖*B*((1+|t|)*‖mellin Phi (t*I)‖) := by
    by_cases hp : p ∈ s
    · dsimp only [f]
      rw [Set.indicator_of_mem hp,row_localized]
      by_cases hw : p ∈ PRZZAStarWindow.window N T (M/2) (3*M)
      · rw [Set.indicator_of_mem hw]
        have hx : 0 < p.1 := (show 0 < M/(4*(2:ℝ)^l) by positivity).trans_le hp.1.1
        have hy : 0 < p.2 := (show 0 < T/(12*M*(2:ℝ)^j) by positivity).trans_le hp.2.1
        simp only [norm_mul,twist_norm _ _ (div_pos (mul_pos hx hy) hT),mul_one]
        have hh := mul_le_mul_of_nonneg_left (hb p hp t)
          (mul_nonneg (norm_nonneg (W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))))
            (norm_nonneg (mellin Phi (t*I))))
        have hp' : p ∈ PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l) := hp
        dsimp only [c,PRZZDyadicEnvelope.common]
        rw [Set.indicator_of_mem hp']
        exact hh.trans_eq (by ring)
      · simp only [Set.indicator_of_notMem hw,zero_mul,norm_zero]
        positivity
    · simp only [f,Set.indicator_of_notMem hp,norm_zero]
      positivity
  have hinner (t : ℝ) : ‖∫ p, f p t‖ ≤
      (∫ p, ‖c p‖)*B*((1+|t|)*‖mellin Phi (t*I)‖) := by
    have hh := norm_integral_le_of_norm_le
      ((hc.norm.mul_const B).mul_const ((1+|t|)*‖mellin Phi (t*I)‖))
      (Filter.Eventually.of_forall (fun p => hpoint p t))
    simpa only [integral_mul_const] using hh
  have hout := norm_integral_le_of_norm_le
    (hm.const_mul ((∫ p, ‖c p‖)*B)) (Filter.Eventually.of_forall hinner)
  rw [row_iterated_eq N d j l D H T M a F1 F2 FM W Phi alpha beta hT hM hFM hW hPhi.continuous hsM hsP,
    row_mellin_window N d j l D H T M a F1 F2 FM W Phi alpha beta hN hT hM hFM hW hPhi hsM hsP]
  change ‖(1/(2*Real.pi):ℂ)*(∫ t, ∫ p, f p t)‖ ≤ _
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]]
  exact (mul_le_mul_of_nonneg_left hout (by positivity)).trans_eq (by rw [integral_const_mul]; ring)


/-- The actual modulated row integral with the uniform Weil/DI row budget
substituted. Constants precede the two profile scales and all row data. -/
theorem row_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (hsM : Function.support FM ⊆ Icc (1/2:ℝ) 3) :
    ∃ caps : (List ℕ × List ℕ) → PRZZActualAggregate.Caps,
      ∃ w : (List ℕ × List ℕ) → ℝ, ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 M : ℝ, ∀ N d j l : ℕ, ∀ T Q D H : ℝ, ∀ alpha beta sigma : ℂ,
      ∀ Phi : ℝ → ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      0 < M → sigma ≠ 0 →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 Q2) (scaledCutoff FM M)
        (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        (PRZZDyadicEnvelope.sourceW sigma) (alpha+beta) p‖)*
        PRZZRowIntegralBudget.rowBudget C w caps js eps eta b T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C,hC,hw,hrow⟩ := PRZZNegativeLocalRows.row_uniform
    hWeil hDI K hK js eps eta b S Z heps heta hb hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 M N d j l T Q D H alpha beta sigma Phi hN hd hT hNT hdT hlog hM0 hsigma
    hfreq ha hz hbShift hPhi hsPhi
  apply row_integral_bound N d j l D H T M _ _ _ _ _ _ _ _ _ hN hd (by linarith) hM0
    (hM.comp (continuous_const.mul continuous_id))
    (PRZZSourceWOuter.sourceW_continuous sigma hsigma) hPhi
    (PRZZWindowScaleSupply.scaled_support FM M hM0 hsM) hsPhi
  · exact PRZZRowIntegralBudget.rowBudget_nonneg C w caps js eps eta b T _ N d K j l
      hC.le (fun q => (hw q).le) (by linarith) (by positivity)
  · intro p hp t
    exact hrow Q2 M N d j l T Q D H p.1 p.2 t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hbShift

#print axioms row_weil_di
#print axioms row_amplitude
#print axioms row_localized
#print axioms row_integral_bound
end XiPrime8845.PRZZNegativeRowIntegral

