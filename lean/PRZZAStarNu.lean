import PRZZAStarTransform
import PRZZNuCoefficient
import PRZZNuBounds

/-! The actual localized A* transform with its signed frequency coefficient.
All original strict cutoffs remain in the frequency set. The DI adapter
below supplies nu's envelope on a rectangle; decomposition of the full
arithmetic coefficient into such rectangles is not asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZAStarNu
open PRZZAStar PRZZAStarMellin PRZZActualMellin PRZZMellinSeparation PRZZNuCoefficient
set_option maxHeartbeats 2000000

def pairs (N d : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N).product (Icc 1 N)).filter
    (fun z => z.1.Coprime z.2 ∧ d*z.1 ≤ N ∧ d*z.2 ≤ N)

def frequencies (d : ℕ) (D H : ℝ) : Finset (ℤ × ℕ) :=
  ((Icc (-⌈D/d⌉) ⌈D/d⌉).filter
    (fun Δ : ℤ => 0 < |(Δ:ℝ)| ∧ |(Δ:ℝ)| < D/d)).product
    ((Icc 1 ⌊H⌋₊).filter (fun h => (h:ℝ) < H))

def pairCoeff (d : ℕ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (i : ℕ × ℕ) : ℂ :=
  (a (d*i.1)*F1 (d*i.1)/(i.1:ℂ)^α*twist i.1 t)*
  (star (a (d*i.2))*F2 (d*i.2)*FM (x*i.2)/(i.2:ℂ)^β*twist i.2 t)

def signedSum (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x y t : ℝ) : ℂ :=
  ∑ k ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y k *
    ∑ i ∈ pairs N d, pairCoeff d a F1 F2 FM α β x t i *
      PRZZKloostermanInputs.e (-(k:ℝ)*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2)

theorem amplitude_nu (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (α β : ℂ) (x y t : ℝ) :
    (∑ z ∈ indices N d D H, amplitude d a F1 F2 FM W α β x y z *
      twist z.1.1 t*twist z.1.2 t) =
      (W (2*Real.pi*x/y)/((d:ℂ)*(x:ℂ)^(α+β)))*
        signedSum N d D H a F1 F2 FM α β x y t := by
  unfold signedSum
  rw [← PRZZNuCoefficient.separate]
  change (∑ z ∈ (pairs N d).product (frequencies d D H), _) = _
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  simp only [amplitude,prefactor,outerKernel,pairCoeff,PRZZNuCoefficient.oscillation,freq,
    Int.cast_mul,Int.cast_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

theorem localized_nu (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (p : ℝ × ℝ) (t : ℝ) :
    (∑ z ∈ indices N d D H, localized N d T A B a F1 F2 FM W Phi α β z p t) =
      (PRZZAStarWindow.window N T A B).indicator
        (fun p : ℝ × ℝ => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(α+β))) p *
      mellin Phi (t*I)*twist (p.1*p.2/T) t *
      signedSum N d D H a F1 F2 FM α β p.1 p.2 t := by
  by_cases hp : p ∈ PRZZAStarWindow.window N T A B
  · simp only [localized,Set.indicator_of_mem hp]
    have he : (∑ z ∈ indices N d D H,
        amplitude d a F1 F2 FM W α β p.1 p.2 z * mellin Phi (t*I) *
          (twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t)) =
        (mellin Phi (t*I)*twist (p.1*p.2/T) t)*
          ∑ z ∈ indices N d D H, amplitude d a F1 F2 FM W α β p.1 p.2 z*
            twist z.1.1 t*twist z.1.2 t := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    rw [he,amplitude_nu]
    ring
  · simp [localized,hp]

theorem literal_mellin_nu (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (PRZZAStarWindow.window N T A B).indicator
          (fun p : ℝ × ℝ => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(α+β))) p *
        mellin Phi (t*I)*twist (p.1*p.2/T) t *
        signedSum N d D H a F1 F2 FM α β p.1 p.2 t := by
  rw [PRZZAStarTransform.literal_mellin N d D H T A B a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hT hA hB]
  simp_rw [localized_nu]

theorem frequency_positive_h (d : ℕ) (D H : ℝ) (q : ℤ × ℕ)
    (hq : q ∈ frequencies d D H) : 0 < q.2 := by
  have hh := (mem_Icc.mp (mem_filter.mp (mem_product.mp hq).2).1).1
  omega

theorem frequency_ne_zero (d : ℕ) (D H : ℝ) (k : ℤ)
    (hk : k ∈ (frequencies d D H).image freq) : k ≠ 0 := by
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hk
  apply mul_ne_zero
  · exact_mod_cast (frequency_positive_h d D H q hq).ne'
  · have hh := (mem_filter.mp (mem_product.mp hq).1).2.1
    intro he
    simp [he] at hh

/-- The divisor bound applies to every actual signed source frequency. -/
theorem source_nu_bound (d : ℕ) (D H x y : ℝ) (k : ℤ)
    (hk : k ∈ (frequencies d D H).image freq) :
    ‖nu (frequencies d D H) x y k‖ ≤ (k.natAbs.divisors.card:ℝ) :=
  nu_norm_le_divisors _ _ _ _ (frequency_ne_zero d D H k hk)
    (frequency_positive_h d D H)

/-- DI applied to a separated positive-frequency rectangle with precisely
the nu appearing in literal_mellin_nu. The other three coefficient bounds
are still inputs; this does not replace the full pair domain by a rectangle. -/
theorem source_positive_rectangle_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (d : ℕ) (D H A E F V : ℝ),
      1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V → ∀ h : ℕ, 1 ≤ h →
      ∀ R S Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < Q → ∀ r beta alpha : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) →
      (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) → ∀ x y : ℝ,
      ‖PRZZSourceTypeII.sourceSum A E F V h d r beta
        (fun k => nu (frequencies d D H) x y k) alpha‖ ≤
        R*S*((C*A^η)*Q)*K*PRZZKloostermanInputs.diBound ε V F A E h := by
  obtain ⟨C,K,hC,hK,hbound⟩ := PRZZNuBounds.positive_rectangle_bound hDI ε η hε hη
  refine ⟨C,K,hC,hK,?_⟩
  intro d D H A E F V hA hE hF hV h hh R S Q hR hS hQ r beta alpha hr hb ha x y
  exact hbound (frequencies d D H) (frequency_positive_h d D H)
    A E F V hA hE hF hV h d hh R S Q hR hS hQ r beta alpha hr hb ha x y

#print axioms amplitude_nu
#print axioms localized_nu
#print axioms literal_mellin_nu
#print axioms frequency_positive_h
#print axioms frequency_ne_zero
#print axioms source_nu_bound
#print axioms source_positive_rectangle_bound
end XiPrime8845.PRZZAStarNu
