import PRZZZeroFourierReduction
import PRZZWRowReindex

/-! The original complete nonzero-gap row family, before any analytic
discard. Both sharp AFE cutoffs, signed gaps and all original coefficients
are retained. The Gamma-weighted second branch is not replaced by a power. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set Finset
namespace XiPrime8845.PRZZAllOffDiagonalRows
open PRZZAFEIndices PRZZWRowLimit PRZZWRowReindex PRZZL1Finite
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def rows (L N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ labels L N,
    if z.2.1 ≠ 0 then literalRows L N F s z a F1 F2 alpha beta t else 0

def selected (L N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ labels L N,
    if z.2.1 ≠ 0 ∧ R s z then literalRows L N F s z a F1 F2 alpha beta t else 0

theorem exhaustive (L N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    rows L N F F1 F2 a alpha beta t =
      selected L N F F1 F2 a R alpha beta t+
      selected L N F F1 F2 a (fun s z => ¬R s z) alpha beta t := by
  unfold rows selected
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro z hz
  by_cases hg : z.2.1 ≠ 0 <;> by_cases hr : R s z <;> simp [hg,hr]

theorem original_field (L N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)] (alpha beta : ℂ) (t : ℝ) :
    complete L N F R (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t-
      PRZZWRowLimit.diagonal L N F (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t =
      rows L N F F1 F2 a alpha beta t := by
  unfold complete PRZZWRowLimit.diagonal retained complement rows
  simp only [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro z hz
  have he := row_reindex L N s z F F1 F2 a alpha beta t
  by_cases hg : z.2.1 = 0 <;> by_cases hr : R s z <;> simp [hg,hr,he]

theorem term_continuous (a b : ℕ → ℂ) (alpha beta : ℂ) (hs : alpha+beta ≠ 0)
    (m k n r : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (T : ℝ) (hT : 0 < T) :
    ContinuousOn (fun t => term a b alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
      t m k n r) (Icc T (2*T)) := by
  have hw : ContinuousOn (fun t : ℝ => PRZZActualDirectSum.mainWeight alpha beta (m*k) t)
      (Icc T (2*T)) := by
    rw [weight_eq]
    apply (PRZZSourceWOuter.sourceW_continuous (alpha+beta) hs).comp
    · fun_prop (disch := intro t ht; have ht0 := hT.trans_le ht.1; positivity)
    · intro t ht
      have ht0 := hT.trans_le ht.1
      exact div_pos (by positivity) ht0
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold term directTerm
  simp_rw [Complex.cpow_def_of_ne_zero hm0,Complex.cpow_def_of_ne_zero hk0,
    Complex.cpow_def_of_ne_zero hn0,Complex.cpow_def_of_ne_zero hr0]
  have hd : Continuous (fun t : ℝ =>
      Complex.exp (Complex.log (m:ℂ)*(1/2+alpha+(t:ℂ)*I))*
      Complex.exp (Complex.log (k:ℂ)*(1/2+beta-(t:ℂ)*I))) := by fun_prop
  have hn' : Continuous (fun t : ℝ => a n/Complex.exp (Complex.log (n:ℂ)*(1/2+(t:ℂ)*I))) := by
    fun_prop (disch := intros; simp)
  have hr' : Continuous (fun t : ℝ => star (b r/Complex.exp (Complex.log (r:ℂ)*(1/2+(t:ℂ)*I)))) := by
    fun_prop (disch := intros; simp)
  exact ((hw.div hd.continuousOn (by intros; simp)).mul hn'.continuousOn).mul hr'.continuousOn

theorem row_continuous (L N s : ℕ) (F : ℝ → ℂ) (z : Label) (a b : ℕ → ℂ)
    (alpha beta : ℂ) (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (fun t => row L N F s z a b alpha beta t) (Icc T (2*T)) := by
  have he (t : ℝ) : row L N F s z a b alpha beta t =
      ∑ i ∈ fibre L N z, PRZZAFEProgression.piece F ((2:ℝ)^s) i.1.1*
        term a b alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
          t i.1.1 i.1.2 i.2.1 i.2.2 := by
    symm
    exact PRZZExplicitDomain.fibre_explicit L N z _
  simp_rw [he]
  apply continuousOn_finsetSum
  intro i hi
  have hidx := (mem_filter.mp hi).1
  have hp := mem_product.mp hidx
  have hmk := mem_product.mp hp.1
  have hnr := mem_product.mp hp.2
  exact (term_continuous a b alpha beta hs _ _ _ _
    (mem_Icc.mp hmk.1).1 (mem_Icc.mp hmk.2).1
    (mem_Icc.mp hnr.1).1 (mem_Icc.mp hnr.2).1 T hT).const_mul _

theorem complete_continuous (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)] (a b : ℕ → ℂ)
    (alpha beta : ℂ) (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (complete L N F R a b alpha beta) (Icc T (2*T)) ∧
      ContinuousOn (PRZZWRowLimit.diagonal L N F a b alpha beta) (Icc T (2*T)) := by
  have hrow := row_continuous L N
  have hd : ContinuousOn (PRZZWRowLimit.diagonal L N F a b alpha beta) (Icc T (2*T)) := by
    unfold PRZZWRowLimit.diagonal
    apply continuousOn_finsetSum
    intro s hss
    apply continuousOn_finsetSum
    intro z hz
    by_cases hg : z.2.1 = 0
    · simp only [if_pos hg]; exact hrow s F z a b alpha beta hs T hT
    · simp only [if_neg hg]; exact continuousOn_const
  refine ⟨?_,hd⟩
  unfold complete
  apply ContinuousOn.add (ContinuousOn.add hd ?_) ?_ <;>
    first | unfold retained | unfold complement
  all_goals
    apply continuousOn_finsetSum
    intro s hss
    apply continuousOn_finsetSum
    intro z hz
    split_ifs
    · exact hrow s F z a b alpha beta hs T hT
    · exact continuousOn_const

/-- Both original time integrals, with the actual dual Gamma quotient. -/
theorem offDiagonal_reindex (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)] (a : ℕ → ℂ)
    (alpha beta : ℂ) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    PRZZCoupledAFE.offDiagonalPair L N F R a alpha beta T phi =
      (∫ t in Icc T (2*T), phi t*rows L N F (fun _ => 1) (fun _ => 1) a alpha beta t)+
      ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
        rows L N F (fun _ => 1) (fun _ => 1) a (-beta) (-alpha) t := by
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hc := complete_continuous L N F R a a alpha beta hs T hT
  have hc' := complete_continuous L N F R a a (-beta) (-alpha) hs' T hT
  have ar := abs_le.mp ((abs_re_le_norm alpha).trans ha)
  have br := abs_le.mp ((abs_re_le_norm beta).trans hb)
  have hg := PRZZMollifiedTime.dualMultiplier_continuous alpha beta
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have h1 : IntegrableOn (fun t : ℝ => phi t*complete L N F R a a alpha beta t) (Icc T (2*T)) :=
    (hp.continuousOn.mul hc.1).integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun t : ℝ => phi t*PRZZWRowLimit.diagonal L N F a a alpha beta t) (Icc T (2*T)) :=
    (hp.continuousOn.mul hc.2).integrableOn_compact isCompact_Icc
  have h3 : IntegrableOn (fun t : ℝ => (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      complete L N F R a a (-beta) (-alpha) t) (Icc T (2*T)) :=
    ((hp.mul hg).continuousOn.mul hc'.1).integrableOn_compact isCompact_Icc
  have h4 : IntegrableOn (fun t : ℝ => (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      PRZZWRowLimit.diagonal L N F a a (-beta) (-alpha) t) (Icc T (2*T)) :=
    ((hp.mul hg).continuousOn.mul hc'.2).integrableOn_compact isCompact_Icc
  unfold PRZZCoupledAFE.offDiagonalPair PRZZWRowLimit.twoSided PRZZCoupledAFE.diagonalPair
  rw [show forall x y z w : ℂ, (x+y)-(z+w)=(x-z)+(y-w) by intros; ring]
  rw [← integral_sub h1 h2,← integral_sub h3 h4]
  have hl : PRZZWRowReindex.leftCoefficient a (fun _ => 1) = a := by
    funext n; simp [PRZZWRowReindex.leftCoefficient]
  have hr : PRZZWRowReindex.rightCoefficient a (fun _ => 1) = a := by
    funext n; simp [PRZZWRowReindex.rightCoefficient]
  have he1 (t : ℝ) := original_field L N F (fun _ => 1) (fun _ => 1) a R alpha beta t
  have he2 (t : ℝ) := original_field L N F (fun _ => 1) (fun _ => 1) a R (-beta) (-alpha) t
  simp only [hl,hr] at he1 he2
  congr 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [← mul_sub,he1 t]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [← mul_sub,he2 t]

#print axioms exhaustive
#print axioms original_field
#print axioms term_continuous
#print axioms row_continuous
#print axioms complete_continuous
#print axioms offDiagonal_reindex
end XiPrime8845.PRZZAllOffDiagonalRows
