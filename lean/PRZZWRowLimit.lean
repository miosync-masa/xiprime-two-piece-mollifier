import PRZZAFEOuterAssembly
import PRZZWArithmeticCutoff
import PRZZIntegratedDefect

/-! Cutoff removal for the complete literal W row partition. Diagonal,
retained off-diagonal and complementary rows are all kept, on both AFE
branches. This does not estimate the complementary rows or identify the
retained central Fourier sum with the final A* expression. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set MeasureTheory Filter Topology Complex
namespace XiPrime8845.PRZZWRowLimit
open PRZZAFEIndices PRZZQuotientMass PRZZL1Finite PRZZActualDirectSum
set_option maxHeartbeats 5000000

/-- The profile used by the literal telescoping spatial partition. -/
def profile (F : ℝ → ℂ) (x : ℝ) : ℂ := F (x/2)-F x

theorem profile_piece (F : ℝ → ℂ) (M x : ℝ) :
    PRZZAFEProgression.piece F M x = profile F (M⁻¹*x) := by
  simp [PRZZAFEProgression.piece,profile,div_eq_mul_inv,mul_inv_rev,
    mul_comm,mul_left_comm,mul_assoc]

/-- The same seed supplies the smooth compact profile required by the
actual Poisson row-error theorem, rather than an unrelated test weight. -/
theorem profile_regular (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0) :
    ContDiff ℝ ∞ (profile F) ∧ HasCompactSupport (profile F) ∧
      Function.support (profile F) ⊆ Icc (1/2:ℝ) 3 := by
  have hs : Function.support (profile F) ⊆ Icc (1/2:ℝ) 3 := by
    intro x hx
    by_contra hn
    have hx' : profile F x ≠ 0 := hx
    simp only [Set.mem_Icc,not_and_or,not_le] at hn
    rcases hn with h | h
    · exact hx' (by unfold profile; rw [hlo (x/2) (by linarith),hlo x (by linarith)]; ring)
    · exact hx' (by unfold profile; rw [hhi (x/2) (by linarith),hhi x (by linarith)]; ring)
  refine ⟨?_,?_,hs⟩
  · exact (hf.comp (contDiff_id.div_const (2:ℝ))).sub hf
  · change IsCompact (closure (Function.support (profile F)))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

def row (L N : ℕ) (F : ℝ → ℂ) (k : ℕ) (z : Label)
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ PRZZExplicitDomain.domain L N z,
    PRZZAFEProgression.piece F ((2:ℝ)^k) p.1 *
      term c e a b (mainWeight a b) t
        (restore z p).1.1 (restore z p).1.2 (restore z p).2.1 (restore z p).2.2

def diagonal (L N : ℕ) (F : ℝ → ℂ) (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (L+2), ∑ z ∈ labels L N,
    if z.2.1 = 0 then row L N F k z c e a b t else 0

def retained (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ k ∈ range (L+2), ∑ z ∈ labels L N,
    if z.2.1 ≠ 0 ∧ R k z then row L N F k z c e a b t else 0

def complement (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ k ∈ range (L+2), ∑ z ∈ labels L N,
    if z.2.1 ≠ 0 ∧ ¬R k z then row L N F k z c e a b t else 0

def complete (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) : ℂ :=
  diagonal L N F c e a b t + retained L N F R c e a b t +
    complement L N F R c e a b t

theorem cover (L : ℕ) : (L:ℝ) ≤ (2:ℝ)^(L+2)/2 := by
  have h : (L:ℝ) ≤ (2:ℝ)^L := by
    induction L with
    | zero => norm_num
    | succ L ih =>
      push_cast
      rw [pow_succ]
      have hp : 1 ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num)
      linarith
  rw [pow_add]
  norm_num
  linarith

/-- No row is dropped or counted twice, for any retained-domain test. -/
theorem complete_eq (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) :
    complete L N F R c e a b t = directSum L a b (mainWeight a b) t *
      PRZZ.dirichletPolynomial c N (1/2+t*I) *
      star (PRZZ.dirichletPolynomial e N (1/2+t*I)) := by
  classical
  rw [PRZZAFEOuterAssembly.literal_partition L N (L+2) F 1
    (by norm_num) le_rfl (by simpa using cover L) hlo hhi]
  unfold complete diagonal retained complement row
  simp only [mul_one, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro z hz
  by_cases hd : z.2.1 = 0 <;> by_cases hr : R k z <;> simp [hd,hr]

theorem complete_cutoff_removed (N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (c e : ℕ → ℂ) (a b : ℂ) (hs : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T), phi t*complete L N F R c e a b t)
      atTop (𝓝 (∫ t in Icc T (2*T),
        PRZZMollifiedTime.mollifierWeight phi c e N t * PRZZIntegratedDefect.mainSeries a b t)) := by
  have he (L : ℕ) : (fun t => phi t*complete L N F R c e a b t) =
      (fun t => PRZZMollifiedTime.mollifierWeight phi c e N t*
        directSum L a b (PRZZWArithmeticCutoff.kernel (a+b)) t) := by
    funext t
    rw [complete_eq L N F R hlo hhi]
    unfold PRZZMollifiedTime.mollifierWeight
    change _ = phi t * _ * _ * directSum L a b (mainWeight a b) t
    ring
  simp_rw [he]
  exact PRZZWArithmeticCutoff.mollified_cutoff_removed a b hs ha hb T hT phi hp c e N

/-- Absolute summability supplies time integrability of the original W
series; no integrability premise on a Poisson expression is introduced. -/
theorem main_integrable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun t => w t*PRZZIntegratedDefect.mainSeries a b t) (Icc T (2*T)) := by
  let f := fun p : ℕ × ℕ => fun t : ℝ =>
    directTerm a b (mainWeight a b) t (p.1+1) (p.2+1)
  let D := PRZZWArithmeticCutoff.decayConstant (a+b)*(T/Real.pi)^2
  let g := fun p : ℕ × ℕ => D*(((p.1:ℝ)+1)^(-2:ℝ)*((p.2:ℝ)+1)^(-2:ℝ))
  have hn : Summable (fun n : ℕ => ((n:ℝ)+1)^(-2:ℝ)) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (by norm_num : (-2:ℝ) < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hg : Summable g := (hn.mul_of_nonneg hn (by intro n; positivity)
    (by intro n; positivity)).mul_left D
  have ar := (abs_le.mp ((Complex.abs_re_le_norm a).trans ha)).1
  have br := (abs_le.mp ((Complex.abs_re_le_norm b).trans hb)).1
  have hm (p : ℕ × ℕ) : AEStronglyMeasurable (f p) (volume.restrict (Icc T (2*T))) :=
    PRZZWArithmeticCutoff.term_measurable a b hs T hT _ _ (by omega) (by omega)
  have hsum : AEStronglyMeasurable (fun t => ∑' p, f p t) (volume.restrict (Icc T (2*T))) := by
    refine ⟨fun t => ∑' p, (hm p).mk (f p) t,
      StronglyMeasurable.tsum (fun p => (hm p).stronglyMeasurable_mk),?_⟩
    filter_upwards [ae_all_iff.mpr (fun p => (hm p).ae_eq_mk)] with t ht
    exact tsum_congr (fun p => ht p)
  have hi : IntegrableOn (fun t => ‖w t‖*(∑' p, g p)) (Icc T (2*T)) :=
    (hw.norm.mul continuous_const).integrableOn_Icc
  apply hi.mono' (hw.aestronglyMeasurable.mul hsum)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [Pi.mul_apply]
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hf := main_summable a b ha hb hs t (hT.trans_le ht.1)
  apply (norm_tsum_le_tsum_norm hf.norm).trans
  apply hf.norm.tsum_le_tsum _ hg
  intro p
  have hbound := PRZZWArithmeticCutoff.arithmetic_bound a b hs (by linarith) (by linarith)
    T t hT ht (p.1+1) (p.2+1) (by omega) (by omega)
  dsimp [f,g,D,directTerm,mainWeight,PRZZWArithmeticCutoff.kernel] at hbound ⊢
  simpa only [Nat.cast_add,Nat.cast_one] using hbound

def twoSided (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (c e : ℕ → ℂ) (a b : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Icc T (2*T), phi t*complete L N F R c e a b t) +
    (∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier a b t)*
      complete L N F R c e (-b) (-a) t)

/-- The error against the complete finite row family tends to the single
original AFE defect integral, with the genuine dual Gamma multiplier. -/
theorem afe_error_limit (N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (c e : ℕ → ℂ) (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    Tendsto (fun L : ℕ =>
      (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
        (riemannZeta (PRZZAFEDual.leftArg a t)*riemannZeta (PRZZAFEDual.rightArg b t))) -
        twoSided L N F R c e a b T phi) atTop
      (𝓝 (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
        PRZZIntegratedDefect.defect a b t)) := by
  have ar := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  have hc := PRZZMollifiedTime.dualMultiplier_continuous a b
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hs' : -b + -a ≠ 0 := by
    rw [show -b + -a = -(a+b) by ring]; exact neg_ne_zero.mpr hs
  have hm := complete_cutoff_removed N F R hlo hhi c e a b hs
    (by linarith [ar.1]) (by linarith [br.1]) T hT phi hp
  have hd := complete_cutoff_removed N F R hlo hhi c e (-b) (-a) hs'
    (by simp; linarith [br.2]) (by simp; linarith [ar.2]) T hT
    (fun t => phi t*PRZZAFEDual.dualMultiplier a b t) (hp.mul hc)
  have hw := PRZZMollifiedTime.mollifierWeight_continuous phi hp c e N
  have hmw : PRZZMollifiedTime.mollifierWeight (fun t => phi t*PRZZAFEDual.dualMultiplier a b t) c e N =
      (fun t => PRZZMollifiedTime.mollifierWeight phi c e N t*PRZZAFEDual.dualMultiplier a b t) := by
    funext t; unfold PRZZMollifiedTime.mollifierWeight; ring
  rw [hmw] at hd
  have hz : IntegrableOn (fun t => PRZZMollifiedTime.mollifierWeight phi c e N t *
      (riemannZeta (PRZZAFEDual.leftArg a t)*riemannZeta (PRZZAFEDual.rightArg b t)))
      (Icc T (2*T)) :=
    (hw.mul (PRZZIntegratedDefect.zeta_continuous a b ha hb)).integrableOn_Icc
  have hi := main_integrable a b ha hb hs T hT _ hw
  have hj := main_integrable (-b) (-a) (by simpa using hb) (by simpa using ha) hs' T hT _ (hw.mul hc)
  simp only [Pi.mul_apply] at hj
  have he : (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
      PRZZIntegratedDefect.defect a b t) =
      (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
        (riemannZeta (PRZZAFEDual.leftArg a t)*riemannZeta (PRZZAFEDual.rightArg b t))) -
      ((∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t*PRZZIntegratedDefect.mainSeries a b t)+
       (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t*
        PRZZAFEDual.dualMultiplier a b t*PRZZIntegratedDefect.mainSeries (-b) (-a) t)) := by
    have hsub := integral_sub hz (hi.add hj)
    have hadd := integral_add hi hj
    dsimp only [Pi.add_apply,Pi.sub_apply] at hsub hadd
    calc
      _ = ∫ t in Icc T (2*T),
          PRZZMollifiedTime.mollifierWeight phi c e N t *
            (riemannZeta (PRZZAFEDual.leftArg a t)*riemannZeta (PRZZAFEDual.rightArg b t)) -
          (PRZZMollifiedTime.mollifierWeight phi c e N t*PRZZIntegratedDefect.mainSeries a b t +
           PRZZMollifiedTime.mollifierWeight phi c e N t*PRZZAFEDual.dualMultiplier a b t*
            PRZZIntegratedDefect.mainSeries (-b) (-a) t) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        unfold PRZZIntegratedDefect.defect
        ring
      _ = _ := hsub.trans (by rw [hadd])
  rw [he]
  exact tendsto_const_nhds.sub (hm.add hd)

/-- The complete row-error limit inherits the proved sharp AFE defect
budget. The row partition is still complete: no complementary term has
silently been declared negligible or replaced by A*. -/
theorem scaled_afe_error_limit_bound
    (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (js : List ℕ) (S r delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ∃ E : ℂ, E = (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
          PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) ∧
      Tendsto (fun L : ℕ =>
        (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
            (riemannZeta (PRZZAFEDual.leftArg (A/(Real.log T:ℂ)) t)*
             riemannZeta (PRZZAFEDual.rightArg (B/(Real.log T:ℂ)) t))) -
        twoSided L N F R (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hd
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T h hsmall
  intro A B hA hB hsep N hN hNT phi P hp hP hphi
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL.ne')
  refine ⟨_,rfl,?_,h A B hA hB hsep N hN hNT phi P hp hP hphi⟩
  exact afe_error_limit N F R hlo hhi _ _ _ _ (hsmall.2 A hA) (hsmall.2 B hB)
    hs T (by
      have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
      linarith) phi hp

#print axioms cover
#print axioms profile_piece
#print axioms profile_regular
#print axioms complete_eq
#print axioms complete_cutoff_removed
#print axioms main_integrable
#print axioms afe_error_limit
#print axioms scaled_afe_error_limit_bound
end XiPrime8845.PRZZWRowLimit
