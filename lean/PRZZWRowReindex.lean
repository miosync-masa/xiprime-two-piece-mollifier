import PRZZWRowLimit
import PRZZActualPoissonError

/-! Literal reindexing from the original W labels to the sharp Poisson
rows. Original cutoff values and both sharp AFE bounds are retained.
The original label gap is the negative of the Poisson row's Delta. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZWRowReindex
open PRZZAFEIndices PRZZL1Finite PRZZActualDirectSum PRZZWRowLimit
set_option maxHeartbeats 6000000

theorem positive_int_sum (L : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc 1 L, f (n:ℤ)) = ∑ n ∈ Finset.Icc (1:ℤ) L, f n := by
  refine Finset.sum_bij (fun n _ => (n:ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
  · intro n hn m hm he
    exact_mod_cast he
  · intro m hm
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hm
    exact ⟨m.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,Int.toNat_of_nonneg (by omega)⟩
  · intro n hn
    rfl

def leftCoefficient (a : ℕ → ℂ) (F1 : ℝ → ℂ) (n : ℕ) : ℂ := a n*F1 n
def rightCoefficient (a : ℕ → ℂ) (F2 : ℝ → ℂ) (n : ℕ) : ℂ := a n*star (F2 n)

theorem term_cutoffs (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (V : ℕ → ℝ → ℂ) (t : ℝ) (m k n r : ℕ) :
    term (leftCoefficient a F1) (rightCoefficient a F2) alpha beta V t m k n r =
      F1 n*F2 r*term a a alpha beta V t m k n r := by
  simp [term,leftCoefficient,rightCoefficient,div_eq_mul_inv]
  ring

theorem weight_eq (alpha beta : ℂ) :
    mainWeight alpha beta = (fun (n : ℕ) (t : ℝ) => PRZZDyadicEnvelope.sourceW (alpha+beta)
      (2*Real.pi*(n:ℝ)/t)) := by
  funext n t
  unfold mainWeight
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

def pairMatches (z : Label) (n r : ℕ) : Prop :=
  Nat.gcd n r = z.1 ∧ Nat.log 2 (n/Nat.gcd n r) = z.2.2.1 ∧
    Nat.log 2 (r/Nat.gcd n r) = z.2.2.2

theorem label_iff (z : Label) (m k n r : ℕ) :
    label ((m,k),(n,r)) = z ↔ pairMatches z n r ∧
      (m:ℤ)*(n/Nat.gcd n r:ℕ)-(k:ℤ)*(r/Nat.gcd n r:ℕ) = z.2.1 := by
  rcases z with ⟨d,delta,j,l⟩
  simp only [label,pairMatches,Prod.mk.injEq]
  tauto

/-- A complete sharp Poisson row on one original mollifier pair. This
identity supplies the actual W argument, cutoffs and signed gap. -/
theorem pair_row (L n r s : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) (delta : ℤ) :
    (∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
      if (m:ℤ)*(n/Nat.gcd n r:ℕ)-(k:ℤ)*(r/Nat.gcd n r:ℕ) = delta then
        PRZZAFEProgression.piece F ((2:ℝ)^s) m *
          term (leftCoefficient a F1) (rightCoefficient a F2) alpha beta
            (mainWeight alpha beta) t m k n r else 0) =
    PRZZUnfrozenPoisson.afeRow L (profile F) F1 F2 ((2:ℝ)^s)
      ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta (alpha+beta) a (Nat.gcd n r) t := by
  have hn : Nat.gcd n r*(n/Nat.gcd n r) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hr : Nat.gcd n r*(r/Nat.gcd n r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
  have hn' : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by exact_mod_cast hn
  have hr' : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by exact_mod_cast hr
  unfold PRZZUnfrozenPoisson.afeRow
  rw [← positive_int_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← positive_int_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Int.toNat_natCast,Int.cast_natCast,neg_neg,hn,hr,hn',hr',profile_piece,weight_eq,term_cutoffs]
  split_ifs <;> ring

def literalRows (L N : ℕ) (F : ℝ → ℂ) (s : ℕ) (z : Label)
    (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    if pairMatches z n r then
      PRZZUnfrozenPoisson.afeRow L (profile F) F1 F2 ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-z.2.1,1)) alpha beta (alpha+beta) a (Nat.gcd n r) t
    else 0

/-- The original congruence-domain row is the sum of literal sharp
Poisson rows. No equality of phases or arithmetic coefficients is assumed. -/
theorem row_reindex (L N s : ℕ) (z : Label) (F F1 F2 : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    row L N F s z (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t =
      literalRows L N F s z a F1 F2 alpha beta t := by
  classical
  let f : PRZZAFEIndices.Index → ℂ := fun i =>
    PRZZAFEProgression.piece F ((2:ℝ)^s) i.1.1 *
      term (leftCoefficient a F1) (rightCoefficient a F2) alpha beta
        (mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2
  change (∑ p ∈ PRZZExplicitDomain.domain L N z, f (PRZZQuotientMass.restore z p)) = _
  rw [← PRZZExplicitDomain.fibre_explicit L N z f]
  unfold fibre
  rw [Finset.sum_filter]
  simp only [indices,Finset.sum_product,f]
  -- Move both original mollifier indices outside the two AFE indices.
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 L) (t := Finset.Icc 1 N)]
  unfold literalRows
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [label_iff]
  by_cases hpair : pairMatches z n r
  · simp only [hpair,true_and,if_true]
    exact pair_row L n r s F F1 F2 a alpha beta t z.2.1
  · simp [hpair]

/-- All three original label classes, including the diagonal and the
complement, now use the literal Poisson-row representation. -/
theorem complete_reindex (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    complete L N F R (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t =
      ∑ s ∈ Finset.range (L+2), ∑ z ∈ labels L N,
        literalRows L N F s z a F1 F2 alpha beta t := by
  classical
  unfold complete PRZZWRowLimit.diagonal retained complement
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd : z.2.1 = 0 <;> by_cases hr : R s z <;>
    simpa [hd,hr] using
        row_reindex L N s z F F1 F2 a alpha beta t

theorem literal_rows_cutoff_removed (N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (hab : alpha+beta ≠ 0)
    (ha : 0 ≤ 1/2+alpha.re) (hb : 0 ≤ 1/2+beta.re)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    Filter.Tendsto (fun L : ℕ => ∫ t in Icc T (2*T), phi t*
      ∑ s ∈ Finset.range (L+2), ∑ z ∈ labels L N,
        literalRows L N F s z a F1 F2 alpha beta t) Filter.atTop
      (nhds (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (leftCoefficient a F1) (rightCoefficient a F2) N t*
        PRZZIntegratedDefect.mainSeries alpha beta t)) := by
  have h := complete_cutoff_removed N F R hlo hhi (leftCoefficient a F1) (rightCoefficient a F2)
    alpha beta hab ha hb T hT phi hp
  simpa only [complete_reindex] using h

def nativeTwoSided (L N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Icc T (2*T), phi t*
    ∑ s ∈ Finset.range (L+2), ∑ z ∈ labels L N, literalRows L N F s z a F1 F2 alpha beta t) +
  (∫ t in Icc T (2*T), phi t*PRZZAFEDual.dualMultiplier alpha beta t*
    ∑ s ∈ Finset.range (L+2), ∑ z ∈ labels L N, literalRows L N F s z a F1 F2 (-beta) (-alpha) t)

/-- Both AFE branches now contain the actual sharp Poisson-row sums,
not a supplied decomposition. The complement and diagonal remain present. -/
theorem native_afe_error_limit (N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hab : alpha+beta ≠ 0)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    Filter.Tendsto (fun L : ℕ =>
      (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (leftCoefficient a F1) (rightCoefficient a F2) N t *
          (riemannZeta (PRZZAFEDual.leftArg alpha t)*riemannZeta (PRZZAFEDual.rightArg beta t))) -
        nativeTwoSided L N F F1 F2 a alpha beta T phi) Filter.atTop
      (nhds (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (leftCoefficient a F1) (rightCoefficient a F2) N t * PRZZIntegratedDefect.defect alpha beta t)) := by
  have h := afe_error_limit N F R hlo hhi (leftCoefficient a F1) (rightCoefficient a F2)
    alpha beta ha hb hab T hT phi hp
  simpa only [twoSided,complete_reindex,nativeTwoSided] using h

def pairBlock (L n r s : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) (delta : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
    if (m:ℤ)*(n/Nat.gcd n r:ℕ)-(k:ℤ)*(r/Nat.gcd n r:ℕ) = delta then
      PRZZAFEProgression.piece F ((2:ℝ)^s) m *
        term (leftCoefficient a F1) (rightCoefficient a F2) alpha beta
          (mainWeight alpha beta) t m k n r else 0

/-- The original pair block minus the actual central/tail/boundary
Poisson expression is exactly the already bounded native rowIntegral. -/
theorem pair_residual_eq (L J n r s : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (delta : ℤ) (T : ℝ) (phi : ℝ → ℂ) :
    (∫ t in Icc T (2*T), phi t*(pairBlock L n r s F F1 F2 a alpha beta t delta -
      PRZZActualPoissonError.poissonPart L J (profile F) ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta (alpha+beta)
        a (Nat.gcd n r) F1 F2 t)) =
    PRZZActualPoissonError.rowIntegral L J (profile F) ((2:ℝ)^s) T
      ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta (alpha+beta)
        a (Nat.gcd n r) F1 F2 phi := by
  unfold PRZZActualPoissonError.rowIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  unfold pairBlock
  rw [pair_row]

/-- The diagonal has no amplitude/phase freezing defect. This is not
an evaluation of its main term. -/
theorem diagonal_error_zero (L : ℕ) (F : ℝ → ℂ) (M : ℝ)
    (z : PRZZAStar.Index) (hz : z.2.1 = 0) (alpha beta sigma : ℂ) (t : ℝ) :
    PRZZUnfrozenPoisson.errorSum L F M z alpha beta sigma t = 0 := by
  simp [PRZZUnfrozenPoisson.errorSum,PRZZUnfrozenPoisson.errorTerm,hz,
    PRZZAmplitudeFreeze.error,PRZZPowerJets.power]

def reducePair (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (Nat.gcd p.1 p.2,p.1/Nat.gcd p.1 p.2,p.2/Nat.gcd p.1 p.2)

theorem reducePair_injective : Function.Injective reducePair := by
  intro p q he
  have hn := congrArg (fun z : ℕ × ℕ × ℕ => z.1*z.2.1) he
  have hr := congrArg (fun z : ℕ × ℕ × ℕ => z.1*z.2.2) he
  simp only [reducePair,Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)] at hn hr
  exact Prod.ext hn hr

/-- Original pairs and reduced coprime pairs are in bijection. This pays
no extra d or pair multiplicity and permits the full analytic summand. -/
theorem gcd_sum {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → ℕ → ℕ → E) :
    (∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      f (Nat.gcd n r) (n/Nat.gcd n r) (r/Nat.gcd n r)) =
    ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N then f d u v else 0 := by
  classical
  let src := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let dst := ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))).filter
    (fun z : ℕ × ℕ × ℕ => Nat.Coprime z.2.1 z.2.2 ∧ z.1*z.2.1 ≤ N ∧ z.1*z.2.2 ≤ N)
  have he : (∑ p ∈ src, f (reducePair p).1 (reducePair p).2.1 (reducePair p).2.2) =
      ∑ z ∈ dst, f z.1 z.2.1 z.2.2 := by
    refine Finset.sum_bij (fun p _ => reducePair p) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hn,hr⟩ := Finset.mem_product.mp hp
      have hn0 : 0 < p.1 := (Finset.mem_Icc.mp hn).1
      have hr0 : 0 < p.2 := (Finset.mem_Icc.mp hr).1
      have hd : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hn0
      have hdu := Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
      have hdv := Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
      apply Finset.mem_filter.mpr
      refine ⟨?_,?_⟩
      · apply Finset.mem_product.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hd,(Nat.gcd_le_left p.2 hn0).trans (Finset.mem_Icc.mp hn).2⟩,?_⟩
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.gcd_le_left p.2 hn0) hd,
          (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hn).2⟩,
          Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.gcd_le_right p.1 hr0) hd,
          (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hr).2⟩⟩
      · exact ⟨Nat.coprime_div_gcd_div_gcd hd,
          by simpa only [reducePair,hdu] using (Finset.mem_Icc.mp hn).2,
          by simpa only [reducePair,hdv] using (Finset.mem_Icc.mp hr).2⟩
    · intro p hp q hq he
      exact reducePair_injective he
    · intro z hz
      obtain ⟨hz,hcop,hun,hvn⟩ := Finset.mem_filter.mp hz
      obtain ⟨hd,hrest⟩ := Finset.mem_product.mp hz
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hrest
      have hd0 : 0 < z.1 := (Finset.mem_Icc.mp hd).1
      have hu0 : 0 < z.2.1 := (Finset.mem_Icc.mp hu).1
      have hv0 : 0 < z.2.2 := (Finset.mem_Icc.mp hv).1
      refine ⟨(z.1*z.2.1,z.1*z.2.2),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd0 hu0,hun⟩,
          Finset.mem_Icc.mpr ⟨Nat.mul_pos hd0 hv0,hvn⟩⟩
      · have hg : Nat.gcd (z.1*z.2.1) (z.1*z.2.2) = z.1 := by
          rw [Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
        simp [reducePair,hg,hd0.ne']
    · intro p hp
      rfl
  simpa only [src,dst,Finset.sum_filter,Finset.sum_product,reducePair] using he

#print axioms positive_int_sum
#print axioms term_cutoffs
#print axioms weight_eq
#print axioms label_iff
#print axioms pair_row
#print axioms row_reindex
#print axioms complete_reindex
#print axioms literal_rows_cutoff_removed
#print axioms native_afe_error_limit
#print axioms pair_residual_eq
#print axioms diagonal_error_zero
#print axioms reducePair_injective
#print axioms gcd_sum
end XiPrime8845.PRZZWRowReindex
