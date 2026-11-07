import PRZZOriginalDiagonal

/-! Sharp AFE reduction with signed diagonal Mellin corrections retained.
The full off-diagonal has not been identified with its zero Fourier main
term and nonzero A* remainder. No such identification or estimate is a
premise here, and this is not the completed PRZZ moment asymptotic. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Finset Set Filter Topology
namespace XiPrime8845.PRZZCoupledAFE
open PRZZDiagonalAssembly PRZZWRowLimit
set_option maxHeartbeats 5000000

/-- A signed contour, not its absolute-value budget. -/
def correction (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v *
      ((1/(2*Real.pi):ℂ)*∫ y : ℝ, PRZZDiagonalMellin.integrand (alpha+beta)
        (t/(2*Real.pi*(u:ℝ)*v)) ((-(1/8:ℝ):ℂ)+(y:ℂ)*I)) else 0

theorem correction_eq (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (t : ℝ) (ht : 0 < t) :
    correction N a alpha beta t =
      assembled N a (fun _ => 1) (fun _ => 1) alpha beta t-
        main N a (fun _ => 1) (fun _ => 1) alpha beta := by
  classical
  unfold correction assembled main
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases ha : admissible N d u v
  · simp only [if_pos ha,← mul_sub]
    congr 1
    symm
    exact PRZZDiagonalContour.shifted_identity (alpha+beta) hs hn _ (by
      have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
      have hv0 : 0 < v := (Finset.mem_Icc.mp hv).1
      positivity)
  · simp [ha]

theorem correction_continuous (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (correction N a alpha beta) (Set.Icc T (2*T)) := by
  have hr : -1 ≤ (alpha+beta).re := by
    have hh := (abs_le.mp ((abs_re_le_norm (alpha+beta)).trans hn)).1
    linarith
  apply ContinuousOn.congr ((assembled_continuous N a (fun _ => 1) (fun _ => 1)
    alpha beta hs hr T hT).sub continuousOn_const)
  intro t ht
  exact correction_eq N a alpha beta hs hn t (hT.trans_le ht.1)

theorem time_split (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) :
    (∫ t in Set.Icc T (2*T), phi t*assembled N a (fun _ => 1) (fun _ => 1) alpha beta t) =
      (∫ t in Set.Icc T (2*T), phi t)*main N a (fun _ => 1) (fun _ => 1) alpha beta+
        ∫ t in Set.Icc T (2*T), phi t*correction N a alpha beta t := by
  have hi : IntegrableOn (fun t => phi t*main N a (fun _ => 1) (fun _ => 1) alpha beta)
      (Set.Icc T (2*T)) := (hp.mul_const _).integrableOn_Icc
  have hj : IntegrableOn (fun t => phi t*correction N a alpha beta t) (Set.Icc T (2*T)) :=
    (hp.continuousOn.mul (correction_continuous N a alpha beta hs hn T hT)).integrableOn_compact isCompact_Icc
  rw [← integral_mul_const,← integral_add hi hj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [correction_eq N a alpha beta hs hn t (hT.trans_le ht.1)]
  ring

def diagonalPair (L N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Set.Icc T (2*T), phi t*diagonal L N F a a alpha beta t)+
    ∫ t in Set.Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      diagonal L N F a a (-beta) (-alpha) t

def diagonalMain (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Set.Icc T (2*T), phi t)*main N a (fun _ => 1) (fun _ => 1) alpha beta+
    (∫ t in Set.Icc T (2*T), phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      main N a (fun _ => 1) (fun _ => 1) (-beta) (-alpha)

def correctionPair (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Set.Icc T (2*T), phi t*correction N a alpha beta t)+
    ∫ t in Set.Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      correction N a (-beta) (-alpha) t

theorem diagonalPair_limit (N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0) :
    Tendsto (fun L : ℕ => diagonalPair L N F a alpha beta T phi) atTop
      (𝓝 (diagonalMain N a alpha beta T phi+correctionPair N a alpha beta T phi)) := by
  have ar := abs_le.mp ((abs_re_le_norm alpha).trans ha)
  have br := abs_le.mp ((abs_re_le_norm beta).trans hb)
  have hc := PRZZMollifiedTime.dualMultiplier_continuous alpha beta
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hr : -1 ≤ (alpha+beta).re := by
    have hh := (abs_le.mp ((abs_re_le_norm (alpha+beta)).trans hn)).1
    linarith
  have hs' : -beta + -alpha ≠ 0 := by rw [show -beta + -alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hn' : ‖-beta + -alpha‖ ≤ 1/8 := by
    rw [show -beta + -alpha = -(alpha+beta) by ring,norm_neg]
    exact hn
  have hr' : -1 ≤ (-beta + -alpha).re := by
    have hh := (abs_le.mp ((abs_re_le_norm (-beta + -alpha)).trans hn')).1
    linarith
  have h1 := PRZZOriginalDiagonal.labelled_time_limit N F (fun _ => 1) (fun _ => 1) a
    alpha beta hs hr T hT phi hp hlo hhi
  have h2 := PRZZOriginalDiagonal.labelled_time_limit N F (fun _ => 1) (fun _ => 1) a
    (-beta) (-alpha) hs' hr' T hT (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t) (hp.mul hc) hlo hhi
  have hlc : PRZZWRowReindex.leftCoefficient a (fun _ => 1) = a := by
    funext n
    simp only [PRZZWRowReindex.leftCoefficient,mul_one]
  have hrc : PRZZWRowReindex.rightCoefficient a (fun _ => 1) = a := by
    funext n
    simp only [PRZZWRowReindex.rightCoefficient,star_one,mul_one]
  rw [hlc,hrc] at h1 h2
  have h := h1.add h2
  have hspl := time_split N a (-beta) (-alpha) hs' hn' T hT
    (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t) (hp.mul hc)
  rw [time_split N a alpha beta hs hn T hT phi hp,hspl] at h
  convert h using 1 <;> first | rfl | (unfold diagonalMain correctionPair; ring)

/-- The entire original off-diagonal, including the complementary rows,
is retained. This is subtraction of actual finite integrals, not a new
unidentified Fourier sum. -/
def offDiagonalPair (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  twoSided L N F R a a alpha beta T phi-diagonalPair L N F a alpha beta T phi

def coupledModel (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  diagonalMain N a alpha beta T phi+correctionPair N a alpha beta T phi+
    offDiagonalPair L N F R a alpha beta T phi

/-- Preserve the optimal AFE defect budget without spending an absolute
diagonal-remainder bound. The correction and off-diagonal remain signed;
identifying their zero/nonzero Fourier pieces is still required. -/
theorem scaled_coupled_limit (F : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)]
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (js : List ℕ) (S r delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Set.Icc T (2*T), ‖phi t‖ ≤ P) → ∃ E : ℂ,
      Tendsto (fun L : ℕ =>
        (∫ t in Set.Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
            (riemannZeta (PRZZAFEDual.leftArg (A/(Real.log T:ℂ)) t)*
             riemannZeta (PRZZAFEDual.rightArg (B/(Real.log T:ℂ)) t)))-
        coupledModel L N F R (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_afe_error_limit_bound F R hlo hhi js S r delta hS hr hd
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num)] with T h hsmall
  intro A B hA hB hsep N hN hNT phi P hp hP hphi
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL.ne')
  have ha := hsmall.2 A hA
  have hb := hsmall.2 B hB
  have hn : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/8 :=
    (norm_add_le _ _).trans (by linarith)
  have hT : 0 < T := by
    have hh : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hdiag := diagonalPair_limit N F (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    _ _ (by linarith) (by linarith) hs hn T hT phi hp hlo hhi
  obtain ⟨E,hE,hlim,hbound⟩ := h A B hA hB hsep N hN hNT phi P hp hP hphi
  refine ⟨E,?_,hbound⟩
  have hz := hdiag.sub_const
    (diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi+
      correctionPair N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi)
  have hh := hlim.add hz
  simp only [sub_self,add_zero] at hh
  convert hh using 1
  funext L
  unfold coupledModel offDiagonalPair
  ring

#print axioms correction_eq
#print axioms correction_continuous
#print axioms time_split
#print axioms diagonalPair_limit
#print axioms scaled_coupled_limit
end XiPrime8845.PRZZCoupledAFE
