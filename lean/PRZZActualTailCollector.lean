import PRZZActualTailNative
import PRZZCommonCutMoment

/-! Full strict-window collector of the actual native tail integrals.
Both valued arithmetic profiles and the genuine dual time profile are
preserved. The difference between the literal rectangle and native masks
is explicit; no optimized bound on this rejection is assumed. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZActualTailCollector
open PRZZMellinSeparation PRZZActualTailNative PRZZNativeCentralLiteral
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def nativeCell (L N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then
    ∫ t in Icc T (2*T), Phi (t/T)*PRZZNativeComponents.row .tail L J
      F G H M z alpha beta a d t else 0

def nativeCellMass (L N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then
    ∫ t in Icc T (2*T), ‖Phi (t/T)*PRZZNativeComponents.row .tail L J
      F G H M z alpha beta a d t‖ else 0

def native (P F Phi : ℝ → ℂ) (R K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  PRZZWindowMoment.collect P K L N T eps cut (fun d J D M G H =>
    nativeCell R N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def rejected (P F Phi : ℝ → ℂ) (R K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  PRZZWindowMoment.collect P K L N T eps cut (fun d J D M G H =>
    rejectedTail R N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def mass (P F Phi : ℝ → ℂ) (R K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ range K ×ˢ range K,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Finset.Icc 1 N,
      nativeCellMass R N d (cut p s d)
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s)
        a (PRZZWRowLimit.profile F)
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi alpha beta

theorem native_mass (P F Phi : ℝ → ℂ) (R K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) :
    ‖native P F Phi R K L N a T eps cut alpha beta‖ ≤
      mass P F Phi R K L N a T eps cut alpha beta := by
  unfold native PRZZWindowMoment.collect mass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro p hp
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  unfold nativeCell nativeCellMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro z hz
  split_ifs
  · exact norm_integral_le_integral_norm _
  · simp

theorem tail_split (P F Phi : ℝ → ℂ) (R K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) :
    PRZZWindowMoment.tail P F Phi K L N a T eps cut alpha beta =
      native P F Phi R K L N a T eps cut alpha beta+
        rejected P F Phi R K L N a T eps cut alpha beta := by
  have hf := PRZZWRowLimit.profile_regular F hF hl hr
  unfold PRZZWindowMoment.tail native rejected PRZZWindowMoment.collect
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro p hp
  apply sum_congr rfl; intro s hss
  apply sum_congr rfl; intro d hd
  exact native_split R N d (cut p s d) _ T _ a _ _ _ Phi alpha beta
    hf.1 hPhi hf.2.2 hsPhi hT (by positivity) hs

def pairedRejected (P Phi : ℝ → ℂ) (js : List ℕ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair
    (fun Phi alpha beta => rejected P P Phi R (Nat.log 2 N+2)
      (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta)
    Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

def pairedMass (P Phi : ℝ → ℂ) (js : List ℕ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℝ :=
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  let m := fun Phi alpha beta => mass P P Phi R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta
  m Phi alpha beta+m (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha)

/-- Full substitution for actualTail, not a bound on a supplied proxy.
Only the explicitly displayed rejected rectangle is still outside the
native mass. Both branches use the very same body cutoff. -/
theorem actual_tail_bound (P Phi : ℝ → ℂ) (js : List ℕ) (R N : ℕ)
    (T eD eH : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4)
    (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    ‖PRZZCommonCutMoment.actualTail P Phi js N T eD eH A B‖ ≤
      pairedMass P Phi js R N T eD eH A B+‖pairedRejected P Phi js R N T eD eH A B‖ := by
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]
    exact neg_ne_zero.mpr hs
  have hp := tail_split P P Phi R (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eD (PRZZCommonSignedWindow.cutoff T eH)
    alpha beta hP hl hr hPhi hsPhi hT hs
  have hq := tail_split P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    T eD (PRZZCommonSignedWindow.cutoff T eH) (-beta) (-alpha) hP hl hr hd.1 hd.2 hT hs'
  unfold PRZZCommonCutMoment.actualTail PRZZCentralMainAssembly.branchPair
  dsimp only
  rw [hp,hq]
  have h1 := native_mass P P Phi R (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta
  have h2 := native_mass P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    T eD (PRZZCommonSignedWindow.cutoff T eH) (-beta) (-alpha)
  dsimp only [pairedMass,pairedRejected,PRZZCentralMainAssembly.branchPair]
  calc
    _ = ‖(native P P Phi R _ _ _ _ _ _ _ _ _+
        native P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R _ _ _ _ _ _ _ _ _)+
        (rejected P P Phi R _ _ _ _ _ _ _ _ _+
        rejected P P (PRZZKeptLiteral.dualProfile Phi T alpha beta) R _ _ _ _ _ _ _ _ _)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) le_rfl)

#print axioms native_mass
#print axioms tail_split
#print axioms actual_tail_bound

/-- A single exhaustion threshold covers every arithmetic and spatial
cell of the original finite collector, uniformly in the time profile,
Fourier cutoffs and shifts. Spatial length L is fixed before R tends up. -/
theorem rejected_eventually (P : ℝ → ℂ) (K L N : ℕ) (T eps : ℝ)
    (hsP : Function.support (PRZZWRowLimit.profile P) ⊆ Icc (1/2:ℝ) 3)
    (hT : 0 < T) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ R : ℕ in atTop, ∀ (F Phi : ℝ → ℂ) (a : ℕ → ℂ)
      (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ),
      rejected P F Phi R K L N a T eps cut alpha beta = 0 := by
  have hh : ∀ᶠ R : ℕ in atTop, ∀ p ∈ range K ×ˢ range K,
      ∀ s ∈ range (L+2), ∀ d ∈ Finset.Icc 1 N,
      ∀ (J : ℕ) (F H Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ),
      rejectedTail R N d J
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s) a
        F (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)) H Phi alpha beta = 0 := by
    apply (eventually_all_finset _).mpr
    intro p hp
    apply (eventually_all_finset _).mpr
    intro s hss
    apply (eventually_all_finset _).mpr
    intro d hd
    exact rejected_tail_eventually N d (PRZZWRowLimit.profile P) ((2:ℝ)^p.1) T ((2:ℝ)^s) eps
      (by positivity) hT (by positivity) (mem_Icc.mp hd).1 hsP hheight
  filter_upwards [hh] with R hR
  intro F Phi a cut alpha beta
  unfold rejected PRZZWindowMoment.collect
  apply sum_eq_zero; intro p hp
  apply sum_eq_zero; intro s hss
  apply sum_eq_zero; intro d hd
  exact hR p hp s (mem_filter.mp hss).1 d hd _ _ _ _ _ _ _

/-- The literal paired tail is eventually bounded by the native mass
alone, with no rejected-row premise. R is an auxiliary native exhaustion;
it is not substituted for the original spatialLength T. -/
theorem actual_tail_native (P Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ)
    (T eD eH : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hheight : 8 ≤ T^(1-eD))
    (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4) (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    ∀ᶠ R : ℕ in atTop,
      ‖PRZZCommonCutMoment.actualTail P Phi js N T eD eH A B‖ ≤
        pairedMass P Phi js R N T eD eH A B := by
  have hp := PRZZWRowLimit.profile_regular P hP hl hr
  filter_upwards [rejected_eventually P (Nat.log 2 N+2)
    (PRZZLiteralExhaustion.spatialLength T) N T eD hp.2.2 hT hheight] with R hR
  have hbnd := actual_tail_bound P Phi js R N T eD eH A B hP hl hr hPhi hsPhi hT ha hb hs
  have hz : pairedRejected P Phi js R N T eD eH A B = 0 := by
    simp only [pairedRejected,PRZZCentralMainAssembly.branchPair,hR,add_zero]
  simpa only [hz,norm_zero,add_zero] using hbnd

#print axioms rejected_eventually
#print axioms actual_tail_native

/-- Transfer an exhaustion-uniform native budget to the actual tail.
The only estimate premise is on the explicit native row mass; neither a
rejection bound nor a relation between the two exhaustion lengths is
requested. Supplying this mass from the source-cutoff budgets is separate. -/
theorem actual_tail_of_native_budget (P Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ)
    (T eD eH C : ℝ) (A B : ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hheight : 8 ≤ T^(1-eD))
    (ha : ‖A/(Real.log T:ℂ)‖ ≤ 1/4) (hb : ‖B/(Real.log T:ℂ)‖ ≤ 1/4)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0)
    (hbudget : ∀ᶠ R : ℕ in atTop, pairedMass P Phi js R N T eD eH A B ≤ C) :
    ‖PRZZCommonCutMoment.actualTail P Phi js N T eD eH A B‖ ≤ C := by
  obtain ⟨R,hR,hC⟩ := ((actual_tail_native P Phi js N T eD eH A B
    hP hl hr hPhi hsPhi hT hheight ha hb hs).and hbudget).exists
  exact hR.trans hC

#print axioms actual_tail_of_native_budget
end XiPrime8845.PRZZActualTailCollector
