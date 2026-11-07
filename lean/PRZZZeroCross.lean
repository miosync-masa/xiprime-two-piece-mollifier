import PRZZActualZeroReflection
import PRZZCoupledAFE

/-! Cross-branch arithmetic cancellation. The actual Gamma quotient
need not equal the power model: their discrepancy is kept explicitly.
This does not assume an unidentified full off-diagonal Fourier split. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
namespace XiPrime8845.PRZZZeroCross
open PRZZActualZeroReflection
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def zero (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      PRZZDiagonalAssembly.coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v *
        density (alpha+beta) ((u:ℝ)*v) t else 0

theorem reciprocal_powers (sigma : ℂ) (t : ℝ) (ht : 0 < t) :
    ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*((t/(2*Real.pi):ℝ):ℂ)^sigma = 1 := by
  rw [← cpow_add _ _ (by exact_mod_cast (show 0 < t/(2*Real.pi) by positivity).ne'),
    neg_add_cancel,cpow_zero]

/-- Both actual reflected zero densities cancel the opposite diagonal
corrections for the power model. For any multiplier m (in particular
the actual Gamma quotient), precisely the displayed defect remains. -/
theorem cross_row (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta m : ℂ)
    (d u v : ℕ) (t : ℝ) (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) :
    let sigma := alpha+beta
    let X := t/(2*Real.pi*((u:ℝ)*v))
    let cp := PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v
    let cm := PRZZDiagonalAssembly.coefficient a F1 F2 (-beta) (-alpha) d u v
    let qm := ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)
    let qp := ((t/(2*Real.pi):ℝ):ℂ)^sigma
    cp*PRZZDiagonalMellin.diagonal sigma X + m*cm*PRZZDiagonalMellin.diagonal (-sigma) X +
      cp*density sigma ((u:ℝ)*v) t + m*cm*density (-sigma) ((u:ℝ)*v) t =
    cp*riemannZeta (1+sigma)+m*cm*riemannZeta (1-sigma)+
      (m-qm)*(cm*(PRZZDiagonalMellin.diagonal (-sigma) X-riemannZeta (1-sigma))-
        cp*qp*(PRZZDiagonalMellin.diagonal sigma X-riemannZeta (1+sigma))) := by
  dsimp only
  have hpos := weighted_density a F1 F2 alpha beta d u v t hu hv
  have hneg := weighted_density a F1 F2 (-beta) (-alpha) d u v t hu hv
  have he : -beta+-alpha = -(alpha+beta) := by ring
  simp only [neg_neg,he] at hneg
  have hz : 1-(-(alpha+beta)) = 1+(alpha+beta) := by ring
  rw [hz] at hneg
  have hq := reciprocal_powers (alpha+beta) t ht
  rw [hpos]
  linear_combination (norm := ring_nf) m*hneg -
    (PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
      (PRZZDiagonalMellin.diagonal (alpha+beta) (t/(2*Real.pi*((u:ℝ)*v)))-riemannZeta (1+(alpha+beta))))*hq

theorem gamma_cross_row (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (t : ℝ) (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) :
    let sigma := alpha+beta
    let X := t/(2*Real.pi*((u:ℝ)*v))
    let cp := PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v
    let cm := PRZZDiagonalAssembly.coefficient a F1 F2 (-beta) (-alpha) d u v
    let m := PRZZAFEDual.dualMultiplier alpha beta t
    cp*PRZZDiagonalMellin.diagonal sigma X + m*cm*PRZZDiagonalMellin.diagonal (-sigma) X +
      cp*density sigma ((u:ℝ)*v) t + m*cm*density (-sigma) ((u:ℝ)*v) t =
    cp*riemannZeta (1+sigma)+m*cm*riemannZeta (1-sigma)+
      (m-((t/(2*Real.pi):ℝ):ℂ)^(-sigma))*
        (cm*(PRZZDiagonalMellin.diagonal (-sigma) X-riemannZeta (1-sigma))-
          cp*((t/(2*Real.pi):ℝ):ℂ)^sigma*(PRZZDiagonalMellin.diagonal sigma X-riemannZeta (1+sigma))) :=
  cross_row a F1 F2 alpha beta (PRZZAFEDual.dualMultiplier alpha beta t) d u v t hu hv ht

theorem zero_correction (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (t : ℝ) (ht : 0 < t) :
    zero N a alpha beta t =
      -((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta))*PRZZCoupledAFE.correction N a (-beta) (-alpha) t := by
  have hs' : -beta+-alpha ≠ 0 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  rw [PRZZCoupledAFE.correction_eq N a (-beta) (-alpha) hs' hn' t ht]
  unfold zero PRZZDiagonalAssembly.assembled PRZZDiagonalAssembly.main
  simp only [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · rw [if_pos had,if_pos had,if_pos had]
    have hh := weighted_density a (fun _ => 1) (fun _ => 1) alpha beta d u v t
      (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1
    rw [show -beta+-alpha = -(alpha+beta) by ring]
    linear_combination (norm := ring_nf) hh
  · simp only [if_neg had,sub_self,mul_zero]

def gammaDefect (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  (PRZZAFEDual.dualMultiplier alpha beta t-((t/(2*Real.pi):ℝ):ℂ)^(-(alpha+beta)))*
    (PRZZCoupledAFE.correction N a (-beta) (-alpha) t-
      ((t/(2*Real.pi):ℝ):ℂ)^(alpha+beta)*PRZZCoupledAFE.correction N a alpha beta t)

/-- Exact cross cancellation with the actual Gamma multiplier, retaining
its discrepancy from the reciprocal power model. -/
theorem correction_cross (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (t : ℝ) (ht : 0 < t) :
    PRZZCoupledAFE.correction N a alpha beta t+
      PRZZAFEDual.dualMultiplier alpha beta t*PRZZCoupledAFE.correction N a (-beta) (-alpha) t+
      zero N a alpha beta t+PRZZAFEDual.dualMultiplier alpha beta t*zero N a (-beta) (-alpha) t =
        gammaDefect N a alpha beta t := by
  have hs' : -beta+-alpha ≠ 0 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  rw [zero_correction N a alpha beta hs hn t ht,zero_correction N a (-beta) (-alpha) hs' hn' t ht]
  simp only [neg_neg,show -beta+-alpha = -(alpha+beta) by ring,neg_neg]
  unfold gammaDefect
  have hq := reciprocal_powers (alpha+beta) t ht
  linear_combination (norm := ring_nf) -(PRZZCoupledAFE.correction N a alpha beta t)*hq

#print axioms reciprocal_powers
#print axioms cross_row
#print axioms gamma_cross_row
#print axioms zero_correction
#print axioms correction_cross
end XiPrime8845.PRZZZeroCross
