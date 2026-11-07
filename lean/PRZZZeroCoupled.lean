import PRZZZeroCross

/-! Signed reassembly into the existing coupled AFE model. The actual
Gamma discrepancy is explicit. The remaining offDiagonalPair-zeroPair
is NOT claimed to be the nonzero Poisson A* until that separate actual
Fourier-decomposition equality is proved. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroCoupled
open PRZZZeroCross PRZZCoupledAFE
set_option maxHeartbeats 6000000

theorem power_continuous (sigma : ℂ) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (fun t : ℝ => ((t/(2*Real.pi):ℝ):ℂ)^sigma) (Icc T (2*T)) := by
  intro t ht
  have hx : 0 < t/(2*Real.pi) := by have ht0 := hT.trans_le ht.1; positivity
  have hb : ContinuousAt (fun t : ℝ => ((t/(2*Real.pi):ℝ):ℂ)) t := by fun_prop
  have hc : ContinuousAt (fun z : ℂ => z^sigma) ((t/(2*Real.pi):ℝ):ℂ) :=
    continuousAt_cpow_const (a := ((t/(2*Real.pi):ℝ):ℂ)) (b := sigma)
      (Complex.ofReal_mem_slitPlane.mpr hx)
  exact (hc.comp_of_eq hb rfl).continuousWithinAt

theorem zero_continuous (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (zero N a alpha beta) (Icc T (2*T)) := by
  have hs' : -beta+-alpha ≠ 0 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  apply ContinuousOn.congr ((power_continuous (-(alpha+beta)) T hT).neg.mul
    (correction_continuous N a (-beta) (-alpha) hs' hn' T hT))
  intro t ht
  exact zero_correction N a alpha beta hs hn t (hT.trans_le ht.1)

def zeroPair (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  (∫ t in Icc T (2*T), phi t*zero N a alpha beta t)+
    ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*zero N a (-beta) (-alpha) t

theorem integrated_cross (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) :
    correctionPair N a alpha beta T phi+zeroPair N a alpha beta T phi =
      ∫ t in Icc T (2*T), phi t*gammaDefect N a alpha beta t := by
  have ar := abs_le.mp ((abs_re_le_norm alpha).trans ha)
  have br := abs_le.mp ((abs_re_le_norm beta).trans hb)
  have hG := PRZZMollifiedTime.dualMultiplier_continuous alpha beta
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  have hs' : -beta+-alpha ≠ 0 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  have h1 : IntegrableOn (fun t : ℝ => phi t*correction N a alpha beta t) (Icc T (2*T)) :=
    (hp.continuousOn.mul (correction_continuous N a alpha beta hs hn T hT)).integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun t : ℝ => (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*correction N a (-beta) (-alpha) t)
      (Icc T (2*T)) :=
    ((hp.mul hG).continuousOn.mul (correction_continuous N a (-beta) (-alpha) hs' hn' T hT)).integrableOn_compact isCompact_Icc
  have h3 : IntegrableOn (fun t : ℝ => phi t*zero N a alpha beta t) (Icc T (2*T)) :=
    (hp.continuousOn.mul (zero_continuous N a alpha beta hs hn T hT)).integrableOn_compact isCompact_Icc
  have h4 : IntegrableOn (fun t : ℝ => (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*zero N a (-beta) (-alpha) t)
      (Icc T (2*T)) :=
    ((hp.mul hG).continuousOn.mul (zero_continuous N a (-beta) (-alpha) hs' hn' T hT)).integrableOn_compact isCompact_Icc
  unfold correctionPair zeroPair
  rw [← integral_add h1 h2,← integral_add h3 h4]
  have hadd := integral_add (h1.add h2) (h3.add h4)
  simp only [Pi.add_apply] at hadd
  rw [← hadd]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hh := correction_cross N a alpha beta hs hn t (hT.trans_le ht.1)
  linear_combination (norm := ring_nf) phi t*hh

/-- Reassemble the *existing* AFE coupled model without replacing its
actual off-diagonal by an assumed A*. The remaining signed difference
and the actual Gamma defect are both visible. -/
theorem coupled_reassembly (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hp : Continuous phi) :
    coupledModel L N F R a alpha beta T phi =
      diagonalMain N a alpha beta T phi+
        (offDiagonalPair L N F R a alpha beta T phi-zeroPair N a alpha beta T phi)+
          ∫ t in Icc T (2*T), phi t*gammaDefect N a alpha beta t := by
  have hh := integrated_cross N a alpha beta ha hb hs hn T hT phi hp
  unfold coupledModel
  linear_combination (norm := ring_nf) hh

#print axioms power_continuous
#print axioms zero_continuous
#print axioms integrated_cross
#print axioms coupled_reassembly
end XiPrime8845.PRZZZeroCoupled
