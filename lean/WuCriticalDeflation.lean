import WuFiniteDeflation

/-! Remove all critical-line eta zeros in a fixed compact interval, from
both eta and xi'. The remaining eta curve is nowhere zero, including at
the removed zeros. Exact analytic orders restore all removed multiplicity.
No phase-crossing inequality or local zero-proportion bound is assumed. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex Set Filter Topology
namespace XiPrime8845.WuCriticalDeflation
open WuAuxiliary WuAuxiliaryBoundary WuAuxiliaryMultiplicity WuCriticalMultiplicity
open WuFiniteDeflation Zeta23.XiPrime
set_option maxHeartbeats 2000000

abbrev multiplicity (L : ℝ) (s : ℂ) := analyticOrderNatAt (eta L) s

structure Data (L u v : ℝ) where
  zeros : Finset ℂ
  mem_zeros : ∀ s, s ∈ zeros ↔ s ∈ critical '' Icc u v ∧ eta L s = 0
  etaPart : ℂ → ℂ
  xiPart : ℂ → ℂ
  eta_entire : Differentiable ℂ etaPart
  xi_entire : Differentiable ℂ xiPart
  eta_factor : ∀ s, eta L s = divisor zeros (multiplicity L) s*etaPart s
  xi_factor : ∀ s, xiDeriv s = divisor zeros (multiplicity L) s*xiPart s
  nonzero : ∀ t ∈ Icc u v, etaPart (critical t) ≠ 0

theorem exists_data (L u v : ℝ) (hL : L ≠ 0) : Nonempty (Data L u v) := by
  classical
  let f := WuAuxiliary.eta L
  have hf : Differentiable ℂ f := eta_entire L
  have hn : ∃ s, f s ≠ 0 := eta_not_identically_zero L hL
  obtain ⟨s,hs⟩ := hn
  have hn : ∃ z, f z ≠ 0 := ⟨s,hs⟩
  have hdisc : IsClosed {z | f z = 0} ∧ IsDiscrete {z | f z = 0} :=
    compl_mem_codiscrete_iff.mp ((show AnalyticOnNhd ℂ f univ from
      fun z _ => hf.analyticAt z).preimage_zero_mem_codiscrete hs)
  have hcompact : IsCompact (critical '' Icc u v) := isCompact_Icc.image (by
    unfold critical; fun_prop)
  have hfin : ((critical '' Icc u v) ∩ {z | f z = 0}).Finite :=
    IsCompact.finite (hcompact.inter_right hdisc.1) (hdisc.2.mono inter_subset_right)
  let Z := hfin.toFinset
  have hZ (s : ℂ) : s ∈ Z ↔ s ∈ critical '' Icc u v ∧ eta L s = 0 := by simp [Z,f]
  obtain ⟨g,hg,heg⟩ := finite_factor Z (multiplicity L) f hf hn (fun _ _ => le_rfl)
  have hm : ∀ c ∈ Z, multiplicity L c ≤ analyticOrderNatAt xiDeriv c := by
    intro c hc
    obtain ⟨t,ht,rfl⟩ := ((hZ c).mp hc).1
    exact eta_order_le_xiDeriv L t hL
  obtain ⟨h,hh,heh⟩ := finite_factor Z (multiplicity L) xiDeriv xiDeriv_differentiable
    exists_xiDeriv_ne_zero hm
  refine ⟨⟨Z,hZ,g,h,hg,hh,heg,heh,?_⟩⟩
  intro t ht
  by_cases hz : critical t ∈ Z
  · have ho := order_restore Z (multiplicity L) f g hg hn heg (critical t)
    rw [if_pos hz] at ho
    have ho0 : analyticOrderNatAt g (critical t) = 0 := by dsimp [f,multiplicity] at ho; omega
    have hgn : ∃ z, g z ≠ 0 := ⟨s,fun h0 => hs (by rw [heg s,h0,mul_zero])⟩
    apply (hg.analyticAt _).analyticOrderAt_eq_zero.mp
    rw [← Nat.cast_analyticOrderNatAt (entire_order_ne_top g hg hgn _),ho0,Nat.cast_zero]
  · intro h0
    apply hz
    exact (hZ _).mpr ⟨⟨t,ht,rfl⟩,by change f (critical t) = 0; rw [heg _,h0,mul_zero]⟩

def Data.totalOrder {L u v : ℝ} (d : Data L u v) : ℕ := ∑ s ∈ d.zeros, multiplicity L s

def Data.realDivisor {L u v : ℝ} (d : Data L u v) (t : ℝ) : ℝ :=
  ∏ s ∈ d.zeros, (t-s.im)^(multiplicity L s)

def Data.curve {L u v : ℝ} (d : Data L u v) (s : ℂ) : ℂ := Complex.I^d.totalOrder*d.etaPart s

def Data.remaining {L u v : ℝ} (d : Data L u v) (s : ℂ) : ℂ := Complex.I^d.totalOrder*d.xiPart s

theorem Data.divisor_critical {L u v : ℝ} (d : Data L u v) (t : ℝ) :
    divisor d.zeros (multiplicity L) (critical t) = Complex.I^d.totalOrder*(d.realDivisor t:ℂ) := by
  classical
  have he (s : ℂ) (hs : s ∈ d.zeros) : critical t-s = I*(t-s.im:ℝ) := by
    obtain ⟨x,hx,rfl⟩ := ((d.mem_zeros s).mp hs).1
    apply Complex.ext <;> simp [critical]
  simp only [divisor]
  rw [Finset.prod_congr rfl (fun s hs => congrArg (fun z : ℂ => z^(multiplicity L s)) (he s hs))]
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    Data.totalOrder,Data.realDivisor]
  push_cast
  rfl

theorem Data.eta_critical {L u v : ℝ} (d : Data L u v) (t : ℝ) :
    eta L (critical t) = (d.realDivisor t:ℂ)*d.curve (critical t) := by
  rw [d.eta_factor,d.divisor_critical,Data.curve]; ring

theorem Data.xi_critical {L u v : ℝ} (d : Data L u v) (t : ℝ) :
    xiDeriv (critical t) = (d.realDivisor t:ℂ)*d.remaining (critical t) := by
  rw [d.xi_factor,d.divisor_critical,Data.remaining]; ring

theorem Data.curve_nonzero {L u v : ℝ} (d : Data L u v) (t : ℝ) (ht : t ∈ Icc u v) :
    d.curve (critical t) ≠ 0 := mul_ne_zero (pow_ne_zero _ I_ne_zero) (d.nonzero t ht)

theorem Data.xi_order_restore {L u v : ℝ} (d : Data L u v) (s : ℂ) :
    analyticOrderNatAt xiDeriv s =
      (if s ∈ d.zeros then multiplicity L s else 0)+analyticOrderNatAt d.xiPart s :=
  order_restore d.zeros (multiplicity L) xiDeriv d.xiPart d.xi_entire
    exists_xiDeriv_ne_zero d.xi_factor s

/-- One full multiplicity budget, not one arbitrary error per component. -/
theorem Data.count_restore {L u v : ℝ} (d : Data L u v) (S : Finset ℂ) (hS : d.zeros ⊆ S) :
    (∑ s ∈ S, analyticOrderNatAt xiDeriv s) =
      d.totalOrder+∑ s ∈ S, analyticOrderNatAt d.xiPart s := by
  classical
  simp_rw [d.xi_order_restore]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_subset hS (fun s hs hn => by simp [hn]) |>.symm.trans (by simp [Data.totalOrder])

/-- A genuine continuous logarithm exists across every removed eta zero. -/
theorem Data.edgeLog {L u v : ℝ} (d : Data L u v) (huv : u ≤ v) :
    Nonempty (WuLittlewood.EdgeLog d.curve (1/2) I u v) := by
  obtain ⟨q,hq⟩ := WuLittlewood.edgeLog_exists d.curve (1/2) I u v u ⟨le_rfl,huv⟩
    (fun t _ => analyticAt_const.mul (d.eta_entire.analyticAt _))
    (fun t ht => d.curve_nonzero t ht)
    (log (d.curve (critical u))) (exp_log (d.curve_nonzero u ⟨le_rfl,huv⟩))
  exact ⟨q⟩

#print axioms exists_data
#print axioms Data.divisor_critical
#print axioms Data.curve_nonzero
#print axioms Data.xi_order_restore
#print axioms Data.count_restore
#print axioms Data.edgeLog
end XiPrime8845.WuCriticalDeflation
