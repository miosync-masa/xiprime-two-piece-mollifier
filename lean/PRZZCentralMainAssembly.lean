import PRZZCentralArithmeticJoin
import PRZZFullLiteralBound
import PRZZZeroGammaBound

/-! Main-term and arithmetic evaluation ports for the explicit full model.
Every part uses the SAME arithmetic grid and strict spatial mask. The
truncated zero mode is not identified with the unrestricted reflected
zeroPair: their actual difference is retained. Weil/DI evaluates positive
cells via CentralArithmeticJoin; no J-uniform bound is inferred from a
J-dependent budget, and no negative-frequency estimate is assumed. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZCentralMainAssembly
open PRZZMellinSeparation PRZZCentralArithmeticJoin PRZZLiteralFourierLimit
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

/-- One common collector, including the actual cutoff values and masks. -/
def collect (P : ℝ → ℂ) (K L N : ℕ) (T eps : ℝ)
    (f : ℕ → ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
      f d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) ((2:ℝ)^s)
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2))

theorem collect_add (P : ℝ → ℂ) (K L N : ℕ) (T eps : ℝ)
    (f g : ℕ → ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ) :
    collect P K L N T eps (fun d D M G H => f d D M G H+g d D M G H) =
      collect P K L N T eps f+collect P K L N T eps g := by
  simp only [collect,sum_add_distrib]

def zeroPart (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps (fun d D M G H =>
    zeroCell N d D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def positivePart (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps (fun d D M G H =>
    positiveCell N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def negativePart (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps (fun d D M G H =>
    negativeCell N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def tailPart (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps (fun d D M G H =>
    cellTail N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

theorem prefix_parts (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    PRZZSmallCentralLiteral.cleanCentralLiteral P F Phi K L J N a T eps alpha beta =
      zeroPart P F Phi K L N a T eps alpha beta+
        positivePart P F Phi K L J N a T eps alpha beta+
        negativePart P F Phi K L J N a T eps alpha beta := by
  simp only [PRZZSmallCentralLiteral.cleanCentralLiteral,PRZZSmallCentralLiteral.cleanRowLiteral,
    zeroPart,positivePart,negativePart,collect,zeroCell,positiveCell,negativeCell,sum_add_distrib]

theorem tail_eq (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    tailPart P F Phi K L J N a T eps alpha beta =
      centralFull P F Phi K L N a T eps alpha beta-
        PRZZSmallCentralLiteral.cleanCentralLiteral P F Phi K L J N a T eps alpha beta := by
  simp only [tailPart,collect,cellTail,cellPrefix,centralFull,rowFull,
    PRZZSmallCentralLiteral.cleanCentralLiteral,PRZZSmallCentralLiteral.cleanRowLiteral,sum_sub_distrib]

theorem full_parts (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    centralFull P F Phi K L N a T eps alpha beta =
      zeroPart P F Phi K L N a T eps alpha beta+
        positivePart P F Phi K L J N a T eps alpha beta+
        negativePart P F Phi K L J N a T eps alpha beta+
        tailPart P F Phi K L J N a T eps alpha beta := by
  rw [tail_eq,prefix_parts]; ring

/-- This convergence is proved for the actual collected tail. -/
theorem tail_part_tendsto (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => tailPart P F Phi K L J N a T eps alpha beta) atTop (𝓝 0) := by
  simp_rw [tail_eq]
  have hc : Tendsto (fun _ : ℕ => centralFull P F Phi K L N a T eps alpha beta) atTop
      (𝓝 (centralFull P F Phi K L N a T eps alpha beta)) := tendsto_const_nhds
  simpa only [sub_self] using hc.sub
    (central_tendsto P F Phi K L N a hF hl hr hPhi hsPhi T eps hT alpha beta hs)

/-- Both branches, with the true Gamma multiplier inside the dual profile. -/
def branchPair (f : (ℝ → ℂ) → ℂ → ℂ → ℂ) (Phi : ℝ → ℂ)
    (T : ℝ) (alpha beta : ℂ) : ℂ :=
  f Phi alpha beta+f (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha)

def zeroMismatch (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  branchPair (fun Phi alpha beta => zeroPart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
    N a T eps alpha beta) Phi T alpha beta-
    PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T)

def arithmeticResidual (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  zeroMismatch P F Phi K N a T eps alpha beta+
    branchPair (fun Phi alpha beta => positivePart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta+
    branchPair (fun Phi alpha beta => negativePart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta+
    branchPair (fun Phi alpha beta => tailPart P F Phi K (PRZZLiteralExhaustion.spatialLength T)
      J N a T eps alpha beta) Phi T alpha beta

theorem model_main_arithmetic (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    fullModel P F Phi K N a T eps alpha beta =
      PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
        arithmeticResidual P F Phi K J N a T eps alpha beta+
        ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  unfold fullModel
  rw [full_parts P F Phi K _ J N a T eps alpha beta,
    full_parts P F (PRZZKeptLiteral.dualProfile Phi T alpha beta) K _ J N a T eps (-beta) (-alpha)]
  unfold arithmeticResidual zeroMismatch branchPair
  ring

/-- The zeta factor is outside the actual primitive coefficient sum. -/
def mainMass (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      PRZZDiagonalAssembly.coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v else 0

theorem diagonal_main_zeta (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) :
    PRZZCoupledAFE.diagonalMain N a alpha beta T phi =
      (∫ t in Icc T (2*T), phi t)*mainMass N a alpha beta*riemannZeta (1+(alpha+beta))+
      (∫ t in Icc T (2*T), phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
        mainMass N a (-beta) (-alpha)*riemannZeta (1+(-beta+-alpha)) := by
  unfold PRZZCoupledAFE.diagonalMain PRZZDiagonalAssembly.main mainMass
  simp only [sum_mul,ite_mul,zero_mul,mul_assoc]

/-- The actual Gamma defect, including all arithmetic coefficients, is
substituted into this model rather than required as a premise. -/
theorem model_main_bound (js : List ℕ) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ K J N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T → ∀ (eps : ℝ) (P F Phi : ℝ → ℂ), Continuous Phi →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖fullModel P F Phi K N a T eps alpha beta-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        ‖arithmeticResidual P F Phi K J N a T eps alpha beta‖+
          C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZZeroGammaBound.defect_time_bound js S r hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep K J N hN hNT eps P F Phi hPhi
  dsimp only
  rw [model_main_arithmetic P F Phi K J]
  have hp : Continuous (scaledCutoff Phi T) :=
    hPhi.comp (continuous_const.mul continuous_id)
  have hh := h A B hA hB hsep N hN hNT (scaledCutoff Phi T) hp
  convert (norm_add_le _ _).trans (add_le_add le_rfl hh) using 1
  congr 1
  ring

/-- The sharp AFE reduction and the evaluated Gamma defect now meet the
same explicit arithmetic residual. There is no original AFE error norm on
the right. This does NOT assert a sharp estimate for arithmeticResidual. -/
theorem moment_main_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop, ∀ (J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T+
          ‖arithmeticResidual (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
            (Nat.log 2 N+2) J N a T eps alpha beta‖+
          D*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZFullLiteralBound.full_total_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨D,hD,hd⟩ := model_main_bound js S r hS hr
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h,hd,eventually_ge_atTop (2:ℝ)] with T h hd hT
  intro J N A B hN hscale hA hB hsep
  dsimp only
  have hpow : T^(4/7:ℝ) ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ T) (by norm_num : (4/7:ℝ) ≤ 1)
  have hNT : (N:ℝ) ≤ T := hscale.trans hpow
  have h1 := (h N A B hN hscale hA hB hsep).2
  have h2 := hd A B hA hB hsep (Nat.log 2 N+2) J N hN hNT eps
    (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi hPhi.continuous
  have hn := norm_add_le
    (PRZZFullLiteralBound.fullError P Phi js N T eps A B)
    (fullModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))-
      PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T))
  have he : PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
      PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T) =
      PRZZFullLiteralBound.fullError P Phi js N T eps A B+
        (fullModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) N
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))-
          PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)) := by
    unfold PRZZFullLiteralBound.fullError
    ring
  rw [he]
  exact (hn.trans (add_le_add h1 h2)).trans_eq (by ring)

#print axioms collect_add
#print axioms prefix_parts
#print axioms tail_eq
#print axioms full_parts
#print axioms tail_part_tendsto
#print axioms model_main_arithmetic
#print axioms diagonal_main_zeta
#print axioms model_main_bound
#print axioms moment_main_bound
end XiPrime8845.PRZZCentralMainAssembly
