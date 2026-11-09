import PRZZClassSignedGrid
import PRZZClassZeroCorrection

/-! Exact identification of the original nonzero central collector with the
row-dependent Weil/DI grid. The common-J to bodyCut difference and the actual
Fourier tail are retained separately, on precisely the same strict spatial
mask. No estimate or vanishing assertion for either correction is assumed. -/
noncomputable section
open scoped BigOperators
open Complex Finset
namespace XiPrime8845.PRZZCentralGridIdentity
open PRZZMellinSeparation PRZZCentralMainAssembly
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem lift_sum {ι : Type*} (ss : Finset ι) (Q : ι → (ℕ → ℂ) → ℂ)
    (c e : ℕ → ℂ) :
    PRZZMixedPoisson.lift (fun f => ∑ i ∈ ss, Q i f) c e =
      ∑ i ∈ ss, PRZZMixedPoisson.lift (Q i) c e := by
  unfold PRZZMixedPoisson.lift
  simp only [mul_sum,← sum_sub_distrib,← sum_add_distrib,sum_div]

theorem lift_add (Q R : (ℕ → ℂ) → ℂ) (c e : ℕ → ℂ) :
    PRZZMixedPoisson.lift (fun f => Q f+R f) c e =
      PRZZMixedPoisson.lift Q c e+PRZZMixedPoisson.lift R c e := by
  unfold PRZZMixedPoisson.lift
  ring

def spatial (L : ℕ) (T : ℝ) : Finset ℕ :=
  (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))

def cell (N d J : ℕ) (D T M : ℝ) (c e : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (a b : ℂ) : ℂ :=
  PRZZClassPoisson.positiveCell N d J D T M c e F G H Phi a b+
    PRZZClassNegativePoisson.negativeCell N d J D T M c e F G H Phi a b

def central (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ)
    (K N : ℕ) (ss : Finset ℕ) (c e : ℕ → ℂ)
    (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (T eps : ℝ) (a b : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    cell N d (cut p s d)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s)
      c e F (scaledCutoff (F0 p.1) ((2:ℝ)^p.1))
      (scaledCutoff (F2 p.2) ((2:ℝ)^p.2)) Phi a b

def body (T eH : ℝ) (p : ℕ × ℕ) (s d : ℕ) : ℕ :=
  PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0

/-- The transfer is the sum of the actual row differences, not an
unidentified scalar remainder. In particular bodyCut=0 is not dropped. -/
def transfer (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ)
    (K J N : ℕ) (ss : Finset ℕ) (c e : ℕ → ℂ)
    (T eps eH : ℝ) (a b : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    (cell N d J
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s)
      c e F (scaledCutoff (F0 p.1) ((2:ℝ)^p.1))
      (scaledCutoff (F2 p.2) ((2:ℝ)^p.2)) Phi a b-
    cell N d (body T eH p s d)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps) T ((2:ℝ)^s)
      c e F (scaledCutoff (F0 p.1) ((2:ℝ)^p.1))
      (scaledCutoff (F2 p.2) ((2:ℝ)^p.2)) Phi a b)

theorem common_eq_body_transfer (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ)
    (K J N : ℕ) (ss : Finset ℕ) (c e : ℕ → ℂ)
    (T eps eH : ℝ) (a b : ℂ) :
    central F0 F2 F Phi K N ss c e (fun _ _ _ => J) T eps a b =
      central F0 F2 F Phi K N ss c e (body T eH) T eps a b+
        transfer F0 F2 F Phi K J N ss c e T eps eH a b := by
  simp only [central,transfer,sum_sub_distrib]
  ring

/-- Exact equality to the grid already estimated by Weil and DI, including
both coefficient slots, both frequency signs and the logarithmic shifts. -/
theorem body_eq_grid (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ)
    (js ks : List ℕ) (N : ℕ) (ss : Finset ℕ) (T eps eH : ℝ) (A B : ℂ) :
    central F0 F2 F Phi (Nat.log 2 N+2) N ss
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient ks n:ℂ))
      (body T eH) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
    PRZZClassSignedGrid.grid F0 F2 F Phi js ks N ss (fun _ _ _ => 1)
      T eps eH A B := by
  simp only [central,cell,body,PRZZClassSignedGrid.grid,
    PRZZClassPositiveGrid.grid,PRZZClassNegativeGrid.grid,one_mul,sum_add_distrib]

theorem common_eq_original (P F Phi : ℝ → ℂ) (K L J N : ℕ)
    (c e : ℕ → ℂ) (T eps : ℝ) (a b : ℂ) :
    central (fun _ => PRZZWRowLimit.profile P) (fun _ => PRZZWRowLimit.profile P)
      (PRZZWRowLimit.profile F) Phi K N (spatial L T) c e (fun _ _ _ => J) T eps a b =
    PRZZMixedPoisson.lift (fun f => positivePart P F Phi K L J N f T eps a b+
      negativePart P F Phi K L J N f T eps a b) c e := by
  simp only [central,cell,spatial,positivePart,negativePart,collect,
    lift_add,lift_sum,PRZZClassPoisson.positiveCell,
    PRZZClassNegativePoisson.negativeCell,sum_add_distrib]

/-- Return the original nonzero field to the body grid without discarding
the common-cutoff correction or the Fourier tail. Both AFE branches keep
their original dualProfile and their original coefficient order. -/
theorem nonzero_eq_body_transfer_tail (P F Phi : ℝ → ℂ) (K J N : ℕ)
    (c e : ℕ → ℂ) (T eps eH : ℝ) (a b : ℂ) :
    PRZZMixedPoisson.lift (fun f => PRZZClassZeroCorrection.nonzeroResidual
      P F Phi K J N f T eps a b) c e =
    branchPair (fun Phi a b =>
      central (fun _ => PRZZWRowLimit.profile P) (fun _ => PRZZWRowLimit.profile P)
        (PRZZWRowLimit.profile F) Phi K N
        (spatial (PRZZLiteralExhaustion.spatialLength T) T) c e (body T eH) T eps a b+
      transfer (fun _ => PRZZWRowLimit.profile P) (fun _ => PRZZWRowLimit.profile P)
        (PRZZWRowLimit.profile F) Phi K J N
        (spatial (PRZZLiteralExhaustion.spatialLength T) T) c e T eps eH a b)
      Phi T a b+
    PRZZMixedPoisson.lift (fun f => branchPair (fun Phi a b =>
      tailPart P F Phi K (PRZZLiteralExhaustion.spatialLength T) J N f T eps a b)
      Phi T a b) c e := by
  simp_rw [← common_eq_body_transfer,common_eq_original]
  unfold PRZZClassZeroCorrection.nonzeroResidual branchPair PRZZMixedPoisson.lift
  ring

/-- The original two-branch nonzero collector for independent arithmetic
labels is exactly the two evaluated grids plus the displayed transfer and
tail. The dual branch uses (-B,-A), with no swap of the coefficient labels. -/
theorem nonzero_eq_grid (P F Phi : ℝ → ℂ) (js ks : List ℕ) (J N : ℕ)
    (T eps eH : ℝ) (A B : ℂ) :
    let c := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let e := fun n => (PRZZGCoefficient.coefficient ks n:ℂ)
    let a := A/(Real.log T:ℂ)
    let b := B/(Real.log T:ℂ)
    let ss := spatial (PRZZLiteralExhaustion.spatialLength T) T
    let F0 := fun _ : ℕ => PRZZWRowLimit.profile P
    let FM := PRZZWRowLimit.profile F
    PRZZMixedPoisson.lift (fun f => PRZZClassZeroCorrection.nonzeroResidual
      P F Phi (Nat.log 2 N+2) J N f T eps a b) c e =
      PRZZClassSignedGrid.grid F0 F0 FM Phi js ks N ss (fun _ _ _ => 1) T eps eH A B+
      PRZZClassSignedGrid.grid F0 F0 FM (PRZZKeptLiteral.dualProfile Phi T a b)
        js ks N ss (fun _ _ _ => 1) T eps eH (-B) (-A)+
      branchPair (fun Phi a b => transfer F0 F0 FM Phi (Nat.log 2 N+2) J N ss c e
        T eps eH a b) Phi T a b+
      PRZZMixedPoisson.lift (fun f => branchPair (fun Phi a b =>
        tailPart P F Phi (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T)
          J N f T eps a b) Phi T a b) c e := by
  dsimp only
  have he := nonzero_eq_body_transfer_tail P F Phi (Nat.log 2 N+2) J N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) T eps eH
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  unfold branchPair at he ⊢
  simp_rw [← neg_div] at he ⊢
  simp_rw [body_eq_grid] at he
  linear_combination he

#print axioms common_eq_body_transfer
#print axioms lift_sum
#print axioms lift_add
#print axioms body_eq_grid
#print axioms common_eq_original
#print axioms nonzero_eq_body_transfer_tail
#print axioms nonzero_eq_grid
end XiPrime8845.PRZZCentralGridIdentity
