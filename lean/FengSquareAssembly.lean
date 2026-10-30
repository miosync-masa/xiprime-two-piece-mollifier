import FengLogProducts

/-! Exact nine-product K22 assembly with the shifted raw outer weight.
Only the five logarithmic products are discharged here. The remaining four
products are explicit arithmetic suppliers, not axioms or inferred limits.
In particular shared/shared retains non-squarefree g and its SHIFTED weight. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSquareAssembly
open FengAtG FengLogProducts LogProfileSum CoprimeEndpoint BetaKernel

def fullSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  productSum fengBlock fengBlock L θ P G A B

def remainingSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  productSum outsideBlock outsideBlock L θ P G A B+
  productSum outsideBlock sharedBlock L θ P G A B+
  productSum sharedBlock outsideBlock L θ P G A B+
  productSum sharedBlock sharedBlock L θ P G A B

/-- The finite identity contains nine ORDERED products, with exactly the same
g range, inner cutoffs and generalized-totient weight in every summand. -/
theorem fullSum_decomposition (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    fullSum L θ P G A B = logarithmicSum L θ P G A B+remainingSum L θ P G A B := by
  unfold fullSum logarithmicSum remainingSum productSum
  simp only [← add_div,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [fengBlock_decomposition _ g _ _ _ _ _ (mem_Ioc.mp hg).1.ne',
    fengBlock_decomposition _ g _ _ _ _ _ (mem_Ioc.mp hg).1.ne']
  ring

def remainingKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  E (-1) (-1) 1-E (-1) 1 3-E 1 (-1) 3+7*E 1 1 5

/-- Coefficient bookkeeping, not a proof of any missing arithmetic limit. -/
theorem kernel_assemble (E : ℤ → ℤ → ℕ → ℂ) :
    logarithmicKernel E+remainingKernel E = poleSum 2 2 E := by
  rw [assemble22]
  unfold logarithmicKernel remainingKernel
  ring

theorem fullSum_residual (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    fullSum L θ P G A B-poleSum 2 2 (monomialIntegral A B θ P G) =
      (logarithmicSum L θ P G A B-logarithmicKernel (monomialIntegral A B θ P G))+
      (remainingSum L θ P G A B-remainingKernel (monomialIntegral A B θ P G)) := by
  rw [fullSum_decomposition,← kernel_assemble]
  ring

/-- One aggregate form of the still-outstanding, literal arithmetic limit. -/
def RemainingAsymptotic (P G : Polynomial ℂ) : Prop :=
  TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => remainingSum L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => remainingKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
    atTop ElementaryGcd.twoBidiscs

/-- Separate suppliers for the four remaining ordered products. These fields
must be proved for the actual shifted sums; zero-weight shared/shared alone
does not inhabit this structure. The common theta^-4 is applied later. -/
structure RemainingSuppliers (P G : Polynomial ℂ) : Prop where
  outside_outside : TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => productSum outsideBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) (-1) 1)
    atTop ElementaryGcd.twoBidiscs
  outside_shared : TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => productSum outsideBlock sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => -monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) 1 3)
    atTop ElementaryGcd.twoBidiscs
  shared_outside : TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => productSum sharedBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => -monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 (-1) 3)
    atTop ElementaryGcd.twoBidiscs
  shared_shared_shifted : TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => productSum sharedBlock sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => 7*monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 5)
    atTop ElementaryGcd.twoBidiscs

theorem remaining_of_suppliers (P G : Polynomial ℂ) (h : RemainingSuppliers P G) :
    RemainingAsymptotic P G := by
  simpa only [RemainingAsymptotic,remainingSum,remainingKernel,sub_eq_add_neg,Pi.add_def] using
    ((h.outside_outside.add h.outside_shared).add h.shared_outside).add h.shared_shared_shifted

/-- Conditional K22 assembly. This theorem does NOT discharge the remaining
outside or shifted shared/shared arithmetic suppliers. -/
theorem fullSum_twoBidiscs_of_remaining (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (h : RemainingAsymptotic P G) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => poleSum 2 2 (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [Pi.add_def,← fullSum_decomposition,kernel_assemble] using
    (logarithmicSum_twoBidiscs P G hP hG).add h

theorem fullSum_reflected_of_remaining (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (h : RemainingAsymptotic P G) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => poleSum 2 2 (monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (fullSum_twoBidiscs_of_remaining P G hP hG h)

#print axioms fullSum_decomposition
#print axioms kernel_assemble
#print axioms fullSum_residual
#print axioms remaining_of_suppliers
#print axioms fullSum_twoBidiscs_of_remaining
#print axioms fullSum_reflected_of_remaining
end XiPrime8845.FengSquareAssembly

