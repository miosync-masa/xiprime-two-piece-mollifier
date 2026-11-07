import PRZZAllOffDiagonalRows

/-! Exhaustive finite AFE-to-Poisson row substitution. Small-gap rows use
the proved full Poisson formula (central modes + infinite Fourier tail -
sharp boundary + freezing error). Large-gap rows are retained verbatim.
This is an exact identity, not an estimate discarding the complement. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Finset
namespace XiPrime8845.PRZZAllPoissonRows
open PRZZWRowReindex PRZZWRowLimit PRZZAFEIndices PRZZAllOffDiagonalRows
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def resolved (L J : ℕ) (F F1 F2 : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ) : ℂ :=
  if |(z.2.1:ℝ)| ≤ M*z.1.1/4 then
    PRZZActualPoissonError.poissonPart L J F M z alpha beta (alpha+beta) a d F1 F2 t+
      PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        PRZZUnfrozenPoisson.errorSum L F M z alpha beta (alpha+beta) t
  else PRZZUnfrozenPoisson.afeRow L F F1 F2 M z alpha beta (alpha+beta) a d t

theorem row_resolved (L J : ℕ) (F F1 F2 : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ)
    (hM : 0 < M) (ht : 0 < t) (hd : 0 < d) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : alpha+beta ≠ 0) :
    PRZZUnfrozenPoisson.afeRow L F F1 F2 M z alpha beta (alpha+beta) a d t =
      resolved L J F F1 F2 M z alpha beta a d t := by
  unfold resolved
  split_ifs with hg
  · obtain ⟨hLB,hB,hkB⟩ := PRZZActualPoissonError.cover_bounds L M z hv
    rw [PRZZUnfrozenPoisson.afe_row_eq L F F1 F2 M z alpha beta (alpha+beta) a d t hd hu hv,
      PRZZUnfrozenPoisson.poisson_eq L _ J hLB F hF hsF M t z alpha beta (alpha+beta)
        hM ht hu hv hc hs hg hB hkB]
    unfold PRZZActualPoissonError.poissonPart
    ring
  · rfl

def family (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ labels L N, if z.2.1 ≠ 0 then
    ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, if pairMatches z n r then
      resolved L J (profile F) F1 F2 ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-z.2.1,1)) alpha beta a (Nat.gcd n r) t
    else 0 else 0

/-- The source indices supply positivity and coprimality. The actual
small-gap test itself chooses Poisson versus the unaltered complement. -/
theorem all_rows (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (a : ℕ → ℂ) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    rows L N F F1 F2 a alpha beta t = family L J N F F1 F2 a alpha beta t := by
  have hf := profile_regular F hF hlo hhi
  unfold rows family literalRows
  apply sum_congr rfl
  intro s hss
  apply sum_congr rfl
  intro z hz
  by_cases hg : z.2.1 ≠ 0
  · simp only [if_pos hg]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro r hr
    by_cases hp : pairMatches z n r
    · simp only [if_pos hp]
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hr0 : 0 < r := (mem_Icc.mp hr).1
      have hd : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn0
      have hu : 0 < n/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_left r hn0) hd
      have hv : 0 < r/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_right n hr0) hd
      exact row_resolved L J (profile F) F1 F2 hf.1 hf.2.2 _ _ alpha beta a _ t
        (by positivity) ht hd hu hv (Nat.coprime_div_gcd_div_gcd hd) hs
    · simp only [if_neg hp]
  · simp only [if_neg hg]

/-- Return the *original* two-sided offDiagonalPair to the exhaustive
resolved row family, including both sharp cutoffs and actual Gamma factor. -/
theorem offDiagonal_poisson (L J N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (R : ℕ → Label → Prop) [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    PRZZCoupledAFE.offDiagonalPair L N F R a alpha beta T phi =
      (∫ t in Icc T (2*T), phi t*family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t)+
      ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
        family L J N F (fun _ => 1) (fun _ => 1) a (-beta) (-alpha) t := by
  rw [offDiagonal_reindex L N F R a alpha beta ha hb hs T hT phi hp]
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  congr 1 <;> apply integral_congr_ae <;>
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  · rw [all_rows L J N F _ _ hF hlo hhi a alpha beta hs t (hT.trans_le ht.1)]
  · rw [all_rows L J N F _ _ hF hlo hhi a (-beta) (-alpha) hs' t (hT.trans_le ht.1)]

#print axioms row_resolved
/-- The original coupled AFE model, now with the full actual Poisson
family in place of its previously unidentified offDiagonalPair. No tail,
boundary, complement, or Gamma discrepancy is silently dropped. -/
theorem coupled_poisson (L J N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (R : ℕ → Label → Prop) [DecidablePred (fun p : ℕ × Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    PRZZCoupledAFE.coupledModel L N F R a alpha beta T phi =
      PRZZCoupledAFE.diagonalMain N a alpha beta T phi+
        (((∫ t in Icc T (2*T), phi t*family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t)+
          ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
            family L J N F (fun _ => 1) (fun _ => 1) a (-beta) (-alpha) t)-
          PRZZZeroCoupled.zeroPair N a alpha beta T phi)+
        ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  rw [PRZZZeroCoupled.coupled_reassembly L N F R a alpha beta ha hb hs hn T hT phi hp,
    offDiagonal_poisson L J N F hF hlo hhi R a alpha beta ha hb hs T hT phi hp]

#print axioms coupled_poisson
#print axioms all_rows
#print axioms offDiagonal_poisson
end XiPrime8845.PRZZAllPoissonRows
