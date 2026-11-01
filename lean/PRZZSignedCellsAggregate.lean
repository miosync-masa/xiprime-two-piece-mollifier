import PRZZAllCellsBound

/-! All actual cells to the original signed sum and outer integral.
The common analytic cell envelope remains an explicit premise. In
particular this does not claim the Type I/II scale suppliers are complete. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZSignedCellsAggregate
open PRZZAllCellsBound PRZZAllSignedSources PRZZActualSignedBranches
open PRZZCoefficientSeparation PRZZSupportedSplit PRZZGCoefficient PRZZHBBranches
open PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 2000000

/-- Quantification uses the literal row-dependent root and every labelled
allocation; a bound for a selected set of balanced cells does not suffice. -/
def CellBound (N d K : ℕ) (js : List ℕ) (D H x y t : ℝ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (B : ℝ) : Prop :=
  ∀ j ∈ range (Nat.log 2 N+1), ∀ l ∈ range (Nat.log 2 N+1),
    ∀ q ∈ allocations js, ∀ h ∈ hSupport N d,
    ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K q.2,
    ∀ k : Fin b.2.length → Fin (Nat.log 2 N+1),
    ‖PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b (fun i => (k i).val)
      (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t
      (fun a => nu (frequencies d D H) x y (a:ℤ))
      (fun a => nu (frequencies d D H) x y (-(a:ℤ)))‖ ≤ B

theorem signedCells_bound (K : ℕ) (js : List ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T B : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B →
      ∀ D H x y t : ℝ, ∀ F1 F2 FM : ℝ → ℂ, ∀ alpha beta' : ℂ,
      CellBound N d K js D H x y t F1 F2 FM alpha beta' B →
      ‖PRZZHiAllocatedCells.signedCells N d K D H js F1 F2 FM alpha beta' x y t‖ ≤
        C*T^eta*(d:ℝ)^eta*(N:ℝ)^beta*B := by
  choose c hc hb using fun q : List ℕ × List ℕ => blocks_bound K q.2 (eta/2) (by positivity)
  obtain ⟨Ca,hCa,ha⟩ := allocation_bound js eta beta heta hbeta
  obtain ⟨Co,hCo,ho⟩ := outer_sum_bound (eta/2) (by positivity)
  let M := ((allocations js).map c).sum
  have hM : 0 ≤ M := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact (hc q).le
  refine ⟨Co*Ca*(M+1),by positivity,?_⟩
  intro N d hN hd T B hNT hL hB D H x y t F1 F2 FM alpha beta' hcell
  have hT : 0 < T := lt_of_lt_of_le (by exact_mod_cast (show 0 < N by omega)) hNT
  have hpow : T^(eta/2)*T^(eta/2) = T^eta := by
    rw [← Real.rpow_add hT]; congr 1; ring
  have hsum : ((allocations js).map (fun q => c q*T^(eta/2)*B)).sum = M*T^(eta/2)*B := by
    have hs (qs : List (List ℕ × List ℕ)) :
        (qs.map (fun q => c q*T^(eta/2)*B)).sum = (qs.map c).sum*T^(eta/2)*B := by
      induction qs with
      | nil => simp
      | cons q qs ih => simp only [List.map_cons,List.sum_cons,ih]; ring
    exact hs _
  rw [signedCells_eq]
  have hh := ho N hN T (Ca*(d:ℝ)^eta*(N:ℝ)^beta*(M*T^(eta/2)*B)) hNT hL (by positivity)
    (fun j l => ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
      (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 js D H x y t F1 F2 FM alpha beta')).sum)
    (by
      intro j hj l hl
      have hh := ha d N hd hN (fun q => c q*T^(eta/2)*B)
        (fun q h => blocks N d h j l K q.2 js D H x y t F1 F2 FM alpha beta')
        (fun q _ => by have := hc q; positivity)
        (fun q hq h hh => hb q N d h j l hN T B hNT hL hB js D H x y t F1 F2 FM alpha beta'
          (hcell j hj l hl q hq h hh))
      simpa only [hsum] using hh)
  apply hh.trans
  have he : Co*T^(eta/2)*(Ca*(d:ℝ)^eta*(N:ℝ)^beta*(M*T^(eta/2)*B)) =
      Co*Ca*M*T^eta*(d:ℝ)^eta*(N:ℝ)^beta*B := by
    calc
      _ = Co*Ca*M*(T^(eta/2)*T^(eta/2))*(d:ℝ)^eta*(N:ℝ)^beta*B := by ring
      _ = _ := by rw [hpow]
  rw [he]
  gcongr
  linarith

theorem signedSum_bound (K : ℕ) (hK : 0 < K) (js : List ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T B : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B →
      ∀ D H x y t : ℝ, ∀ F1 F2 FM : ℝ → ℂ, ∀ alpha beta' : ℂ,
      CellBound N d K js D H x y t F1 F2 FM alpha beta' B →
      ‖signedSum N d D H (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta' x y t‖ ≤
        C*T^eta*(d:ℝ)^eta*(N:ℝ)^beta*B := by
  obtain ⟨C,hC,h⟩ := signedCells_bound K js eta beta heta hbeta
  refine ⟨C,hC,?_⟩
  intro N d hN hd T B hNT hL hB D H x y t F1 F2 FM alpha beta' hb
  rw [PRZZHiAllocatedCells.signedSum_eq N d K hd hK]
  exact h N d hN hd T B hNT hL hB D H x y t F1 F2 FM alpha beta' hb

/-- The original A* integral, not an abstract substituted sum. All
arithmetic decomposition and outer L1 costs are supplied. -/
theorem literal_bound (K : ℕ) (hK : 0 < K) (js : List ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta)
    (W Phi : ℝ → ℂ) (hW : Continuous W) (hPhi : ContDiff ℝ ∞ Phi)
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ D H M : ℝ, 0 ≤ M →
      ∀ (F1 F2 FM : ℝ → ℂ) (alpha beta' : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(alpha+beta').re| ≤ S/Real.log T →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t : ℝ,
        CellBound N d K js D H p.1 p.2 t F1 F2 FM alpha beta' (M*(1+|t|))) →
      ‖PRZZAStar.literal N d D H T (fun n => (coefficient js n:ℂ)) F1 F2 FM W Phi alpha beta'‖ ≤
        C*(T/d)*T^eta*(d:ℝ)^eta*(N:ℝ)^beta*M := by
  obtain ⟨Ca,hCa,ha⟩ := signedCells_bound K js eta beta heta hbeta
  obtain ⟨Co,hCo,ho⟩ := PRZZHiAllocatedCells.literal_bound W Phi hW hPhi hsP A B S hA hB hS
  refine ⟨Co*Ca,mul_nonneg hCo hCa.le,?_⟩
  intro N d hN hd T hT hL hNT D H M hM F1 F2 FM alpha beta' hFM hsM hz hc
  have hh := ho N d K (by omega) (by omega) hK T hT hL hNT D H
    (Ca*T^eta*(d:ℝ)^eta*(N:ℝ)^beta*M) (by positivity) js F1 F2 FM alpha beta' hFM hsM hz (by
      intro p hp t
      have hh := ha N d hN hd T (M*(1+|t|)) hNT hL (by positivity)
        D H p.1 p.2 t F1 F2 FM alpha beta' (hc p hp t)
      simpa only [mul_assoc] using hh)
  exact hh.trans_eq (by ring)

#print axioms signedCells_bound
#print axioms signedSum_bound
#print axioms literal_bound
end XiPrime8845.PRZZSignedCellsAggregate
