import PRZZRowMellinBranches
import PRZZActualAggregate
import PRZZCoefficientPolarization

/-! Actual independent-label row bounds from Weil and DI. The original
coprimality, source cutoff and both frequency signs are retained. Constants
are selected before the finite complex profile vectors. These are explicit
row budgets, not yet the full optimized moment-minus-main-term estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex
namespace XiPrime8845.PRZZFiniteFamilyRows
open PRZZSupportedBranches PRZZSupportedSource PRZZSupportedAllocation
open PRZZSupportedSplit PRZZGCoefficient PRZZCoefficientSeparation
open PRZZAllSignedSources PRZZActualAggregate PRZZMellinSeparation
open PRZZAStarNu PRZZNuCoefficient PRZZHBRectangles
set_option maxHeartbeats 6000000

def signedRow (N d j l : ℕ) (D H : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  ∑ v ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y v *
    mixed N d j l a b F1 F2 FM alpha beta x t v

theorem diagonal_eq (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H a a F1 F2 FM alpha beta x y t =
      PRZZRowMellinBranches.signedRow N d j l D H a F1 F2 FM alpha beta x y t := rfl

theorem mixed_allocated (N d j l : ℕ) (hd : 1 ≤ d) (js ks : List ℕ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x t : ℝ) (v : ℤ) :
    mixed N d j l (fun n => (coefficient js n:ℂ))
      (fun n => (coefficient ks n:ℂ)) F1 F2 FM alpha beta x t v =
      ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
        (sourceG q.1 0 0 d h:ℂ)*residual N d q.2
          (PRZZSupportedBranches.row N d j l (fun _ => 1) (fun n => (coefficient ks n:ℂ))
            F1 F2 FM alpha beta x t v) h)).sum := by
  rw [mixed_row]
  simp_rw [row_factor N d j l (fun n => (coefficient js n:ℂ))
    (fun n => (coefficient ks n:ℂ)) F1 F2 FM alpha beta x t v]
  exact weighted_source N d hd js _

theorem mixed_blocks (N d j l K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H : ℝ) (js ks : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H (fun n => (coefficient js n:ℂ))
      (fun n => (coefficient ks n:ℂ)) F1 F2 FM alpha beta x y t =
      ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
        (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 ks D H x y t F1 F2 FM alpha beta)).sum := by
  unfold signedRow
  simp_rw [mixed_allocated N d j l hd]
  rw [PRZZActualSignedBranches.sum_list]
  congr 1
  apply List.map_congr_left
  intro q hq
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h hh
  have he (v : ℤ) := PRZZHiAllocatedCells.residual_eq N d h j K q.2
    (PRZZSupportedBranches.row N d j l (fun _ => 1) (fun n => (coefficient ks n:ℂ))
      F1 F2 FM alpha beta x t v) hK (by
        intro n hcut hlarge
        exact PRZZHiAllocatedCells.row_vanish N d h j l (by omega)
          (by have := (mem_hSupport N d h hh).1; omega)
          (fun _ => 1) (fun n => (coefficient ks n:ℂ))
          F1 F2 FM alpha beta x t v n hcut hlarge)
  simp_rw [he]
  unfold blocks
  rw [← PRZZActualSignedBranches.cells_eq_sources,mul_sum]
  apply sum_congr rfl
  intro v hv
  ring

def budget (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (eps eta beta T A : ℝ) (N d K j l : ℕ) : ℝ :=
  C*(d:ℝ)^eta*(N:ℝ)^beta*((allocations js).map (fun q =>
    w q*T^eta*PRZZActualAggregate.row (caps q) eps eta T A N K j l q.2)).sum

/-- A genuine mixed-basis supplier: no mixed norm bound is a premise. -/
theorem basis_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedRow N d j l D H (fun n => (coefficient js n:ℂ))
        (fun n => (coefficient ks n:ℂ)) (scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
      budget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    actual_blocks hWeil hDI K hK q.2 ks eps eta S Z heps heta hS hZ
      F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [mixed_blocks N d j l K hd (by omega)]
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*PRZZActualAggregate.row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*PRZZActualAggregate.row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 ks D H x y t (scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  have hscale (qs : List (List ℕ × List ℕ)) (f : (List ℕ × List ℕ) → ℝ) (r : ℝ) :
      (qs.map (fun q => f q*r)).sum = (qs.map f).sum*r := by
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  rw [hscale] at hh
  exact hh.trans_eq (by dsimp [budget,A]; ring)

theorem add_left (N d j l : ℕ) (D H : ℝ) (a b c : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H (a+b) c F1 F2 FM alpha beta x y t =
      signedRow N d j l D H a c F1 F2 FM alpha beta x y t +
      signedRow N d j l D H b c F1 F2 FM alpha beta x y t := by
  simp only [signedRow,mixed_add_left,mul_add,sum_add_distrib]

theorem add_right (N d j l : ℕ) (D H : ℝ) (a b c : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H a (b+c) F1 F2 FM alpha beta x y t =
      signedRow N d j l D H a b F1 F2 FM alpha beta x y t +
      signedRow N d j l D H a c F1 F2 FM alpha beta x y t := by
  simp only [signedRow,mixed_add_right,mul_add,sum_add_distrib]

theorem smul_left (N d j l : ℕ) (D H : ℝ) (a b : ℕ → ℂ) (z : ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H (z • a) b F1 F2 FM alpha beta x y t =
      z*signedRow N d j l D H a b F1 F2 FM alpha beta x y t := by
  simp only [signedRow,mixed,Pi.smul_apply,smul_eq_mul,mul_sum]
  apply sum_congr rfl; intro v hv
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro m hm
  split_ifs <;> ring

theorem smul_right (N d j l : ℕ) (D H : ℝ) (a b : ℕ → ℂ) (z : ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H a (z • b) F1 F2 FM alpha beta x y t =
      star z*signedRow N d j l D H a b F1 F2 FM alpha beta x y t := by
  simp only [signedRow,mixed,Pi.smul_apply,smul_eq_mul,star_mul,mul_sum]
  apply sum_congr rfl; intro v hv
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro m hm
  split_ifs <;> ring

open PRZZCoefficientPolarization

/-- Every ordered basis pair occurs, with the conjugate in the right slot. -/
theorem family_expansion {ι : Type*} [Fintype ι]
    (basis : ι → ℕ → ℂ) (z w : ι → ℂ) (N d j l : ℕ) (D H : ℝ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H (family basis z) (family basis w) F1 F2 FM alpha beta x y t =
      ∑ i, ∑ k, z i*star (w k)*
        signedRow N d j l D H (basis i) (basis k) F1 F2 FM alpha beta x y t := by
  classical
  have hf (u : ι → ℂ) : family basis u = ∑ i, u i • basis i := by
    funext n
    simp [family,Finset.sum_apply]
  have hl (b : ℕ → ℂ) :
      signedRow N d j l D H (family basis z) b F1 F2 FM alpha beta x y t =
        ∑ i, z i*signedRow N d j l D H (basis i) b F1 F2 FM alpha beta x y t := by
    let L : (ℕ → ℂ) →+ ℂ := {
      toFun := fun a => signedRow N d j l D H a b F1 F2 FM alpha beta x y t
      map_zero' := by simp [signedRow,mixed]
      map_add' := fun a c => add_left N d j l D H a c b F1 F2 FM alpha beta x y t }
    rw [hf]
    exact (map_sum L _ univ).trans (by
      apply sum_congr rfl; intro i hi
      exact smul_left N d j l D H (basis i) b (z i) F1 F2 FM alpha beta x y t)
  have hr (a : ℕ → ℂ) :
      signedRow N d j l D H a (family basis w) F1 F2 FM alpha beta x y t =
        ∑ k, star (w k)*signedRow N d j l D H a (basis k) F1 F2 FM alpha beta x y t := by
    let R : (ℕ → ℂ) →+ ℂ := {
      toFun := fun b => signedRow N d j l D H a b F1 F2 FM alpha beta x y t
      map_zero' := by simp [signedRow,mixed]
      map_add' := fun b c => add_right N d j l D H a b c F1 F2 FM alpha beta x y t }
    rw [hf]
    exact (map_sum R _ univ).trans (by
      apply sum_congr rfl; intro k hk
      exact smul_right N d j l D H a (basis k) (w k) F1 F2 FM alpha beta x y t)
  rw [hl]
  simp_rw [hr,mul_sum,mul_assoc]

/-- Weil and DI supply a square row budget uniformly on the radius-two
box. There is no assumed square or mixed estimate. The finite pair sum
retains label-dependent caps; its optimal outer-height absorption is separate. -/
theorem square_row_budget {ι : Type*} [Fintype ι] (labels : ι → List ℕ)
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : ι → ι → (List ℕ × List ℕ) → Caps,
      ∃ w : ι → ι → (List ℕ × List ℕ) → ℝ, ∃ C : ι → ι → ℝ,
      (∀ i k, 0 < C i k) ∧ (∀ i k q, 0 < w i k q) ∧
      ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ∀ z : ι → ℂ, (∀ i, ‖z i‖ ≤ 2) →
      let a := family (fun i n => (coefficient (labels i) n:ℂ)) z
      ‖signedRow N d j l D H a a (scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
        4*(∑ i, ∑ k, budget (C i k) (w i k) (caps i k) (labels i) eps eta beta T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K j l)*(1+|t|) := by
  classical
  choose caps w C hC hw hb using fun i k =>
    basis_bound hWeil hDI K hK (labels i) (labels k) eps eta beta S Z
      heps heta hbeta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hbeta z hzz
  dsimp only
  rw [family_expansion]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, ∑ k, 4*(budget (C i k) (w i k) (caps i k) (labels i) eps eta beta T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|)) := by
      apply sum_le_sum; intro i hi
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro k hk
      simp only [norm_mul,norm_star]
      have hp : ‖z i‖*‖z k‖ ≤ 4 := by nlinarith [hzz i,hzz k,norm_nonneg (z i),norm_nonneg (z k)]
      exact mul_le_mul hp (hb i k N d j l T Q D H x y t alpha betaShift
        hN hd hT hNT hdT hlog hA ha hz hbeta) (norm_nonneg _) (by norm_num)
    _ = _ := by
      simp only [mul_sum,sum_mul]
      apply sum_congr rfl; intro i hi
      apply sum_congr rfl; intro k hk
      ring

#print axioms diagonal_eq
#print axioms mixed_allocated
#print axioms mixed_blocks
#print axioms basis_bound
#print axioms add_left
#print axioms add_right
#print axioms smul_left
#print axioms smul_right
#print axioms family_expansion
#print axioms square_row_budget
end XiPrime8845.PRZZFiniteFamilyRows
