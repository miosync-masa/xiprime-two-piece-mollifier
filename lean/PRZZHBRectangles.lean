import PRZZHBBranches
import PRZZSharpAggregation

/-! Exact ordered branch pairs in the original dyadic rectangle. The
second coefficient is conjugated; repeated HB branches are never merged.
Balanced factor partitions and their DI identification are still separate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZHBRectangles
open PRZZHBBranches PRZZAStarRectangles
set_option maxHeartbeats 2000000

def mixed (N d j l : ℕ) (a b : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) : ℂ :=
  ∑ n1 ∈ PRZZDyadic.cell N j, ∑ n2 ∈ PRZZDyadic.cell N l,
    if n1.Coprime n2 ∧ d*n1 ≤ N ∧ d*n2 ≤ N then
      (a (d*n1)*F1 (d*n1)/(n1:ℂ)^α*PRZZMellinSeparation.twist n1 t)*
      (star (b (d*n2))*F2 (d*n2)*FM (x*n2)/(n2:ℂ)^β*PRZZMellinSeparation.twist n2 t)*
      PRZZKloostermanInputs.e (-(k:ℝ)*PRZZKloostermanInputs.inverseResidue n2 n1/n2)
    else 0

theorem mixed_diagonal (N d j l : ℕ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l a a F1 F2 FM α β x t k = rectangle N d j l a F1 F2 FM α β x t k := rfl

theorem mixed_add_left (N d j l : ℕ) (a b c : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l (a+b) c F1 F2 FM α β x t k =
      mixed N d j l a c F1 F2 FM α β x t k+mixed N d j l b c F1 F2 FM α β x t k := by
  unfold mixed
  simp only [Pi.add_apply,add_mul,add_div,← sum_add_distrib]
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro m hm
  split_ifs <;> ring

theorem mixed_add_right (N d j l : ℕ) (a b c : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l a (b+c) F1 F2 FM α β x t k =
      mixed N d j l a b F1 F2 FM α β x t k+mixed N d j l a c F1 F2 FM α β x t k := by
  unfold mixed
  simp only [Pi.add_apply,star_add,add_mul,add_div,mul_add,← sum_add_distrib]
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro m hm
  split_ifs <;> ring

def coeff (b : Branch) (n : ℕ) : ℂ := (value b n:ℂ)
def coeffTotal (bs : List Branch) (n : ℕ) : ℂ := (total bs n:ℂ)

theorem coeffTotal_cons (b : Branch) (bs : List Branch) :
    coeffTotal (b::bs) = coeff b+coeffTotal bs := by
  funext n
  simp [coeffTotal,coeff,total,ArithmeticFunction.add_apply]

theorem mixed_branch_pairs (N d j l : ℕ) (bs cs : List Branch) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    mixed N d j l (coeffTotal bs) (coeffTotal cs) F1 F2 FM α β x t k =
      (bs.flatMap (fun b => cs.map (fun c =>
        mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k))).sum := by
  have right (b : Branch) :
      mixed N d j l (coeff b) (coeffTotal cs) F1 F2 FM α β x t k =
        (cs.map (fun c => mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k)).sum := by
    induction cs with
    | nil => simp [coeffTotal,total,mixed]
    | cons c cs ih => rw [coeffTotal_cons,mixed_add_right,ih]; rfl
  induction bs with
  | nil => simp [coeffTotal,total,mixed]
  | cons b bs ih => rw [coeffTotal_cons,mixed_add_left,ih,right]; simp

/-- Every ordered pair of HB branches in the actual original rectangle.
The root cutoff, d*n constraints, dyadic cells and coprimality are exact. -/
theorem original_branch_pairs (N d j l K : ℕ) (js : List ℕ) (hK : 0 < K)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
    rectangle N d j l (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM α β x t k =
      (bs.flatMap (fun b => bs.map (fun c =>
        mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k))).sum := by
  dsimp only
  rw [rectangle_branches N d j l K js hK F1 F2 FM α β x t k]
  exact mixed_branch_pairs N d j l _ _ F1 F2 FM α β x t k

theorem list_budget {ι : Type*} (bs : List ι) (z : ι → ℂ) (B : ι → ℝ)
    (hb : ∀ b ∈ bs, ‖z b‖ ≤ B b) : ‖(bs.map z).sum‖ ≤ (bs.map B).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (hb b (by simp))
      (ih (fun c hc => hb c (by simp [hc]))))

/-- Budget every ordered branch pair without losing repeated terms. -/
theorem original_branch_bound (N d j l K : ℕ) (js : List ℕ) (hK : 0 < K)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) (B : Branch → Branch → ℝ)
    (hb : ∀ b ∈ branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js,
      ∀ c ∈ branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js,
      ‖mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k‖ ≤ B b c) :
    let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
    ‖rectangle N d j l (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM α β x t k‖ ≤
      (bs.flatMap (fun b => bs.map (B b))).sum := by
  dsimp only
  rw [original_branch_pairs N d j l K js hK F1 F2 FM α β x t k]
  let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
  -- Use a generic flattening identity, with independent outer/inner lists.
  have flat' {R : Type} [AddMonoid R] (xs : List Branch) (ys : List Branch) (z : Branch → Branch → R) :
      (xs.flatMap (fun b => ys.map (z b))).sum = (xs.map (fun b => (ys.map (z b)).sum)).sum := by
    induction xs with
    | nil => simp
    | cons b xs ih => simp [ih]
  rw [flat' bs bs (fun b c => mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k),
    flat' bs bs B]
  apply list_budget
  intro b hb'
  exact list_budget _ _ _ (hb b hb')

/-- The whole original signed frequency sum uses these exact branch pairs;
the original frequency set, nu coefficient and dyadic cells are unchanged. -/
theorem signedSum_branches (N d K : ℕ) (js : List ℕ) (hK : 0 < K) (D H : ℝ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x y t : ℝ) :
    let bs := branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js
    PRZZAStarNu.signedSum N d D H (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      F1 F2 FM α β x y t =
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
        (bs.flatMap (fun b => bs.map (fun c =>
          mixed N d j l (coeff b) (coeff c) F1 F2 FM α β x t k))).sum := by
  dsimp only
  rw [signedSum_rectangles]
  simp_rw [original_branch_pairs N d _ _ K js hK F1 F2 FM α β x t]

#print axioms mixed_diagonal
#print axioms mixed_add_left
#print axioms mixed_add_right
#print axioms mixed_branch_pairs
#print axioms original_branch_pairs
#print axioms original_branch_bound
#print axioms signedSum_branches
end XiPrime8845.PRZZHBRectangles
