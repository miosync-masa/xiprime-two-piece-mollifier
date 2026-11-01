import PRZZBranchDegrees
import PRZZHBRectangles

/-! Scalar HB weights are independent of the short cutoff. Repeated
branches are retained in lists, hence the absolute mass counts every term.
These identities do not yet account for dyadic factor-box multiplicities. -/
noncomputable section
open ArithmeticFunction
namespace XiPrime8845.PRZZBranchMass
open PRZZHBBranches PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

def weights (bs : List Branch) : List ℝ := bs.map Prod.fst

def allocations : ℕ → ℕ → List ℝ
  | J, 0 => if J=0 then [1] else []
  | J, L+1 => (List.range (J+1)).flatMap (fun k =>
      (allocations (J-k) L).map (fun c => (J.choose k:ℝ)*c))

theorem weighted_weights (fs : List (ArithmeticFunction ℝ)) (J : ℕ) :
    weights (weighted J fs) = allocations J fs.length := by
  induction fs generalizing J with
  | nil => by_cases h : J=0 <;> simp [weights,weighted,allocations,h]
  | cons f fs ih =>
    simp only [weighted,weights,List.map_flatMap,List.map_map,List.length_cons,allocations]
    congr 1
    funext k
    simpa only [weights,List.map_map,Function.comp_def] using
      congrArg (List.map (fun c : ℝ => (J.choose k:ℝ)*c)) (ih (J-k))

theorem scale_weights (c : ℝ) (bs : List Branch) :
    weights (bs.map (scale c)) = (weights bs).map (fun w => c*w) := by
  simp [weights,scale]

theorem multiply_weights (bs cs : List Branch) :
    weights (multiply bs cs) = (weights bs).flatMap (fun b => (weights cs).map (fun c => b*c)) := by
  simp [weights,multiply,join,List.map_flatMap,List.flatMap_map,Function.comp_def]

theorem mu_weights (y K : ℕ) : weights (muBranches y K) = weights (muBranches 0 K) := by
  simp [weights,muBranches]

theorem lambda_weights (y K J : ℕ) :
    weights (lambdaBranches y K J) = weights (lambdaBranches 0 K J) := by
  have he (y : ℕ) : weights (lambdaBranches y K J) =
      (List.range K).flatMap (fun j => (allocations J (2*(j+1))).map
        (fun w => ((-1:ℝ)^j*(K.choose (j+1):ℝ))*w)) := by
    unfold lambdaBranches
    change List.map Prod.fst _ = _
    rw [List.map_flatMap]
    congr 1
    funext j
    change weights ((weighted J (factors y j)).map (scale _)) = _
    rw [scale_weights,weighted_weights,factors_length]
  rw [he,he]

theorem branches_weights (y K : ℕ) (js : List ℕ) :
    weights (branches y K js) = weights (branches 0 K js) := by
  induction js with
  | nil => exact mu_weights y K
  | cons J js ih => simp only [branches,multiply_weights,ih,lambda_weights]

def mass (K : ℕ) (js : List ℕ) : ℝ := ((weights (branches 0 K js)).map abs).sum

theorem mass_nonneg (K : ℕ) (js : List ℕ) : 0 ≤ mass K js := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem mass_eq (y K : ℕ) (js : List ℕ) :
    ((branches y K js).map (fun b => |b.1|)).sum = mass K js := by
  have h := congrArg (fun ws : List ℝ => (ws.map abs).sum) (branches_weights y K js)
  simpa only [weights,List.map_map,Function.comp_def,mass] using h

/-- A bound on unscaled branch blocks costs exactly the fixed absolute
scalar mass, not a height-dependent number of branches. -/
theorem sum_bound (y K : ℕ) (js : List ℕ) (z : Branch → ℂ) (B : ℝ)
    (hz : ∀ b ∈ branches y K js, ‖z b‖ ≤ B) :
    ‖((branches y K js).map (fun b => (b.1:ℂ)*z b)).sum‖ ≤ mass K js*B := by
  have h := PRZZHBRectangles.list_budget (branches y K js)
    (fun b => (b.1:ℂ)*z b) (fun b => |b.1| * B) (by
      intro b hb
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hz b hb) (abs_nonneg _))
  apply h.trans_eq
  have he (bs : List Branch) : (bs.map (fun b => |b.1| * B)).sum =
      (bs.map (fun b => |b.1|)).sum*B := by
    induction bs with
    | nil => simp
    | cons b bs ih => simp [ih,add_mul]
  rw [he,mass_eq]

/-- Restore the actual signed scalar factors, including the conjugated
second coefficient, without replacing them by absolute values. -/
theorem mixed_unscaled (N d j l : ℕ) (b c : Branch) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x t : ℝ) (k : ℤ) :
    PRZZHBRectangles.mixed N d j l (PRZZHBRectangles.coeff b) (PRZZHBRectangles.coeff c)
      F1 F2 FM alpha beta x t k =
    ((b.1*c.1:ℝ):ℂ)*PRZZHBRectangles.mixed N d j l
      (fun n => (b.2.prod n:ℂ)) (fun n => (c.2.prod n:ℂ)) F1 F2 FM alpha beta x t k := by
  unfold PRZZHBRectangles.mixed PRZZHBRectangles.coeff value
  simp only [Finset.mul_sum,ArithmeticFunction.smul_map,smul_eq_mul,Complex.ofReal_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> ring

theorem pair_sum_bound (y K : ℕ) (js : List ℕ) (z : Branch → Branch → ℂ) (B : ℝ)
    (hz : ∀ b ∈ branches y K js, ∀ c ∈ branches y K js, ‖z b c‖ ≤ B) :
    ‖((branches y K js).map (fun b => (b.1:ℂ)*
      ((branches y K js).map (fun c => (c.1:ℂ)*z b c)).sum)).sum‖ ≤ (mass K js)^2*B := by
  have h := sum_bound y K js _ (mass K js*B) (by
    intro b hb
    exact sum_bound y K js (z b) B (hz b hb))
  exact h.trans_eq (by ring)

#print axioms mixed_unscaled
#print axioms pair_sum_bound
#print axioms weighted_weights
#print axioms branches_weights
#print axioms mass_eq
#print axioms sum_bound
end XiPrime8845.PRZZBranchMass
