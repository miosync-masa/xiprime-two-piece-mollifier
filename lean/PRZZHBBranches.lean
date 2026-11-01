import PRZZFullHeathBrown
import PRZZGroupedConvolution

/-! Literal finite branches of the whole Heath-Brown coefficient. Lists
retain repeated branches and their signed binomial/multinomial weights.
No balanced factor partition is assumed to exist in this module. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZHBBranches
open PRZZHeathBrown PRZZWeightedHeathBrown PRZZFullHeathBrown
set_option maxHeartbeats 2000000

abbrev Branch := ℝ × List (ArithmeticFunction ℝ)
def value (b : Branch) : ArithmeticFunction ℝ := b.1 • b.2.prod
def total (bs : List Branch) : ArithmeticFunction ℝ := (bs.map value).sum
def scale (c : ℝ) (b : Branch) : Branch := (c*b.1,b.2)
def join (a b : Branch) : Branch := (a.1*b.1,a.2++b.2)
def multiply (as bs : List Branch) : List Branch :=
  as.flatMap (fun a => bs.map (join a))

theorem value_scale (c : ℝ) (b : Branch) : value (scale c b) = c • value b := by
  simp [value,scale,mul_smul]

theorem value_join (a b : Branch) : value (join a b) = value a*value b := by
  simp only [value,join,List.prod_append,smul_mul_assoc,mul_smul_comm]
  rw [← mul_smul,mul_comm b.1 a.1]

theorem total_scale (c : ℝ) (bs : List Branch) :
    total (bs.map (scale c)) = c • total bs := by
  induction bs with
  | nil => simp [total]
  | cons b bs ih => simpa [total,value_scale,smul_add] using congrArg (fun x => c • value b+x) ih

theorem total_flatMap {ι : Type*} (is : List ι) (bs : ι → List Branch) :
    total (is.flatMap bs) = (is.map (fun i => total (bs i))).sum := by
  induction is with
  | nil => simp [total]
  | cons i is ih => simpa [total,List.sum_append] using congrArg (fun x => total (bs i)+x) ih

theorem total_join (a : Branch) (bs : List Branch) :
    total (bs.map (join a)) = value a*total bs := by
  induction bs with
  | nil => simp [total]
  | cons b bs ih => simpa [total,value_join,mul_add] using congrArg (fun x => value a*value b+x) ih

theorem total_multiply (as bs : List Branch) : total (multiply as bs) = total as*total bs := by
  induction as with
  | nil => simp [multiply,total]
  | cons a as ih =>
    change total (bs.map (join a) ++ multiply as bs) = _
    have hadd (xs ys : List Branch) : total (xs++ys) = total xs+total ys := by
      simp [total]
    rw [hadd,total_join,ih]
    change _ = (value a+total as)*total bs
    ring

/-- Every successive binomial allocation is retained, including repeats. -/
def weighted : ℕ → List (ArithmeticFunction ℝ) → List Branch
  | J, [] => if J=0 then [(1,[])] else []
  | J, f::fs => (List.range (J+1)).flatMap (fun k =>
      (weighted (J-k) fs).map (fun b => ((J.choose k:ℝ)*b.1,weight k f::b.2)))

theorem range_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,sum_range_succ,ih]

theorem weighted_total (fs : List (ArithmeticFunction ℝ)) (J : ℕ) :
    total (weighted J fs) = expand J fs := by
  induction fs generalizing J with
  | nil => by_cases h : J=0 <;> simp [weighted,expand,h,total,value]
  | cons f fs ih =>
    rw [weighted,total_flatMap,expand]
    rw [range_sum]
    apply sum_congr rfl
    intro k hk
    have hm (bs : List Branch) :
        total (bs.map (fun b => ((J.choose k:ℝ)*b.1,weight k f::b.2))) =
          (J.choose k:ℝ) • (weight k f*total bs) := by
      induction bs with
      | nil => simp [total]
      | cons b bs ih =>
        simp only [List.map_cons,total,List.sum_cons] at ih ⊢
        rw [ih]
        simp [value,smul_add,mul_add,mul_smul]
    rw [hm,ih]

def muBranches (y K : ℕ) : List Branch := (List.range K).map (fun j =>
  (((-1:ℝ)^j*(K.choose (j+1):ℝ)),
    List.replicate (j+1) (truncatedMu y) ++ List.replicate j (ζ : ArithmeticFunction ℝ)))

def lambdaBranches (y K J : ℕ) : List Branch := (List.range K).flatMap (fun j =>
  (weighted J (factors y j)).map (scale ((-1:ℝ)^j*(K.choose (j+1):ℝ))))

def branches (y K : ℕ) : List ℕ → List Branch
  | [] => muBranches y K
  | J::js => multiply (branches y K js) (lambdaBranches y K J)

theorem mu_total (y K : ℕ) : total (muBranches y K) = muExpansion y K := by
  simp only [total,muBranches,List.map_map]
  rw [range_sum]
  unfold muExpansion
  apply sum_congr rfl
  intro j hj
  simp only [Function.comp_def,value,List.prod_append,List.prod_replicate]
  rw [← scalar_coefficient]
  ring

theorem lambda_total (y K J : ℕ) : total (lambdaBranches y K J) = lambdaExpansion y K J := by
  rw [lambdaBranches,total_flatMap,range_sum]
  simp only [total_scale,weighted_total,lambdaExpansion]

theorem branches_total (y K : ℕ) (js : List ℕ) :
    total (branches y K js) = fullExpansion y K js := by
  induction js with
  | nil => exact mu_total y K
  | cons J js ih => rw [branches,total_multiply,ih,lambda_total,fullExpansion]

/-- Exact original coefficient, not an absolute-value replacement. -/
theorem coefficient_branches (y K : ℕ) (js : List ℕ) (n : ℕ)
    (hn : n < (y+1)^K) :
    PRZZGCoefficient.coefficient js n = total (branches y K js) n := by
  rw [branches_total]
  exact coefficient_eq_fullExpansion y K js n hn

theorem rectangle_branches (N d j l K : ℕ) (js : List ℕ) (hK : 0 < K)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    PRZZAStarRectangles.rectangle N d j l
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 FM α β x t k =
    PRZZAStarRectangles.rectangle N d j l
      (fun n => (total (branches ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js) n:ℂ))
      F1 F2 FM α β x t k := by
  simp only [branches_total]
  exact rectangle_heathBrown_root N d j l K js hK F1 F2 FM α β x t k

#print axioms value_join
#print axioms total_multiply
#print axioms weighted_total
#print axioms mu_total
#print axioms lambda_total
#print axioms branches_total
#print axioms coefficient_branches
#print axioms rectangle_branches

end XiPrime8845.PRZZHBBranches
