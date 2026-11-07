import PRZZInfiniteTail
import PRZZL1Finite

/-! Lossless grouping of the four finite AFE indices. Fibres retain both
AFE truncations and every original coefficient. This is not yet elimination
of the k-index by a residue progression, nor a smooth M partition. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZAFEIndices
set_option maxHeartbeats 2000000

abbrev Index := (ℕ × ℕ) × (ℕ × ℕ)
abbrev Label := ℕ × ℤ × ℕ × ℕ

def indices (L N : ℕ) : Finset Index :=
  (Icc 1 L ×ˢ Icc 1 L) ×ˢ (Icc 1 N ×ˢ Icc 1 N)

def label (i : Index) : Label :=
  let d := Nat.gcd i.2.1 i.2.2
  let u := i.2.1/d
  let v := i.2.2/d
  (d,(i.1.1:ℤ)*u-(i.1.2:ℤ)*v,Nat.log 2 u,Nat.log 2 v)

def labels (L N : ℕ) : Finset Label := (indices L N).image label

def fibre (L N : ℕ) (z : Label) : Finset Index :=
  (indices L N).filter (fun i => label i = z)

theorem grouped {E : Type*} [AddCommMonoid E] (L N : ℕ) (f : Index → E) :
    (∑ i ∈ indices L N, f i) =
      ∑ z ∈ labels L N, ∑ i ∈ fibre L N z, f i := by
  symm
  apply sum_fiberwise_of_maps_to
  intro i hi
  exact mem_image_of_mem label hi

/-- The literal four-index AFE term, not an unspecified decomposition. -/
theorem direct_grouped (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (V : ℕ → ℝ → ℂ) (t : ℝ) :
    PRZZL1Finite.directSum L alpha beta V t *
      PRZZ.dirichletPolynomial a N (1/2+t*Complex.I) *
      star (PRZZ.dirichletPolynomial b N (1/2+t*Complex.I)) =
    ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      PRZZL1Finite.term a b alpha beta V t i.1.1 i.1.2 i.2.1 i.2.2 := by
  rw [PRZZL1Finite.direct_expansion, ← grouped]
  simp only [indices,sum_product]

/-- Disjoint label fibres do not introduce any multiplicity loss. -/
theorem mass_exact (L N : ℕ) (c : Index → ℂ) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z, ‖c i‖) =
      ∑ i ∈ indices L N, ‖c i‖ := (grouped L N _).symm

/-- Gcd reduction supplies the actual retained pair, including the original
cutoff evaluations at n and r, not cutoff evaluations at the quotients. -/
theorem reduced_rows (N n r : ℕ) (hn : n ∈ Icc 1 N) (hr : r ∈ Icc 1 N)
    (F1 F2 : ℝ → ℂ) (hf : F1 n ≠ 0) (hg : F2 r ≠ 0) :
    let d := Nat.gcd n r
    let u := n/d
    let v := r/d
    (u,v) ∈ PRZZSourceRows.rows N d (Nat.log 2 u) (Nat.log 2 v) F1 F2 := by
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hr0 : 0 < r := (mem_Icc.mp hr).1
  have hd : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn0
  have hdu : Nat.gcd n r*(n/Nat.gcd n r) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hdv : Nat.gcd n r*(r/Nat.gcd n r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
  have hu : 1 ≤ n/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_left r hn0) hd
  have hv : 1 ≤ r/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_right n hr0) hd
  have huN : n/Nat.gcd n r ≤ N := (Nat.div_le_self _ _).trans (mem_Icc.mp hn).2
  have hvN : r/Nat.gcd n r ≤ N := (Nat.div_le_self _ _).trans (mem_Icc.mp hr).2
  dsimp only
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨?_,?_⟩,?_,?_,?_,?_,?_⟩
  · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu,huN⟩,rfl⟩
  · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hv,hvN⟩,rfl⟩
  · simpa [hdu] using (mem_Icc.mp hn).2
  · simpa [hdv] using (mem_Icc.mp hr).2
  · exact Nat.coprime_div_gcd_div_gcd hd
  · have he : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by exact_mod_cast hdu
    simpa [he] using hf
  · have he : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by exact_mod_cast hdv
    simpa [he] using hg

/-- Original mollifier denominators pay the pair count before gcd grouping. -/
theorem reciprocal_total (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, |PRZZGCoefficient.coefficient js n|/(n:ℝ)) ≤
      (Nat.log 2 N+1:ℕ)*(Real.log N)^PRZZGCoefficient.degree js := by
  have he : (∑ n ∈ Icc 1 N, |PRZZGCoefficient.coefficient js n|/(n:ℝ)) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ n ∈ PRZZDyadic.cell N j,
        |PRZZGCoefficient.coefficient js n|/(n:ℝ) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hn).2))
  rw [he]
  exact (sum_le_sum (fun j hj => PRZZDyadicArithmeticMass.reciprocal_mass js N j hN)).trans_eq
    (by simp)

/-- Exact gcd/Delta/dyadic grouping preserves the reciprocal coefficient
mass. The two still-truncated AFE indices cost L^2; no extra label count is
charged. Removing this AFE truncation requires analytic decay separately. -/
theorem grouped_mass (L N : ℕ) (js : List ℕ) (hN : 1 ≤ N) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖((PRZZGCoefficient.coefficient js i.2.1:ℂ)*
        star (PRZZGCoefficient.coefficient js i.2.2:ℂ))/((i.2.1:ℂ)*i.2.2)‖) ≤
    (L:ℝ)^2*((Nat.log 2 N+1:ℕ):ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js) := by
  rw [mass_exact]
  simp only [indices,sum_product,norm_div,norm_mul,norm_star,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
  let s := ∑ n ∈ Icc 1 N, |PRZZGCoefficient.coefficient js n|/(n:ℝ)
  have he : (∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L, ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      |PRZZGCoefficient.coefficient js n| * |PRZZGCoefficient.coefficient js r|/
        ((n:ℝ)*r)) = (L:ℝ)^2*s^2 := by
    simp_rw [show ∀ n r : ℕ,
      |PRZZGCoefficient.coefficient js n| * |PRZZGCoefficient.coefficient js r|/((n:ℝ)*r) =
        (|PRZZGCoefficient.coefficient js n|/(n:ℝ))*(|PRZZGCoefficient.coefficient js r|/(r:ℝ))
      from fun n r => by ring]
    simp only [← sum_mul_sum]
    simp [s,pow_two]
    <;> ring
  rw [he]
  have hs : 0 ≤ s := sum_nonneg (by intro n hn; positivity)
  have hb := reciprocal_total js N hN
  change s ≤ _ at hb
  calc
    _ ≤ (L:ℝ)^2*(((Nat.log 2 N+1:ℕ):ℝ)*(Real.log N)^PRZZGCoefficient.degree js)^2 := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul]; simp only [Nat.mul_comm]; ring

/-- Delta is the signed reduced off-diagonal gap, with no natural-number
subtraction or discarded negative frequencies. -/
theorem gap_eq (i : Index) :
    (i.1.1:ℤ)*i.2.1-(i.1.2:ℤ)*i.2.2 =
      ((label i).1:ℤ)*(label i).2.1 := by
  have h1 : (Nat.gcd i.2.1 i.2.2:ℤ)*(i.2.1/Nat.gcd i.2.1 i.2.2:ℕ) = i.2.1 := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left i.2.1 i.2.2)
  have h2 : (Nat.gcd i.2.1 i.2.2:ℤ)*(i.2.2/Nat.gcd i.2.1 i.2.2:ℕ) = i.2.2 := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right i.2.1 i.2.2)
  dsimp only [label]
  calc
    _ = (i.1.1:ℤ)*((Nat.gcd i.2.1 i.2.2:ℤ)*(i.2.1/Nat.gcd i.2.1 i.2.2:ℕ)) -
        (i.1.2:ℤ)*((Nat.gcd i.2.1 i.2.2:ℤ)*(i.2.2/Nat.gcd i.2.1 i.2.2:ℕ)) := by rw [h1,h2]
    _ = _ := by ring

#print axioms gap_eq
#print axioms reciprocal_total
#print axioms grouped_mass
#print axioms reduced_rows
#print axioms grouped
#print axioms direct_grouped
#print axioms mass_exact
end XiPrime8845.PRZZAFEIndices
