import PRZZNativeFamily

/-! Exact separate components of the original family after the native
pair/gap bijection. Boundary uses the actual row-dependent cover; the
large-gap complement, the infinite tail and freezing error stay literal. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZNativeComponents
open PRZZNativeFamily
set_option maxHeartbeats 5000000

inductive Part | central | tail | boundary | freeze | outside

def row (part : Part) (L J : ℕ) (F F1 F2 : ℝ → ℂ) (M : ℝ)
    (z : PRZZAStar.Index) (alpha beta : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ) : ℂ :=
  let c := PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))
  let small := |(z.2.1:ℝ)| ≤ M*z.1.1/4
  match part with
  | .central => if small then c*PRZZCentralTail.central F M 1
      (PRZZCentralTail.residue z/z.1.2) z alpha beta (alpha+beta) t J else 0
  | .tail => if small then c*(∑' k, PRZZFrozenTail.pair F M 1
      (PRZZCentralTail.residue z/z.1.2) z alpha beta (alpha+beta) J k t) else 0
  | .boundary => if small then c*PRZZWeightedSourcePoisson.boundary L
      (PRZZActualPoissonError.cover L M z) F M z alpha beta (alpha+beta) t else 0
  | .freeze => if small then c*PRZZUnfrozenPoisson.errorSum L F M z
      alpha beta (alpha+beta) t else 0
  | .outside => if small then 0 else PRZZUnfrozenPoisson.afeRow L F F1 F2 M z
      alpha beta (alpha+beta) a d t

theorem row_decomposition (L J : ℕ) (F F1 F2 : ℝ → ℂ) (M : ℝ)
    (z : PRZZAStar.Index) (alpha beta : ℂ) (a : ℕ → ℂ) (d : ℕ) (t : ℝ) :
    PRZZAllPoissonRows.resolved L J F F1 F2 M z alpha beta a d t =
      row .central L J F F1 F2 M z alpha beta a d t+
      row .tail L J F F1 F2 M z alpha beta a d t-
      row .boundary L J F F1 F2 M z alpha beta a d t+
      row .freeze L J F F1 F2 M z alpha beta a d t+
      row .outside L J F F1 F2 M z alpha beta a d t := by
  unfold PRZZAllPoissonRows.resolved row
  dsimp only
  split_ifs <;> (try unfold PRZZActualPoissonError.poissonPart) <;> ring

def component (part : Part) (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
    ∑ delta ∈ gaps L N n r, if delta ≠ 0 then
      row part L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta a (Nat.gcd n r) t else 0

theorem family_decomposition (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F F1 F2 a alpha beta t =
      component .central L J N F F1 F2 a alpha beta t+
      component .tail L J N F F1 F2 a alpha beta t-
      component .boundary L J N F F1 F2 a alpha beta t+
      component .freeze L J N F F1 F2 a alpha beta t+
      component .outside L J N F F1 F2 a alpha beta t := by
  rw [PRZZNativeFamily.family]
  simp_rw [row_decomposition]
  have hi (p : Prop) [Decidable p] (a b c d e : ℂ) :
      (if p then a+b-c+d+e else 0) =
        (if p then a else 0)+(if p then b else 0)-(if p then c else 0)+
          (if p then d else 0)+(if p then e else 0) := by split_ifs <;> ring
  simp only [component,hi,sum_add_distrib,sum_sub_distrib]

#print axioms row_decomposition
#print axioms family_decomposition

/-- The original normalized Poisson coefficient equals the literal gcd
coefficient used in the arithmetic boundary assembly, as a complex
number, including both valued cutoffs and both shifted denominators. -/
theorem arithmetic_coefficient (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (w : ℤ × ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha ((u,v),w)/((u:ℂ)*(v:ℂ)) =
      PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v := by
  have huC : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [PRZZDiagonalAssembly.coefficient_eq a F1 F2 alpha beta d u v hd hu hv]
  unfold PRZZUnfrozenPoisson.arithmetic
  dsimp only
  rw [Complex.cpow_add _ _ huC,Complex.cpow_add _ _ hvC]
  simp only [Complex.cpow_one,div_div]
  congr 1 <;> ring

#print axioms arithmetic_coefficient
end XiPrime8845.PRZZNativeComponents
