import PRZZNativeComponents
import PRZZArithmeticBoundaryFamily

/-! The missing lossless bijection from original (n,r) pairs to the
admissible gcd grid. Arbitrary label, gap, cover and active filters can
be retained in f, including dependence on the original n and r. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZNativeGcdGrid
open PRZZDiagonalAssembly PRZZArithmeticBoundaryFamily
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

def reduce (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  ((Nat.gcd p.1 p.2,p.1/Nat.gcd p.1 p.2),p.2/Nat.gcd p.1 p.2)
def restore (i : (ℕ × ℕ) × ℕ) : ℕ × ℕ := (i.1.1*i.1.2,i.1.1*i.2)

theorem restore_reduce (p : ℕ × ℕ) : restore (reduce p) = p := by
  exact Prod.ext (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2))
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2))

theorem reduce_restore (i : (ℕ × ℕ) × ℕ) (hd : 0 < i.1.1)
    (hc : i.1.2.Coprime i.2) : reduce (restore i) = i := by
  have hg : Nat.gcd (i.1.1*i.1.2) (i.1.1*i.2) = i.1.1 := by
    rw [Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
  simp only [reduce,restore,hg,Nat.mul_div_cancel_left _ hd,Prod.mk.eta]

theorem sum_reindex {E : Type*} [AddCommMonoid E] (N : ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → E) :
    (∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      f n r (Nat.gcd n r) (n/Nat.gcd n r) (r/Nat.gcd n r)) =
      ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if admissible N d u v then f (d*u) (d*v) d u v else 0 := by
  let s := (grid N).filter (fun i => admissible N i.1.1 i.1.2 i.2)
  have he : (∑ i ∈ s, f (restore i).1 (restore i).2 i.1.1 i.1.2 i.2) =
      ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, f p.1 p.2 (reduce p).1.1 (reduce p).1.2 (reduce p).2 := by
    apply sum_bij (fun i _ => restore i)
    · intro i hi
      obtain ⟨hi,hc,huN,hvN⟩ := mem_filter.mp hi
      have hdu := mem_product.mp (mem_product.mp hi).1
      have hv := mem_product.mp hi |>.2
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by
        have := (mem_Icc.mp hdu.1).1
        have := (mem_Icc.mp hdu.2).1
        dsimp [restore]; nlinarith,huN⟩,mem_Icc.mpr ⟨by
        have := (mem_Icc.mp hdu.1).1
        have := (mem_Icc.mp hv).1
        dsimp [restore]; nlinarith,hvN⟩⟩
    · intro i hi k hk he
      have hi' := mem_filter.mp hi
      have hk' := mem_filter.mp hk
      have hdi := (mem_Icc.mp (mem_product.mp (mem_product.mp hi'.1).1).1).1
      have hdk := (mem_Icc.mp (mem_product.mp (mem_product.mp hk'.1).1).1).1
      have hh := congrArg reduce he
      rw [reduce_restore i hdi hi'.2.1,reduce_restore k hdk hk'.2.1] at hh
      exact hh
    · intro p hp
      have hn := mem_Icc.mp (mem_product.mp hp).1
      have hr := mem_Icc.mp (mem_product.mp hp).2
      have hd : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hn.1
      have hu : 0 < p.1/Nat.gcd p.1 p.2 := Nat.div_pos (Nat.gcd_le_left p.2 hn.1) hd
      have hv : 0 < p.2/Nat.gcd p.1 p.2 := Nat.div_pos (Nat.gcd_le_right p.1 hr.1) hd
      refine ⟨reduce p,mem_filter.mpr ⟨?_,?_,?_,?_⟩,restore_reduce p⟩
      · exact mem_product.mpr ⟨mem_product.mpr
          ⟨mem_Icc.mpr ⟨hd,(Nat.gcd_le_left p.2 hn.1).trans hn.2⟩,
           mem_Icc.mpr ⟨hu,(Nat.div_le_self _ _).trans hn.2⟩⟩,
          mem_Icc.mpr ⟨hv,(Nat.div_le_self _ _).trans hr.2⟩⟩
      · exact Nat.coprime_div_gcd_div_gcd hd
      · simpa only [reduce,restore] using (show (restore (reduce p)).1 ≤ N by rw [restore_reduce]; exact hn.2)
      · simpa only [reduce,restore] using (show (restore (reduce p)).2 ≤ N by rw [restore_reduce]; exact hr.2)
    · intro i hi
      have hi' := mem_filter.mp hi
      have hd := (mem_Icc.mp (mem_product.mp (mem_product.mp hi'.1).1).1).1
      rw [reduce_restore i hd hi'.2.1]
  symm
  simpa only [s,grid,sum_filter,sum_product,restore,reduce] using he

/-- Simultaneous original-label, original-pair and gcd-grid reindex for
each of the five *actual* Poisson components. In particular boundary
keeps its L,M,u,v,Delta-dependent cover, and tail keeps its cutoff J. -/
theorem component_reindex (part : PRZZNativeComponents.Part) (L J N : ℕ)
    (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    PRZZNativeComponents.component part L J N F F1 F2 a alpha beta t =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v), if delta ≠ 0 then
            PRZZNativeComponents.row part L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
              ((u,v),(-delta,1)) alpha beta a d t else 0 else 0 := by
  unfold PRZZNativeComponents.component
  apply sum_congr rfl
  intro s hs
  exact sum_reindex (E := ℂ) N (fun n r d u v =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N n r, if delta ≠ 0 then
      PRZZNativeComponents.row part L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
        ((u,v),(-delta,1)) alpha beta a d t else 0)

#print axioms restore_reduce
#print axioms reduce_restore
#print axioms sum_reindex
#print axioms component_reindex

/-- Full original family on the same arithmetic grid as the boundary
envelope. Neither infeasible labels nor large gaps are silently erased. -/
theorem family_reindex (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F F1 F2 a alpha beta t =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v), if delta ≠ 0 then
            PRZZAllPoissonRows.resolved L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
              ((u,v),(-delta,1)) alpha beta a d t else 0 else 0 := by
  rw [PRZZNativeFamily.family]
  apply sum_congr rfl
  intro s hs
  exact sum_reindex (E := ℂ) N (fun n r d u v =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N n r, if delta ≠ 0 then
      PRZZAllPoissonRows.resolved L J (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
        ((u,v),(-delta,1)) alpha beta a d t else 0)

#print axioms family_reindex

/-- The actual source cutoff may depend on every row index. Its change
is absorbed by the *central plus tail* expression, not by declaring the
intermediate Fourier band zero. This permits the tail theorem's literal
ceil(poissonCutoff) in place of the original uniform J. -/
theorem family_local_cutoff (L J N : ℕ) (F F1 F2 : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hleft : ∀ y ≤ (1/2:ℝ), F y = 1)
    (hright : ∀ y, 1 ≤ y → F y = 0) (a : ℕ → ℂ)
    (alpha beta : ℂ) (hsigma : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t)
    (Jloc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ) :
    PRZZAllPoissonRows.family L J N F F1 F2 a alpha beta t =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v), if delta ≠ 0 then
            PRZZAllPoissonRows.resolved L (Jloc s d u v delta)
              (PRZZWRowLimit.profile F) F1 F2 ((2:ℝ)^s)
              ((u,v),(-delta,1)) alpha beta a d t else 0 else 0 := by
  rw [family_reindex]
  have hp := PRZZWRowLimit.profile_regular F hF hleft hright
  apply sum_congr rfl
  intro s hss
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  by_cases had : admissible N d u v
  · simp only [if_pos had]
    apply sum_congr rfl
    intro delta hdelta
    by_cases hzero : delta ≠ 0
    · simp only [if_pos hzero]
      rw [← PRZZAllPoissonRows.row_resolved L J (PRZZWRowLimit.profile F) F1 F2
        hp.1 hp.2.2 ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t (by positivity) ht
        (mem_Icc.mp hd).1 (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 had.1 hsigma,
        ← PRZZAllPoissonRows.row_resolved L (Jloc s d u v delta)
          (PRZZWRowLimit.profile F) F1 F2 hp.1 hp.2.2 ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t
          (by positivity) ht (mem_Icc.mp hd).1 (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 had.1 hsigma]
    · simp [hzero]
  · simp [had]

#print axioms family_local_cutoff
end XiPrime8845.PRZZNativeGcdGrid
