import WuIndependentWindows
import Zeta23.XiPrime.ZeroCount.Landau
import Zeta23.XiPrime.ExplicitFormula.ZeroFree

/-! Actual xi-prime counts, with analytic multiplicity. AF supplies the strip
theorem and the unit-height bound; neither is a hypothesis here. Only the
retained-window Wu counting inequality remains an input to the transfer. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology
namespace XiPrime8845.WuXiBands
open Zeta23 (ZeroConfig)
open Zeta23.XiPrime
set_option maxHeartbeats 1000000

def zeros : ZeroConfig :=
  xiDerivZeros xiDerivZerosInStrip_holds (xiDerivSeam_of_strip xiDerivZerosInStrip_holds)

def total (X : ℝ) : ℝ := Ncount 0 X
def good (X : ℝ) : ℝ := N0 0 X

theorem total_mono : Monotone total := by
  intro x y h
  unfold total
  exact_mod_cast (show Ncount 0 x ≤ Ncount 0 y by
    simpa [zeros] using zeros.N_mono (a:=0) (c:=0) le_rfl h)

theorem good_mono : Monotone good := by
  intro x y h
  have hh : zeros.N0 0 x ≤ zeros.N0 0 y := by
    apply zeros.finsum_mult_mono 0 y _ inter_subset_left
    rintro z ⟨⟨hz,hz0,hzx⟩,hl⟩
    exact ⟨⟨hz,hz0,hzx.trans h⟩,hl⟩
  have hh' : N0 0 x ≤ N0 0 y := by simpa [zeros] using hh
  unfold good
  exact_mod_cast hh'

theorem total_nonneg (X : ℝ) : 0 ≤ total X := Nat.cast_nonneg _
theorem good_nonneg (X : ℝ) : 0 ≤ good X := Nat.cast_nonneg _

theorem total_increment (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    total b-total a = (Ncount a b:ℝ) := by
  have h : Ncount 0 b = Ncount 0 a+Ncount a b := by
    simpa [zeros] using zeros.N_add ha hab
  unfold total
  rw [h,Nat.cast_add]
  ring

theorem good_increment (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    good b-good a = (N0 a b:ℝ) := by
  have h : zeros.N0 0 b = zeros.N0 0 a+zeros.N0 a b := by
    unfold ZeroConfig.N0
    rw [zeros.window_union ha hab,union_inter_distrib_right]
    apply finsum_mem_union _ ((zeros.window_finite 0 a).subset inter_subset_left)
      ((zeros.window_finite a b).subset inter_subset_left)
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨_,_,hza⟩,_⟩ ⟨⟨_,haz,_⟩,_⟩
    exact (not_lt_of_ge hza) haz
  have h' : N0 0 b = N0 0 a+N0 a b := by simpa [zeros] using h
  unfold good
  rw [h',Nat.cast_add]
  ring

/-- Actual all-height unit-strip count, including multiplicities. -/
theorem unit_count : ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ,
    (Ncount t (t+1):ℝ) ≤ A*Real.log (|t|+3) := by
  simpa using ZeroCount.xiDeriv_local_count xiDerivZerosInStrip_holds
    (xiDerivSeam_of_strip xiDerivZerosInStrip_holds)

/-- A single constant works for every positive unit band below X. -/
theorem unit_increment_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    ∀ t : ℝ, 0 ≤ t → t ≤ X → total (t+1)-total t ≤ C*Real.log X := by
  obtain ⟨A,hA,h⟩ := unit_count
  refine ⟨2*A,by positivity,?_⟩
  intro X hX t ht htX
  rw [total_increment t (t+1) ht (by linarith)]
  apply (h t).trans
  have hl : Real.log (|t|+3) ≤ 2*Real.log X := by
    rw [abs_of_nonneg ht,← show Real.log (X^2) = 2*Real.log X by simp only [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    nlinarith
  exact (mul_le_mul_of_nonneg_left hl (by linarith)).trans_eq (by ring)

/-- The deleted endpoint bands are now controlled for the literal target
counts. The local eta/xi-prime counting inequality is NOT proved here. -/
theorem inward_counting_transfer : ∃ C : ℝ, 0 < C ∧
    ∀ X l u v h B e : ℝ, 3 ≤ X → 0 ≤ l → 1 ≤ h → l ≤ X → h ≤ X → 0 ≤ B →
    u ∈ Icc l (l+1) → v ∈ Icc (h-1) h →
    B*(total v-total u)-e ≤ good v-good u →
    B*(total h-total l)-(e+2*B*C*Real.log X) ≤ good h-good l := by
  obtain ⟨C,hC,hband⟩ := unit_increment_uniform
  refine ⟨C,hC,?_⟩
  intro X l u v h B e hX hl hh hlX hhX hB hu hv hlocal
  have hb := hband X hX (h-1) (by linarith) (by linarith)
  simp only [sub_add_cancel] at hb
  convert WuIndependentWindows.unit_band_transfer total good total_mono good_mono
    l u v h B e (C*Real.log X) hB hu hv (hband X hX l hl hlX) hb hlocal using 1
  ring

open WuWindowTiling

/-- The endpoint-band hypotheses in the geometric aggregation are now
discharged for actual xi-prime counts. The local analytic gate is retained. -/
theorem global_bound : ∃ C : ℝ, 0 < C ∧ ∀ δ X K B eps : ℝ,
    0 < δ → δ < 1/2 → 3 ≤ X → 0 ≤ B →
    ∀ (n : ℕ) (u v e : ℕ → ℝ),
    (∀ j < n, 1 ≤ boundary δ X j) → boundary δ X n ≤ K →
    (∀ j ∈ Finset.range n, u j ∈ Icc (boundary δ X (j+1)) (boundary δ X (j+1)+1)) →
    (∀ j ∈ Finset.range n, v j ∈ Icc (boundary δ X j-1) (boundary δ X j)) →
    (∀ j ∈ Finset.range n, B*(total (v j)-total (u j))-e j ≤ good (v j)-good (u j)) →
    (∑ j ∈ Finset.range n, e j) ≤ eps*X*Real.log X →
    B*total X-eps*X*Real.log X-
      2*B*C*(Real.log X+Real.log X^2/(-Real.log (ratio δ)))-B*total K ≤ good X := by
  obtain ⟨C,hC,hband⟩ := unit_increment_uniform
  refine ⟨C,hC,?_⟩
  intro δ X K B eps hδ hd hX hB n u v e hstop hcut hu hv hlocal herr
  have hb (j : ℕ) : 0 < boundary δ X j ∧ boundary δ X j ≤ X := by
    refine ⟨boundary_pos δ X hδ hd (by linarith) j,?_⟩
    simpa only [boundary,pow_zero,mul_one] using
      boundary_antitone δ X hδ hd (by linarith) (Nat.zero_le j)
  apply WuIndependentWindows.global_independent_bound δ X K B C eps hδ hd
    (by linarith) hB hC.le total good total_mono good_mono good_nonneg n u v e
    hstop hcut hu hv _ _ hlocal herr
  · intro j hj
    exact hband X hX _ (hb _).1.le (hb _).2
  · intro j hj
    have hh := hband X hX (boundary δ X j-1)
      (by linarith [hstop j (Finset.mem_range.mp hj)]) (by linarith [(hb j).2])
    simpa only [sub_add_cancel] using hh

#print axioms total_mono
#print axioms good_mono
#print axioms total_increment
#print axioms good_increment
#print axioms unit_count
#print axioms unit_increment_uniform
#print axioms inward_counting_transfer
#print axioms global_bound
end XiPrime8845.WuXiBands
