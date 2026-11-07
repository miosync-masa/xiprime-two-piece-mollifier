import PRZZRejectedExhaustion

/-! Exact arithmetic dyadic partition on the original coefficient range.
Both evaluated cutoff values survive until their finite product sum is one.
This reconstructs the full family, not a smallness claim for one window. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZArithmeticCutoffPartition
open PRZZMellinSeparation
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem profile_unity (P : ℝ → ℂ) (K N n : ℕ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hn : n ∈ Icc 1 N) (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    (∑ j ∈ range K, scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^j) n) = 1 := by
  have hh := PRZZAFEProgression.piece_sum_one P 1 n K (by norm_num) hleft hright
    (by exact_mod_cast (mem_Icc.mp hn).1)
    (by simpa using (show (n:ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn).2).trans hK)
  simpa only [mul_one,PRZZWRowLimit.profile_piece,scaledCutoff] using hh

theorem product_unity (P : ℝ → ℂ) (K N n r : ℕ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hn : n ∈ Icc 1 N) (hr : r ∈ Icc 1 N) (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    (∑ p ∈ range K ×ˢ range K,
      scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1) n*
      scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2) r) = 1 := by
  simp only [sum_product,← mul_sum,← sum_mul]
  rw [profile_unity P K N n hleft hright hn hK,profile_unity P K N r hleft hright hr hK,one_mul]

theorem resolved_values (L J d : ℕ) (F G H : ℝ → ℂ) (M : ℝ)
    (z : PRZZAStar.Index) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.resolved L J F G H M z alpha beta a d t =
      (G ((d:ℝ)*z.1.1)*H ((d:ℝ)*z.1.2))*
        PRZZAllPoissonRows.resolved L J F (fun _ => 1) (fun _ => 1) M z alpha beta a d t := by
  unfold PRZZAllPoissonRows.resolved
  split_ifs
  · unfold PRZZActualPoissonError.poissonPart PRZZUnfrozenPoisson.arithmetic
    ring
  · unfold PRZZUnfrozenPoisson.afeRow
    simp only [mul_sum]
    apply sum_congr rfl; intro m hm
    apply sum_congr rfl; intro k hk
    split_ifs <;> ring

/-- A finite valued partition on the original n,r coordinates lifts to
the actual complete Poisson family, including every native filter. -/
theorem family_cover {ι : Type*} (qs : Finset ι) (G H : ι → ℝ → ℂ)
    (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ)
    (hcover : ∀ n ∈ Icc 1 N, ∀ r ∈ Icc 1 N, (∑ i ∈ qs, G i n*H i r) = 1) :
    (∑ i ∈ qs, PRZZAllPoissonRows.family L J N F (G i) (H i) a alpha beta t) =
      PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t := by
  simp_rw [PRZZNativeGcdGrid.family_reindex]
  rw [sum_comm]
  apply sum_congr rfl; intro s hs
  rw [sum_comm]
  apply sum_congr rfl; intro d hd
  rw [sum_comm]
  apply sum_congr rfl; intro u hu
  rw [sum_comm]
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    rw [sum_comm]
    apply sum_congr rfl; intro delta hdelta
    by_cases hz : delta ≠ 0
    · simp only [if_pos hz]
      have hrow (i : ι) := resolved_values L J d (PRZZWRowLimit.profile F)
        (G i) (H i) ((2:ℝ)^s) ((u,v),(-delta,1)) a alpha beta t
      simp_rw [hrow]
      rw [← sum_mul]
      have hn : d*u ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hu).1,had.2.1⟩
      have hr : d*v ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hv).1,had.2.2⟩
      simpa only [Nat.cast_mul,one_mul] using congrArg (fun c : ℂ => c*
        PRZZAllPoissonRows.resolved L J (PRZZWRowLimit.profile F) (fun _ => 1) (fun _ => 1)
          ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t) (hcover (d*u) hn (d*v) hr)
    · simp [hz]
  · simp [had]

theorem family_partition (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    (∑ p ∈ range K ×ˢ range K,
      PRZZAllPoissonRows.family L J N F
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a alpha beta t) =
      PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t := by
  apply family_cover
  intro n hn r hr
  exact product_unity P K N n r hleft hright hn hr hK

/-- A concrete arithmetic scale count, chosen before all AFE truncations.
No logarithmic grid-count assumption is needed for exact reconstruction. -/
theorem scale_count (N : ℕ) : (N:ℝ) ≤ (2:ℝ)^(N+1)/2 := by
  have hh : N ≤ 2^N := Nat.le_of_lt Nat.lt_two_pow_self
  have hc : (N:ℝ) ≤ (2:ℝ)^N := by exact_mod_cast hh
  simpa only [pow_succ,mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hc

theorem dyadic_scale_count (N : ℕ) : (N:ℝ) ≤ (2:ℝ)^(Nat.log 2 N+2)/2 := by
  have hh : N < 2^(Nat.log 2 N+1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hc : (N:ℝ) ≤ (2:ℝ)^(Nat.log 2 N+1) := by exact_mod_cast hh.le
  simpa only [show Nat.log 2 N+2 = (Nat.log 2 N+1)+1 by omega,pow_succ,
    mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hc

theorem family_continuous (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (hF : ContDiff ℝ ∞ F)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (hs : alpha+beta ≠ 0) (hT : 0 < T) :
    ContinuousOn (PRZZAllPoissonRows.family L J N F G H a alpha beta) (Set.Icc T (2*T)) := by
  have hh := PRZZPrunedAFEError.selected_continuous L J N F G H hF hleft hright a
    (fun _ _ => True) alpha beta hs T hT
  apply hh.congr
  intro t ht
  simp only [PRZZAllPoissonRows.family,PRZZSourceMaskFamily.selectedFamily,and_true]

/-- Move the valued arithmetic partition through the actual weighted time
integral. Integrability is supplied for each finite family by its native
AFE representation, including the time-varying dual Gamma weight if used. -/
theorem partition_time (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0) (hs : alpha+beta ≠ 0) (hT : 0 < T)
    (hphi : ContinuousOn phi (Set.Icc T (2*T))) :
    (∫ t in Set.Icc T (2*T), phi t*
      PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t) =
    ∑ p ∈ range K ×ˢ range K, ∫ t in Set.Icc T (2*T), phi t*
      PRZZAllPoissonRows.family L J N F
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a alpha beta t := by
  have he (t : ℝ) := family_partition P F K L J N a alpha beta t hleft hright hK
  conv_lhs => arg 2; ext t; rw [← he,mul_sum]
  apply integral_finsetSum
  intro p hp
  exact (hphi.mul (family_continuous L J N F _ _ a alpha beta T hF hFl hFr hs hT)).integrableOn_compact isCompact_Icc

#print axioms profile_unity
#print axioms product_unity
#print axioms resolved_values
#print axioms family_cover
#print axioms family_partition
#print axioms scale_count
#print axioms dyadic_scale_count
#print axioms family_continuous
#print axioms partition_time
end XiPrime8845.PRZZArithmeticCutoffPartition
