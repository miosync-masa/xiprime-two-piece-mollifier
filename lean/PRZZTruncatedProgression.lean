import PRZZCongruencePoisson

/-! Reindex the weighted, doubly truncated AFE gap sum by progression
indices. Both original cutoffs remain in a finite image, and every weight
is evaluated at the reconstructed pair. No smoothness of a sharp mask. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTruncatedProgression
open PRZZKloostermanInputs PRZZCongruencePoisson
set_option maxHeartbeats 2000000

def retained (L u v : ℕ) (delta : ℤ) : Finset ℤ :=
  (Icc 1 (L:ℤ)).filter (fun m => (v:ℤ) ∣ m*u-delta ∧
    1 ≤ (m*u-delta)/v ∧ (m*u-delta)/v ≤ L)

def residue (u v : ℕ) (delta : ℤ) : ℤ := delta*(inverseResidue v u:ℤ)

def progressionIndices (L u v : ℕ) (delta : ℤ) : Finset ℤ :=
  (retained L u v delta).image (fun m => (m-residue u v delta)/v)

theorem reconstruct (L u v : ℕ) (delta m : ℤ)
    (hv : 0 < v) (hc : u.Coprime v) (hm : m ∈ retained L u v delta) :
    residue u v delta+(v:ℤ)*((m-residue u v delta)/v)=m := by
  have hd := (congruence_iff u v hv hc m delta).mp (mem_filter.mp hm).2.1
  change (v:ℤ) ∣ m-residue u v delta at hd
  rw [mul_comm (v:ℤ),Int.ediv_mul_cancel hd]
  ring

/-- The new finite domain keeps both m and k cutoffs, including the signed gap. -/
theorem progression_bounds (L u v : ℕ) (delta j : ℤ) (hv : 0 < v)
    (hc : u.Coprime v) (hj : j ∈ progressionIndices L u v delta) :
    let m := residue u v delta+(v:ℤ)*j
    1 ≤ m ∧ m ≤ L ∧ 1 ≤ (m*u-delta)/v ∧ (m*u-delta)/v ≤ L := by
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hj
  dsimp only
  rw [reconstruct L u v delta m hv hc hm]
  exact ⟨(mem_Icc.mp (mem_filter.mp hm).1).1,
    (mem_Icc.mp (mem_filter.mp hm).1).2,(mem_filter.mp hm).2.2⟩

/-- Equality of sums, not merely membership in a congruence class. -/
theorem weighted_sum (L u v : ℕ) (delta : ℤ) (hv : 0 < v)
    (hc : u.Coprime v) (f : ℤ → ℤ → ℂ) :
    (∑ m ∈ Icc (1:ℤ) L, ∑ k ∈ Icc (1:ℤ) L,
      if m*u-k*v=delta then f m k else 0) =
      ∑ j ∈ progressionIndices L u v delta,
        f (residue u v delta+(v:ℤ)*j)
          (((residue u v delta+(v:ℤ)*j)*u-delta)/v) := by
  classical
  simp_rw [PRZZAFEProgression.k_sum L u v _ delta (by exact_mod_cast hv.ne')]
  rw [← sum_filter]
  change (∑ m ∈ retained L u v delta, f m ((m*u-delta)/v)) = _
  unfold progressionIndices
  rw [sum_image]
  · apply sum_congr rfl
    intro m hm
    rw [reconstruct L u v delta m hv hc hm]
  · intro m hm n hn he
    have h := congrArg (fun j : ℤ => residue u v delta+(v:ℤ)*j) he
    simpa only [reconstruct L u v delta m hv hc hm,
      reconstruct L u v delta n hv hc hn] using h

/-- The literal Gamma or W kernel and both outer arithmetic coefficients
are substituted without dropping their denominators or conjugation. -/
theorem actual_weight (L u v n r : ℕ) (delta : ℤ) (hv : 0 < v)
    (hc : u.Coprime v) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (V : ℕ → ℝ → ℂ) (t : ℝ) :
    (∑ m ∈ Icc (1:ℤ) L, ∑ k ∈ Icc (1:ℤ) L,
      if m*u-k*v=delta then
        PRZZL1Finite.term a b alpha beta V t m.toNat k.toNat n r else 0) =
      ∑ j ∈ progressionIndices L u v delta,
        PRZZL1Finite.term a b alpha beta V t
          (residue u v delta+(v:ℤ)*j).toNat
          (((residue u v delta+(v:ℤ)*j)*u-delta)/v).toNat n r :=
  weighted_sum L u v delta hv hc _

#print axioms reconstruct
#print axioms progression_bounds
#print axioms weighted_sum
#print axioms actual_weight
end XiPrime8845.PRZZTruncatedProgression
