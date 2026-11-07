import PRZZSharpPoisson
import PRZZExpandedCutoff

/-! One sharp-cutoff threshold for a fixed finite family, all positive
times, and all Fourier cutoffs. This does not remove an L-dependent family
of spatial scales, or identify the unreplaced Gamma AFE weight with W. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology
namespace XiPrime8845.PRZZFrozenFamilyCutoff
set_option maxHeartbeats 3000000

def sharp (L : ℕ) (F : ℝ → ℂ) (M t : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
    if m*z.1.1-k*z.1.2= -z.2.1 then
      PRZZFrozenTail.frozen F M z alpha beta sigma t m else 0

/-- The threshold precedes time and frequency cutoffs, and covers every
member of the fixed finite family simultaneously. -/
theorem family_stable {ι : Type*} (s : Finset ι) (F : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M : ι → ℝ) (z : ι → PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hs : sigma ≠ 0)
    (hrow : ∀ i ∈ s, 0 < M i ∧ 0 < (z i).1.1 ∧ 0 < (z i).1.2 ∧
      (z i).1.1.Coprime (z i).1.2 ∧
      |((z i).2.1:ℝ)| ≤ (M i/(z i).1.2)*(z i).1.1/4) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ t : ℝ, 0 < t → ∀ J : ι → ℕ, ∀ i ∈ s,
      sharp L F (M i) t (z i) alpha beta sigma =
        PRZZCentralTail.central F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma t (J i) +
        ∑' j, PRZZFrozenTail.pair F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma (J i) j t := by
  classical
  have he : ∀ i ∈ s, ∃ L0 : ℕ, ∀ L ≥ L0, ∀ t : ℝ, 0 < t → ∀ J : ℕ,
      sharp L F (M i) t (z i) alpha beta sigma =
        PRZZCentralTail.central F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma t J +
        ∑' j, PRZZFrozenTail.pair F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma J j t := by
    intro i hi
    obtain ⟨hM,hu,hv,hc,hd⟩ := hrow i hi
    exact PRZZSharpPoisson.sharp_frozen_stable F hF hsF (M i) (z i) alpha beta sigma
      hM hu hv hc hs hd
  choose bound hb using he
  let L0 := ∑ i ∈ s.attach, bound i.1 i.2
  refine ⟨L0,?_⟩
  intro L hL t ht J i hi
  have hle : bound i hi ≤ L0 := by
    exact Finset.single_le_sum (f := fun i : {i // i ∈ s} => bound i.1 i.2)
      (fun i _ => Nat.zero_le _) (Finset.mem_attach s ⟨i,hi⟩)
  exact hb i hi L (hle.trans hL) t ht (J i)

/-- Central block and intermediate band are subtracted exactly. The
remaining tail is independent of the original sharp cutoff L. -/
theorem remainder_stable {ι : Type*} (s : Finset ι) (F : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M : ι → ℝ) (z : ι → PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hs : sigma ≠ 0)
    (hrow : ∀ i ∈ s, 0 < M i ∧ 0 < (z i).1.1 ∧ 0 < (z i).1.2 ∧
      (z i).1.1.Coprime (z i).1.2 ∧
      |((z i).2.1:ℝ)| ≤ (M i/(z i).1.2)*(z i).1.1/4) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ t : ℝ, 0 < t → ∀ J G : ι → ℕ,
      (∀ i ∈ s, J i ≤ G i) → ∀ c : ι → ℂ,
      (∑ i ∈ s, c i*(sharp L F (M i) t (z i) alpha beta sigma -
        PRZZCentralTail.central F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma t (J i) -
        PRZZExpandedCutoff.band F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma t (J i) (G i))) =
      ∑ i ∈ s, c i*∑' j, PRZZFrozenTail.pair F (M i) (z i).1.2
        (PRZZCentralTail.residue (z i)) (z i) alpha beta sigma (G i) j t := by
  obtain ⟨L0,h⟩ := family_stable s F hF hsF M z alpha beta sigma hs hrow
  refine ⟨L0,?_⟩
  intro L hL t ht J G hJG c
  apply Finset.sum_congr rfl
  intro i hi
  rw [h L hL t ht G i hi,PRZZExpandedCutoff.central_extend F (M i) (z i).1.2
    (PRZZCentralTail.residue (z i)) (z i) alpha beta sigma t (J i) (G i) (hJG i hi)]
  ring

/-- A fixed finite family's weighted time integral is eventually constant.
No integrability or dominated-limit premise is needed for this exact equality. -/
theorem time_stable {ι : Type*} (s : Finset ι) (F : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M : ι → ℝ) (z : ι → PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hs : sigma ≠ 0)
    (hrow : ∀ i ∈ s, 0 < M i ∧ 0 < (z i).1.1 ∧ 0 < (z i).1.2 ∧
      (z i).1.1.Coprime (z i).1.2 ∧
      |((z i).2.1:ℝ)| ≤ (M i/(z i).1.2)*(z i).1.1/4)
    (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ) (c : ι → ℝ → ℂ) (J : ι → ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (∫ t in Icc T (2*T), w t * ∑ i ∈ s, c i t * sharp L F (M i) t (z i) alpha beta sigma) =
      ∫ t in Icc T (2*T), w t * ∑ i ∈ s, c i t *
        (PRZZCentralTail.central F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma t (J i) +
        ∑' j, PRZZFrozenTail.pair F (M i) (z i).1.2 (PRZZCentralTail.residue (z i))
          (z i) alpha beta sigma (J i) j t) := by
  obtain ⟨L0,h⟩ := family_stable s F hF hsF M z alpha beta sigma hs hrow
  filter_upwards [eventually_ge_atTop L0] with L hL
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h L hL t (hT.trans_le ht.1) J i hi]

/-- The source Delta cutoff alone is not the frozen support condition.
Here T=M=128, u=d=1, v=64, Q1=2, Delta=1, eD=0.
Even the strict source cutoff holds, while the sufficient frozen condition
fails. This does not assert failure of Poisson or of the source theorem. -/
theorem source_cutoff_not_sufficient :
    (1:ℝ) < PRZZSourceCutoffs.deltaCutoff 128 128 2 0 / 1 ∧
      ¬ ((1:ℝ) ≤ (128/64)*1/4) := by
  norm_num [PRZZSourceCutoffs.deltaCutoff]

#print axioms source_cutoff_not_sufficient
#print axioms family_stable
#print axioms remainder_stable
#print axioms time_stable
end XiPrime8845.PRZZFrozenFamilyCutoff
