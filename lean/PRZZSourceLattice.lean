import PRZZSharpPoisson

/-! The source integer variable is y=v*x. Transporting its residue lattice
therefore gives modulus one in x, not modulus v. Sharp boundary corrections
are retained explicitly. No Gamma-to-W replacement error is set to zero. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace XiPrime8845.PRZZSourceLattice
set_option maxHeartbeats 3000000

def source (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t y : ℝ) : ℂ :=
  PRZZFrozenTail.frozen F M z alpha beta sigma t (y/z.1.2)

theorem lattice (a v : ℝ) (hv : v ≠ 0) (j : ℤ) :
    (a+v*j)/v = a/v+(j:ℝ) := by field_simp

/-- The original source cutoff supplies the corrected lower-support bound
with no extra condition on v. -/
theorem source_delta (T M Q d u eps delta : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hd : 0 < d) (hu : 0 < u)
    (hQ : Q ≤ 2*d*u) (hheight : 8 ≤ T^(1-eps))
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d) :
    |delta| ≤ M*u/4 := by
  have hp : 0 < T^(1-eps) := by positivity
  have hh : |delta| * (T^(1-eps)*d) ≤ M*Q := by
    apply (le_div_iff₀ (mul_pos hp hd)).mp
    simpa [PRZZSourceCutoffs.deltaCutoff,div_div] using hdelta
  have hq := mul_le_mul_of_nonneg_left hQ hM.le
  have hs := mul_le_mul_of_nonneg_left hheight (mul_nonneg (abs_nonneg delta) hd.le)
  nlinarith

theorem source_support (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (t : ℝ) (hM : 0 < M) (hv : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    Function.support (source F M z alpha beta sigma t) ⊆ Icc (M/2) (3*M) := by
  intro y hy
  have hh := PRZZWeightFourier.support_subset (1/2) 3 (by norm_num) F
    (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
    ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma
    (by positivity) hsF hy
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  constructor
  · have hh' := (mul_le_mul_of_nonneg_right hh.1 hv0.le)
    field_simp at hh'
    nlinarith
  · have hh' := (mul_le_mul_of_nonneg_right hh.2 hv0.le)
    field_simp at hh'
    nlinarith

/-- Correct source lattice: no extra v in the lower support condition. -/
theorem sharp_source (L J : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hL : 3*M ≤ L) (hkL : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (L:ℝ)*z.1.2) :
    (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
      if m*z.1.1-k*z.1.2= -z.2.1 then source F M z alpha beta sigma t m else 0) =
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2)
        z alpha beta sigma t J +
      ∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
        z alpha beta sigma J j t := by
  have hlo : 0 < M/2*z.1.1-((-z.2.1:ℤ):ℝ) := by
    push_cast
    have hp : 0 < M*(z.1.1:ℝ) := by positivity
    nlinarith [neg_abs_le (z.2.1:ℝ)]
  have hhi : 3*M*z.1.1-((-z.2.1:ℤ):ℝ) ≤ (L:ℝ)*z.1.2 := by
    push_cast
    linarith [le_abs_self (z.2.1:ℝ)]
  rw [PRZZSharpPoisson.sharp_eq_progression L z.1.1 z.1.2 (-z.2.1)
    (source F M z alpha beta sigma t) (M/2) (3*M) hu hv hc
    (source_support F M z alpha beta sigma t hM hv hsF) (by positivity) hL hlo hhi]
  have he : (∑' j : ℤ, source F M z alpha beta sigma t
      ((PRZZTruncatedProgression.residue z.1.1 z.1.2 (-z.2.1):ℝ)+z.1.2*j)) =
      ∑' j : ℤ, PRZZFrozenTail.frozen F M z alpha beta sigma t
        (PRZZCentralTail.residue z/z.1.2+1*j) := by
    apply tsum_congr
    intro j
    unfold source
    rw [lattice _ _ (by exact_mod_cast hv.ne')]
    simp [PRZZCentralTail.residue,PRZZTruncatedProgression.residue]
  rw [he]
  exact PRZZCentralTail.poisson_split F hF hsF M 1
    (PRZZCentralTail.residue z/z.1.2) t z alpha beta sigma J hM (by norm_num) ht hu hv hs

/-- The omitted boundary is a finite, explicit set of pairs. It includes
both m>L and k>L, rather than silently discarding one cutoff. -/
theorem boundary_split (L B : ℕ) (hLB : L ≤ B) (f : ℤ × ℤ → ℂ) :
    (∑ m ∈ Finset.Icc (1:ℤ) B, ∑ k ∈ Finset.Icc (1:ℤ) B, f (m,k)) =
      (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L, f (m,k)) +
      ∑ p ∈ ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) \
        ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)), f p := by
  have hsub : ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)) ⊆
      ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) := by
    intro p hp
    simp only [Finset.mem_product,Finset.mem_Icc] at hp ⊢
    have hh : (L:ℤ) ≤ B := by exact_mod_cast hLB
    omega
  simpa only [Finset.sum_product,add_comm] using (Finset.sum_sdiff hsub (f := f)).symm

/-- All missing sharp pairs are accounted for before applying Poisson.
B covers the smooth support; L need not do so. -/
theorem source_boundary (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2) :
    (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
      if m*z.1.1-k*z.1.2= -z.2.1 then source F M z alpha beta sigma t m else 0) +
    (∑ p ∈ ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) \
        ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)),
      if p.1*z.1.1-p.2*z.1.2= -z.2.1 then source F M z alpha beta sigma t p.1 else 0) =
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2)
        z alpha beta sigma t J +
      ∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
        z alpha beta sigma J j t := by
  rw [← boundary_split L B hLB (fun p =>
    if p.1*z.1.1-p.2*z.1.2= -z.2.1 then source F M z alpha beta sigma t p.1 else 0)]
  exact sharp_source B J F hF hsF M t z alpha beta sigma hM ht hu hv hc hs hdelta hB hkB

/-- Every nonzero omitted pair lies at a large spatial scale. This is
uniform in L and in the larger containing box B, so growing families may
be pruned by scale before any coefficient-mass estimate is applied. -/
theorem boundary_scale (L B : ℕ) (p : ℤ × ℤ)
    (F : ℝ → ℂ) (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hp : p ∈ ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) \
        ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)))
    (hgap : p.1*z.1.1-p.2*z.1.2= -z.2.1)
    (hf : source F M z alpha beta sigma t p.1 ≠ 0) :
    (L:ℝ) < 3*M ∨ (L:ℝ)*z.1.2 < (13/4:ℝ)*M*z.1.1 := by
  have hm := (source_support F M z alpha beta sigma t hM hv hsF hf).2
  have hg : (p.1:ℝ)*z.1.1-(p.2:ℝ)*z.1.2 = -(z.2.1:ℝ) := by
    exact_mod_cast hgap
  have hlarge : (L:ℤ) < p.1 ∨ (L:ℤ) < p.2 := by
    simp only [Finset.mem_sdiff,Finset.mem_product,Finset.mem_Icc] at hp
    omega
  rcases hlarge with hmL | hkL
  · left
    have hh : (L:ℝ) < p.1 := by exact_mod_cast hmL
    exact hh.trans_le hm
  · right
    have hh : (L:ℝ) < p.2 := by exact_mod_cast hkL
    have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
    have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
    have hn := mul_lt_mul_of_pos_right hh hv0
    have hb := mul_le_mul_of_nonneg_right hm hu0.le
    nlinarith [le_abs_self (z.2.1:ℝ)]

#print axioms boundary_scale
#print axioms source_delta
#print axioms source_boundary
#print axioms lattice
#print axioms source_support
#print axioms sharp_source
#print axioms boundary_split
end XiPrime8845.PRZZSourceLattice
