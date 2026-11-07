import PRZZSourceLattice
import PRZZWArithmeticCutoff

/-! Decay of the phase-replaced source weight on its actual lattice.
The modulus in the rescaled variable is one. No equality between the
unreplaced AFE weight and this weight is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex Filter Topology
namespace XiPrime8845.PRZZSourceBoundaryDecay
open PRZZSourceLattice PRZZWArithmeticCutoff
set_option maxHeartbeats 3000000

def cap (CF T : ℝ) (z : PRZZAStar.Index) (a b sigma : ℂ) : ℝ :=
  CF * ‖Complex.exp ((a+b+1)*(Real.log (z.1.2:ℝ):ℂ))‖ *
    (decayConstant sigma*(T/Real.pi)^2) * (3/2:ℝ)^2

/-- One cutoff constant works at every dilated scale. -/
theorem cutoff_cap (F : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ x, ‖F x‖ ≤ CF := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1/2:ℝ) 3) hF.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x
  by_cases hf : F x = 0
  · simpa [hf] using le_max_right C 0
  · exact (hC x (hsF hf)).trans (le_max_left _ _)

/-- Source decay survives the reciprocal-phase replacement. The original
gap and support imply mk <= (3/2)(u/v)m^2. M does not enter the cap. -/
theorem source_pointwise (F : ℝ → ℂ) (CF M T t : ℝ) (z : PRZZAStar.Index)
    (a b sigma : ℂ) (m k : ℕ) (hCF : 0 ≤ CF) (hF : ‖F (M⁻¹*(m:ℝ))‖ ≤ CF)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : sigma ≠ 0)
    (hab : 0 ≤ (a+b+1).re)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hgap : (m:ℤ)*z.1.1-(k:ℤ)*z.1.2= -z.2.1) :
    ‖source F M z a b sigma t m‖ ≤
      cap CF T z a b sigma * ((m:ℝ)^(-2:ℝ)*(k:ℝ)^(-2:ℝ)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  by_cases hf : source F M z a b sigma t m = 0
  · rw [hf,norm_zero]; unfold cap decayConstant; positivity
  have hsupport := source_support F M z a b sigma t hM hv hsF hf
  have hg : (m:ℝ)*z.1.1-(k:ℝ)*z.1.2= -(z.2.1:ℝ) := by exact_mod_cast hgap
  have hkm : (k:ℝ)*z.1.2 ≤ (3/2:ℝ)*(m:ℝ)*z.1.1 := by
    nlinarith [mul_le_mul_of_nonneg_right hsupport.1 hu0.le,le_abs_self (z.2.1:ℝ)]
  let X : ℝ := (z.1.1:ℝ)/z.1.2*(m:ℝ)^2
  have hX : 0 < X := by dsimp [X]; positivity
  have hprod : (m:ℝ)*k ≤ (3/2:ℝ)*X := by
    have hh := mul_le_mul_of_nonneg_left hkm hm0.le
    have heq : (3/2:ℝ)*X = ((3/2:ℝ)*(m:ℝ)^2*z.1.1)/z.1.2 := by dsimp [X]; ring
    rw [heq]
    apply (le_div_iff₀ hv0).mpr
    nlinarith
  have hker := kernel_bound sigma hs T t X hT ht hX
  have ht0 : 0 < t := hT.trans_le ht.1
  have he : (2*Real.pi*z.1.1/(t*z.1.2))*(m:ℝ)^2 = X/(t/(2*Real.pi)) := by
    dsimp [X]; field_simp
  have hp : ‖Complex.exp (-(a+b+1)*(Real.log (m:ℝ):ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hab)
      (Real.log_nonneg (by exact_mod_cast hm))
  have hphase : ‖Complex.exp (I*(((z.2.1:ℝ)*t/z.1.1/(m:ℝ):ℝ):ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  rw [source,PRZZFrozenTail.frozen_dilation F M z a b sigma t m hv hm0,
    PRZZFullWeightSmooth.weight,norm_mul,norm_mul,norm_mul,norm_mul,hphase,mul_one,he]
  have h1 := mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul hF hp (norm_nonneg _) hCF) hker
      (norm_nonneg _) (by positivity))
    (norm_nonneg (Complex.exp ((a+b+1)*(Real.log (z.1.2:ℝ):ℂ))))
  simp only [mul_one] at h1
  apply h1.trans
  rw [Real.rpow_neg hm0.le,Real.rpow_neg hk0.le,Real.rpow_two,Real.rpow_two]
  have hsq : ((m:ℝ)*k)^2 ≤ ((3/2:ℝ)*X)^2 := by gcongr
  have hi : 1/X^2 ≤ (3/2:ℝ)^2/((m:ℝ)^2*(k:ℝ)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ CF*‖Complex.exp ((a+b+1)*(Real.log (z.1.2:ℝ):ℂ))‖*
      (decayConstant sigma*(T/Real.pi)^2) by unfold decayConstant; positivity)
  convert hh using 1 <;> simp only [cap,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem source_bound (F : ℝ → ℂ) (CF M T t : ℝ) (z : PRZZAStar.Index)
    (a b sigma : ℂ) (hCF : 0 ≤ CF) (hF : ∀ x, ‖F x‖ ≤ CF)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : sigma ≠ 0)
    (hab : 0 ≤ (a+b+1).re)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hgap : (m:ℤ)*z.1.1-(k:ℤ)*z.1.2= -z.2.1) :
    ‖source F M z a b sigma t m‖ ≤
      cap CF T z a b sigma * ((m:ℝ)^(-2:ℝ)*(k:ℝ)^(-2:ℝ)) :=
  source_pointwise F CF M T t z a b sigma m k hCF (hF _) hsF hM hT ht
    hu hv hs hab hdelta hm hk hgap

def majorant (p : ℕ × ℕ) : ℝ :=
  (((p.1:ℝ)+1)^(-2:ℝ))*(((p.2:ℝ)+1)^(-2:ℝ))

theorem majorant_summable : Summable majorant := by
  have hn : Summable (fun n : ℕ => ((n:ℝ)+1)^(-2:ℝ)) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (by norm_num : (-2:ℝ) < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  exact hn.mul_of_nonneg hn (by intro n; positivity) (by intro n; positivity)

def tail (L : ℕ) : ℝ := (∑' p, majorant p) -
  ∑ p ∈ Finset.range L ×ˢ Finset.range L, majorant p

theorem tail_nonneg (L : ℕ) : 0 ≤ tail L := by
  apply sub_nonneg.mpr
  exact majorant_summable.sum_le_tsum _ (fun p _ => by unfold majorant; positivity)

theorem tail_zero : Tendsto tail atTop (𝓝 0) := by
  have hh := majorant_summable.hasSum.comp PRZZL1Truncation.rectangles_tendsto
  change Tendsto (fun L => (∑' p, majorant p) -
    ∑ p ∈ Finset.range L ×ˢ Finset.range L, majorant p) atTop (𝓝 0)
  simpa only [Function.comp_def,sub_self] using
    (tendsto_const_nhds (x := (∑' p, majorant p))).sub hh

/-- A common tail controls every larger containing box, even if B grows
with L. Both sharp cutoffs are retained. -/
theorem boundary_bound (L B : ℕ) (hLB : L ≤ B) (f : ℕ × ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ p, ‖f p‖ ≤ C*majorant p) :
    ‖∑ p ∈ (Finset.range B ×ˢ Finset.range B) \
      (Finset.range L ×ˢ Finset.range L), f p‖ ≤ C*tail L := by
  have hsub : Finset.range L ×ˢ Finset.range L ⊆ Finset.range B ×ˢ Finset.range B := by
    exact Finset.product_subset_product (Finset.range_mono hLB) (Finset.range_mono hLB)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p _ => hf p)).trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  have he := Finset.sum_sdiff hsub (f := majorant)
  have hh := majorant_summable.sum_le_tsum (Finset.range B ×ˢ Finset.range B)
    (fun p _ => by unfold majorant; positivity)
  unfold tail
  linarith

def row (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index) (a b sigma : ℂ)
    (t : ℝ) (p : ℕ × ℕ) : ℂ :=
  if ((p.1+1:ℕ):ℤ)*z.1.1-((p.2+1:ℕ):ℤ)*z.1.2= -z.2.1 then
    source F M z a b sigma t (p.1+1) else 0

theorem row_bound (F : ℝ → ℂ) (CF M T t : ℝ) (z : PRZZAStar.Index)
    (a b sigma : ℂ) (hCF : 0 ≤ CF) (hF : ∀ x, ‖F x‖ ≤ CF)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : sigma ≠ 0)
    (hab : 0 ≤ (a+b+1).re) (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4) (p : ℕ × ℕ) :
    ‖row F M z a b sigma t p‖ ≤ cap CF T z a b sigma*majorant p := by
  unfold row
  split_ifs with hg
  · simpa only [majorant,Nat.cast_add,Nat.cast_one] using
      source_bound F CF M T t z a b sigma hCF hF hsF hM hT ht hu hv hs hab hdelta
        (p.1+1) (p.2+1) (by omega) (by omega) hg
  · simp only [norm_zero]; unfold cap majorant decayConstant; positivity

/-- Actual source rows, with both omitted cutoffs and all coefficient
weights. The scale family may grow; its displayed coefficient mass must
be bounded before deducing a uniform-in-family limit. -/
theorem family_boundary {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (M : ι → ℝ) (z : ι → PRZZAStar.Index) (F : ℝ → ℂ)
    (CF T t : ℝ) (a b sigma : ℂ) (hCF : 0 ≤ CF) (hF : ∀ x, ‖F x‖ ≤ CF)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : ∀ i ∈ s, 0 < M i) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : ∀ i ∈ s, 0 < (z i).1.1) (hv : ∀ i ∈ s, 0 < (z i).1.2)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (hdelta : ∀ i ∈ s, |((z i).2.1:ℝ)| ≤ M i*(z i).1.1/4)
    (L B : ℕ) (hLB : L ≤ B) :
    ‖∑ i ∈ s, c i * ∑ p ∈ (Finset.range B ×ˢ Finset.range B) \
      (Finset.range L ×ˢ Finset.range L), row F (M i) (z i) a b sigma t p‖ ≤
      (∑ i ∈ s, ‖c i‖*cap CF T (z i) a b sigma)*tail L := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply boundary_bound L B hLB _ _ (by unfold cap decayConstant; positivity)
  intro p
  exact row_bound F CF (M i) T t (z i) a b sigma hCF hF hsF (hM i hi) hT ht
    (hu i hi) (hv i hi) hs hab (hdelta i hi) p

/-- Growing outer families are allowed once their displayed weighted cap
is uniformly bounded; no conclusion is drawn from rowwise decay alone. -/
theorem boundary_tendsto (f : ℕ → ℕ × ℕ → ℂ) (B : ℕ → ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hLB : ∀ L, L ≤ B L)
    (hf : ∀ L p, ‖f L p‖ ≤ C*majorant p) :
    Tendsto (fun L => ∑ p ∈ (Finset.range (B L) ×ˢ Finset.range (B L)) \
      (Finset.range L ×ˢ Finset.range L), f L p) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun L => boundary_bound L (B L) (hLB L) (f L) C hC (hf L))
  simpa using (tendsto_const_nhds (x := C)).mul tail_zero

/-- Exact conversion to the integer positive square used by source_boundary. -/
theorem positive_square (L : ℕ) (f : ℤ × ℤ → ℂ) :
    (∑ p ∈ Finset.range L ×ˢ Finset.range L,
      f (((p.1+1:ℕ):ℤ),((p.2+1:ℕ):ℤ))) =
    ∑ p ∈ Finset.Icc (1:ℤ) L ×ˢ Finset.Icc (1:ℤ) L, f p := by
  apply Finset.sum_bij (fun p _ => (((p.1+1:ℕ):ℤ),((p.2+1:ℕ):ℤ)))
  · intro p hp
    simp only [Finset.mem_product,Finset.mem_range,Finset.mem_Icc] at hp ⊢
    push_cast
    omega
  · intro p hp q hq he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at * <;> omega
  · intro p hp
    simp only [Finset.mem_product,Finset.mem_Icc] at hp
    refine ⟨(p.1.toNat-1,p.2.toNat-1),?_,?_⟩
    · simp only [Finset.mem_product,Finset.mem_range]; omega
    · apply Prod.ext <;> dsimp <;> omega
  · intro p hp; rfl

theorem boundary_integer (L B : ℕ) (hLB : L ≤ B) (f : ℤ × ℤ → ℂ) :
    (∑ p ∈ (Finset.range B ×ˢ Finset.range B) \
      (Finset.range L ×ˢ Finset.range L), f (((p.1+1:ℕ):ℤ),((p.2+1:ℕ):ℤ))) =
    ∑ p ∈ (Finset.Icc (1:ℤ) B ×ˢ Finset.Icc (1:ℤ) B) \
      (Finset.Icc (1:ℤ) L ×ˢ Finset.Icc (1:ℤ) L), f p := by
  have hn := Finset.sum_sdiff
    (Finset.product_subset_product (Finset.range_mono hLB) (Finset.range_mono hLB))
    (f := fun p : ℕ × ℕ => f (((p.1+1:ℕ):ℤ),((p.2+1:ℕ):ℤ)))
  rw [positive_square,positive_square] at hn
  have hi := PRZZSourceLattice.boundary_split L B hLB f
  simp only [← Finset.sum_product] at hi
  linear_combination hn + hi

/-- The actual q=1 Poisson central-plus-tail representation differs from
the sharp arithmetic square by a vanishing, explicitly bounded boundary. -/
theorem poisson_boundary (L B J : ℕ) (hLB : L ≤ B)
    (F : ℝ → ℂ) (hFs : ContDiff ℝ ∞ F) (CF M T t : ℝ) (z : PRZZAStar.Index)
    (a b sigma : ℂ) (hCF : 0 ≤ CF) (hF : ∀ x, ‖F x‖ ≤ CF)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hc : z.1.1.Coprime z.1.2)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4)
    (hB : 3*M ≤ B) (hkB : 3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2) :
    ‖PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2)
        z a b sigma t J +
      (∑' j, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2)
        z a b sigma J j t) -
      (∑ p ∈ Finset.range L ×ˢ Finset.range L, row F M z a b sigma t p)‖ ≤
      cap CF T z a b sigma * tail L := by
  let f : ℤ × ℤ → ℂ := fun p =>
    if p.1*z.1.1-p.2*z.1.2= -z.2.1 then source F M z a b sigma t p.1 else 0
  have he := source_boundary L B J hLB F hFs hsF M t z a b sigma hM
    (hT.trans_le ht.1) hu hv hc hs hdelta hB hkB
  have hsmall := positive_square L f
  have hbd := boundary_integer L B hLB f
  have hr : (fun p : ℕ × ℕ => f (((p.1+1:ℕ):ℤ),((p.2+1:ℕ):ℤ))) =
      row F M z a b sigma t := by
    funext p
    simp [f,row]
  rw [hr] at hsmall hbd
  simp only [Finset.sum_product] at hsmall
  change _ + (∑ p ∈ (Finset.Icc (1:ℤ) B ×ˢ Finset.Icc (1:ℤ) B) \
    (Finset.Icc (1:ℤ) L ×ˢ Finset.Icc (1:ℤ) L), f p) = _ at he
  rw [← hsmall,← hbd] at he
  rw [← he]
  simp only [Finset.sum_product,add_sub_cancel_left]
  exact boundary_bound L B hLB _ _ (by unfold cap decayConstant; positivity)
    (row_bound F CF M T t z a b sigma hCF hF hsF hM hT ht hu hv hs hab hdelta)

#print axioms poisson_boundary
#print axioms cutoff_cap
#print axioms positive_square
#print axioms boundary_integer
#print axioms boundary_tendsto
#print axioms row_bound
#print axioms family_boundary
#print axioms majorant_summable
#print axioms tail_nonneg
#print axioms tail_zero
#print axioms boundary_bound
#print axioms source_bound
#print axioms source_pointwise
end XiPrime8845.PRZZSourceBoundaryDecay
