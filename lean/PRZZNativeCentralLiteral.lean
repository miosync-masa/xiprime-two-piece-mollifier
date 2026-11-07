import PRZZRetainedNative
import PRZZSignedCentral

/-! Actual finite-gap central cells versus the literal A* rectangle.
The discrepancy is the explicit sum of rejected rectangle rows, not an
assumed reconstruction error. Native Delta=-gap and the shift-slot swap
are both retained. Zero and negative modes remain separate. -/
noncomputable section
open scoped BigOperators FourierTransform ContDiff
open Complex Finset MeasureTheory
namespace XiPrime8845.PRZZNativeCentralLiteral
open PRZZCentralTail PRZZMellinSeparation
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def gapRectangle (B : ℝ) : Finset ℤ :=
  (Icc (-⌈B⌉) ⌈B⌉).filter (fun z => 0 < |(z:ℝ)| ∧ |(z:ℝ)| < B)

theorem gap_reindex (g : Finset ℤ) (B : ℝ) (f : ℤ → ℂ) :
    (∑ delta ∈ g, if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < B then f (-delta) else 0) =
      ∑ delta ∈ gapRectangle B, if -delta ∈ g then f delta else 0 := by
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun delta _ => -delta)
  · intro delta hd
    obtain ⟨hg,hh⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨(PRZZAStar.delta_cutoff_iff B (-delta)).mpr (by simpa using hh),by simpa using hg⟩
  · intro x hx y hy he; exact neg_injective he
  · intro delta hd
    obtain ⟨hg,hh⟩ := mem_filter.mp hd
    refine ⟨-delta,mem_filter.mpr ⟨hh,?_⟩,by simp⟩
    have hz := (PRZZAStar.delta_cutoff_iff B delta).mp hg
    simpa using hz
  · intro delta hd; rfl

def good (L N d : ℕ) (M : ℝ) (z : PRZZAStar.Index) : Prop :=
  -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) ∧
    |(z.2.1:ℝ)| ≤ M*z.1.1/4

def centralTerm (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index) (t : ℝ) : ℂ :=
  Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
    central F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) t J)

def cell (L J N d : ℕ) (D T M : ℝ) (F G H Phi : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, if PRZZDiagonalAssembly.admissible N d u v then
    ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
      if delta ≠ 0 ∧ |(delta:ℝ)| < D/d then
        Phi (t/T)*PRZZNativeComponents.row .central L J F G H M ((u,v),(-delta,1)) alpha beta a d t
      else 0 else 0

def rejected (L J N d : ℕ) (D T M : ℝ) (F G H Phi : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then 0 else
    centralTerm d J F G H Phi a T M alpha beta z t

theorem cell_rectangle (L J N d : ℕ) (D T M : ℝ) (F G H Phi : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    cell L J N d D T M F G H Phi a alpha beta t =
      ∑ z ∈ PRZZAStar.indices N d D 2, if good L N d M z then
        centralTerm d J F G H Phi a T M alpha beta z t else 0 := by
  have h2 : (Icc 1 ⌊(2:ℝ)⌋₊).filter (fun h : ℕ => (h:ℝ)<2) = {1} := by
    ext h
    rw [PRZZAStar.h_cutoff_iff,mem_singleton]
    constructor
    · intro hh
      have : h < 2 := by exact_mod_cast hh.2
      omega
    · intro hh; subst h; norm_num
  unfold PRZZAStar.indices cell
  rw [h2]
  simp only [Finset.product_eq_sprod,sum_product,sum_filter,sum_singleton]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    have he := gap_reindex (PRZZNativeFamily.gaps L N (d*u) (d*v)) (D/d)
      (fun delta => if |(delta:ℝ)| ≤ M*u/4 then centralTerm d J F G H Phi a T M alpha beta ((u,v),(delta,1)) t else 0)
    calc
      _ = ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d then
            (if |((-delta:ℤ):ℝ)| ≤ M*u/4 then
              centralTerm d J F G H Phi a T M alpha beta ((u,v),(-delta,1)) t else 0) else 0 := by
        apply sum_congr rfl; intro delta hd
        have hz : delta ≠ 0 ↔ 0 < |(delta:ℝ)| := by
          rw [abs_pos]; exact_mod_cast (Iff.rfl : delta ≠ 0 ↔ delta ≠ 0)
        simp only [PRZZNativeComponents.row,centralTerm]
        split_ifs <;> simp_all
      _ = _ := by
        rw [he]
        unfold gapRectangle good
        rw [sum_filter]
        apply sum_congr rfl; intro delta hd
        dsimp only
        split_ifs <;> simp_all
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had']

theorem cell_split (L J N d : ℕ) (D T M : ℝ) (F G H Phi : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) :
    cell L J N d D T M F G H Phi a alpha beta t =
      PRZZSignedCentral.centralRows N d J D T M a G H F Phi beta alpha (alpha+beta) t-
        rejected L J N d D T M F G H Phi a alpha beta t := by
  rw [cell_rectangle]
  unfold PRZZSignedCentral.centralRows rejected centralTerm
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro z hz
  by_cases hg : good L N d M z <;> simp [hg]

theorem term_integrable (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    Integrable (centralTerm d J F G H Phi a T M alpha beta z) := by
  have hm (h : ℤ) : Integrable (fun t : ℝ => Phi (t/T)*
      (PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        mode F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) t h)) := by
    simp_rw [PRZZFilteredResidual.normalized_mode]
    have hi := PRZZCentralFubini.spectrum_integrable F Phi hF hP (M/z.1.2)
      ((z.1.1:ℝ)*z.1.2) z.2.1 T h (alpha+beta+1) (alpha+beta)
      (by positivity) (by positivity) hT hs hsF hsP
    convert hi.const_mul (PRZZFilteredResidual.signedPrefactor a G H d alpha beta z h/
      ((z.1.1:ℂ)*(z.1.2:ℂ))) using 1
    funext t; simp only [PRZZFrozenTail.frozen]; ring
  have he (t : ℝ) : centralTerm d J F G H Phi a T M alpha beta z t =
      Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        mode F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) t 0)+
      ∑ j ∈ range J,
        (Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
          mode F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) t (j+1))+
         Phi (t/T)*(PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
          mode F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) t (-(j+1)))) := by
    simp only [centralTerm,central,PRZZFrozenTail.pair,mode,mul_add,mul_sum,
      Nat.cast_zero,zero_add,Int.cast_add,Int.cast_natCast,
      Int.cast_one,Int.cast_neg,neg_div,add_div]
  change Integrable (fun t => centralTerm d J F G H Phi a T M alpha beta z t)
  simp_rw [he]
  exact (hm 0).add (integrable_finsetSum _ (fun j hj => (hm (j+1)).add (hm (-(j+1)))))

/-- Literal A* with the genuine native filters charged to an explicit
rejected-row integral. The A* arguments are beta,alpha in this convention. -/
theorem cell_time_literal (L J N d : ℕ) (D T M : ℝ) (F G H Phi : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : alpha+beta ≠ 0) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    (∫ t : ℝ, cell L J N d D T M F G H Phi a alpha beta t) =
      PRZZSignedCentral.signedLiteral 0 N d D 2 T M a G H F Phi beta alpha (alpha+beta)+
      PRZZAStar.literal N d D ((J:ℝ)+1) T a G H (fun y => F (M⁻¹*y))
        (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
      PRZZSignedCentral.signedLiteral (-1) N d D ((J:ℝ)+1) T M a G H F Phi beta alpha (alpha+beta)-
      ∫ t : ℝ, rejected L J N d D T M F G H Phi a alpha beta t := by
  have hi (z : PRZZAStar.Index) (hz : z ∈ PRZZAStar.indices N d D 2) := by
    have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact term_integrable d J F G H Phi a T M alpha beta z hF hP hT hM
      (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs hsF hsP
  have hc : Integrable (fun t => PRZZSignedCentral.centralRows N d J D T M a G H F Phi beta alpha (alpha+beta) t) := by
    exact integrable_finsetSum _ (fun z hz => hi z hz)
  have hr : Integrable (rejected L J N d D T M F G H Phi a alpha beta) := by
    unfold rejected
    apply integrable_finsetSum; intro z hz
    by_cases hg : good L N d M z
    · simp only [if_pos hg]; exact integrable_zero ℝ ℂ volume
    · simpa only [if_neg hg] using hi z hz
  simp_rw [cell_split]
  rw [integral_sub hc hr,PRZZSignedCentral.central_time N d J D T M a G H F Phi beta alpha
    (alpha+beta) hF hP hT hM hs hsF hsP]

/-- The central component in kept_decomposition is exactly these cells,
with the original raw-gap cutoff divided by the actual gcd. -/
theorem retained_central_cells (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    Phi (t/T)*PRZZRetainedNative.selectedPart .central L J N P G H a
      (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N,
        cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t := by
  rw [PRZZRetainedNative.selected_reindex]
  simp only [mul_sum,cell]
  apply sum_congr rfl; intro s hss
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had,mul_sum]
    apply sum_congr rfl; intro delta hdelta
    have hg : Nat.gcd (d*u) (d*v) = d := by
      rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
    have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have he : (¬PRZZSourceMaskFamily.discarded T Q eps s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)) ↔
        |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
      simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le]
      rw [lt_div_iff₀ hd0]
      simp only [mul_comm]
    rw [he]
    split_ifs <;> simp
  · simp only [if_neg had,mul_zero]

theorem retained_central_time (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hleft : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T Q eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t : ℝ, Phi (t/T)*PRZZRetainedNative.selectedPart .central L J N P G H a
      (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t) =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N,
        (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          2 T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)+
         PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T a G H (fun y => PRZZWRowLimit.profile P (((2:ℝ)^s)⁻¹*y))
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
         PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)-
         ∫ t : ℝ, rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t) := by
  have hp := PRZZWRowLimit.profile_regular P hP hleft hright
  have hi (s d : ℕ) : Integrable (cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta) := by
    change Integrable (fun t => cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t)
    simp_rw [cell_rectangle]
    apply integrable_finsetSum; intro z hz
    by_cases hg : good L N d ((2:ℝ)^s) z
    · simp only [if_pos hg]
      have hz' := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
      exact term_integrable d J _ G H Phi a T _ alpha beta z hp.1.continuous hPhi hT
        (by positivity) (mem_Icc.mp hz'.1).1 (mem_Icc.mp hz'.2).1 hs hp.2.2 hsPhi
    · simp only [if_neg hg]; exact integrable_zero ℝ ℂ volume
  simp_rw [retained_central_cells]
  rw [integral_finsetSum _ (fun s hss => integrable_finsetSum _ (fun d hd => hi s d))]
  apply sum_congr rfl; intro s hss
  rw [integral_finsetSum _ (fun d hd => hi s d)]
  apply sum_congr rfl; intro d hd
  exact cell_time_literal L J N d _ T _ _ G H Phi a alpha beta hp.1.continuous hPhi hT
    (by positivity) hs hp.2.2 hsPhi

#print axioms gap_reindex
#print axioms cell_rectangle
#print axioms cell_split
#print axioms term_integrable
#print axioms cell_time_literal
#print axioms retained_central_cells
#print axioms retained_central_time
end XiPrime8845.PRZZNativeCentralLiteral
