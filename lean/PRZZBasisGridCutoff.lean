import PRZZCentralGridIdentity
import PRZZProfileMellin

/-! Absorb the actual height-dependent seven basis profiles into smooth
arithmetic cutoffs at the finite arithmetic samples. No division by Mobius
coefficients is used. The right profile is conjugated before using its
real-valuedness; the two labels remain ordered. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset
namespace XiPrime8845.PRZZBasisGridCutoff
open PRZZMellinSeparation PRZZWitnessMass PRZZProfileScale
set_option maxHeartbeats 10000000

theorem raw_star (Y : ℝ) (i : Fin 7) (x : ℝ) : star (raw Y i x) = raw Y i x := by
  simp [raw]

theorem sample_factorization (theta T Q : ℝ) (i : Fin 7) (F : ℝ → ℂ)
    (N n : ℕ) (hn : n ∈ Icc 1 N) (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZWitnessBasis.basis theta T i n*scaledCutoff F Q n =
      (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ)*
        cutoffRaw F (PRZZ.length theta T) Q i n := by
  rw [basis_arithmetic_factorization,weight_on_support theta T i n
    (mem_Icc.mp hn).1 ((by exact_mod_cast (mem_Icc.mp hn).2 : (n:ℝ) ≤ N).trans hNY)]
  unfold cutoffRaw
  ring

theorem index_samples (N d : ℕ) (D H : ℝ) (z : PRZZAStar.Index)
    (hz : z ∈ PRZZAStar.indices N d D H) (hd : 0 < d) :
    d*z.1.1 ∈ Icc 1 N ∧ d*z.1.2 ∈ Icc 1 N := by
  have hh := mem_filter.mp (mem_product.mp hz).1
  have hu := (mem_Icc.mp (mem_product.mp hh.1).1).1
  have hv := (mem_Icc.mp (mem_product.mp hh.1).2).1
  exact ⟨mem_Icc.mpr ⟨by nlinarith,hh.2.2.1⟩,
    mem_Icc.mpr ⟨by nlinarith,hh.2.2.2⟩⟩

/-- Independent basis pair, positive literal cell, at its actual samples. -/
theorem positive_absorb (theta T Q V : ℝ) (i j : Fin 7) (N d J : ℕ)
    (D M : ℝ) (F G H Phi : ℝ → ℂ) (a b : ℂ)
    (hd : 0 < d) (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZClassPoisson.positiveCell N d J D T M
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)
      F (scaledCutoff G Q) (scaledCutoff H V) Phi a b =
    PRZZClassPoisson.positiveCell N d J D T M
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels j) n:ℂ))
      F (cutoffRaw G (PRZZ.length theta T) Q i)
      (cutoffRaw H (PRZZ.length theta T) V j) Phi a b := by
  rw [PRZZClassPoisson.positive_eq,PRZZClassPoisson.positive_eq]
  unfold PRZZMixedLiteral.literal
  apply sum_congr rfl
  intro z hz
  obtain ⟨hu,hv⟩ := index_samples N d D _ z hz hd
  simp only [PRZZAStar.prefactor,star_one,one_mul,cutoffRaw]
  rw [basis_arithmetic_factorization,basis_arithmetic_factorization,
    weight_on_support theta T i _ (mem_Icc.mp hu).1
      ((by exact_mod_cast (mem_Icc.mp hu).2 : ((d*z.1.1:ℕ):ℝ) ≤ N).trans hNY),
    weight_on_support theta T j _ (mem_Icc.mp hv).1
      ((by exact_mod_cast (mem_Icc.mp hv).2 : ((d*z.1.2:ℕ):ℝ) ≤ N).trans hNY)]
  simp only [star_mul,raw_star,Nat.cast_mul]
  ring

/-- The last arithmetic window may have Q>Y. Its scale is still at most
2Y, and the normalized logarithmic parameters remain in the unit box. -/
theorem parameters_doubled (Y Q : ℝ) (hY : 1 ≤ Real.log Y)
    (hQ : 1 ≤ Q) (hQY : Q ≤ 2*Y) :
    |parameterA Y Q| ≤ 1 ∧ |parameterB Y| ≤ 1 := by
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL : 0 < Real.log Y := by linarith
  have hq0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hq : Real.log Q ≤ Real.log 2+Real.log Y := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hY0.ne']
    exact Real.log_le_log hQ0 hQY
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  constructor
  · unfold parameterA
    rw [Real.log_div hY0.ne' hQ0.ne',abs_div,abs_of_pos hL]
    apply (div_le_one hL).mpr
    rw [abs_le]
    constructor <;> linarith
  · unfold parameterB
    rw [abs_div,abs_one,abs_of_pos hL]
    exact (div_le_one hL).mpr hY

/-- The profile presented to the grid before dilation. It is smooth;
the sharp n<=Y indicator remains solely in the finite arithmetic support. -/
def normalized (F : ℝ → ℂ) (Y Q : ℝ) (i : Fin 7) (x : ℝ) : ℂ :=
  (amplitude Y i:ℂ)*PRZZProfileSmooth.window F (profileDegree i)
    (parameterA Y Q) (parameterB Y) x

theorem normalized_scaled (F : ℝ → ℂ) (hs : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (Y Q : ℝ) (i : Fin 7) (hY : 0 < Y) (hQ : 0 < Q) :
    scaledCutoff (normalized F Y Q i) Q = cutoffRaw F Y Q i := by
  rw [cutoffRaw_eq F (1/2) 3 (by norm_num) hs Y Q i hY hQ]
  rfl

theorem normalized_support (F : ℝ → ℂ) (Y Q : ℝ) (i : Fin 7) :
    Function.support (normalized F Y Q i) ⊆ Function.support F := by
  intro x hx hf
  exact hx (by simp [normalized,PRZZProfileSmooth.window,hf])

/-- One jet sequence, before Y,Q,i and every dilation R, supplies both
arithmetic slots of the grid, including the final window Q<=2Y. -/
theorem normalized_members (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Set.Icc (1/2:ℝ) 3) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ ∀ (Y Q R : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ 2*Y → 0 < R →
      PRZZProfileMellin.Member (Real.log 6) jets
        (scaledCutoff (normalized F Y Q i) R) := by
  choose C hC h using fun (n : ℕ) (i : Fin 7) =>
    PRZZProfileSmooth.scaled_uniform F hF (1/2) 3 (by norm_num) hs (profileDegree i) n
  refine ⟨fun n => 3*∑ i, C n i,fun n => mul_nonneg (by norm_num) (sum_nonneg (fun i hi => hC n i)),?_⟩
  intro Y Q R i hY hQ hQY hR
  obtain ⟨ha,hb⟩ := parameters_doubled Y Q hY hQ hQY
  have hf := PRZZProfileSmooth.window_smooth F hF (1/2) 3 (by norm_num) hs
    (profileDegree i) (parameterA Y Q) (parameterB Y)
  have hscaled : ContDiff ℝ ∞ (scaledCutoff
      (PRZZProfileSmooth.window F (profileDegree i) (parameterA Y Q) (parameterB Y)) R) :=
    hf.comp (contDiff_const.mul contDiff_id)
  refine ⟨contDiff_const.mul hscaled,?_,?_⟩
  · refine ⟨R/2,3*R,by positivity,by linarith,?_,?_⟩
    · exact PRZZWindowScaleSupply.scaled_support _ R hR ((normalized_support F Y Q i).trans hs)
    · rw [show 3*R/(R/2)=6 by field_simp; ring]
  · intro n x
    have low : (n:WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
    change ‖(x:ℂ)^n*iteratedDeriv n
      (fun x => (amplitude Y i:ℂ)*scaledCutoff
        (PRZZProfileSmooth.window F (profileDegree i) (parameterA Y Q) (parameterB Y)) R x) x‖ ≤ _
    rw [iteratedDeriv_const_mul _ (hscaled.contDiffAt.of_le low)]
    have he : ∀ z : ℂ, (x:ℂ)^n*((amplitude Y i:ℂ)*z) =
      (amplitude Y i:ℂ)*((x:ℂ)^n*z) := by intro z; ring
    rw [he,norm_mul]
    exact (mul_le_mul (amplitude_bound Y i hY) (h n i _ _ R x ha hb)
      (norm_nonneg _) (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (single_le_sum (fun j hj => hC n j) (mem_univ i)) (by norm_num))

/-- Same absorption for the reflected negative cell: no coefficient swap. -/
theorem negative_absorb (theta T Q V : ℝ) (i j : Fin 7) (N d J : ℕ)
    (D M : ℝ) (F G H Phi : ℝ → ℂ) (a b : ℂ)
    (hd : 0 < d) (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZClassNegativePoisson.negativeCell N d J D T M
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)
      F (scaledCutoff G Q) (scaledCutoff H V) Phi a b =
    PRZZClassNegativePoisson.negativeCell N d J D T M
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels j) n:ℂ))
      F (cutoffRaw G (PRZZ.length theta T) Q i)
      (cutoffRaw H (PRZZ.length theta T) V j) Phi a b := by
  rw [PRZZClassNegativePoisson.negative_fold,PRZZClassNegativePoisson.negative_fold]
  unfold PRZZSignedCentral.signedLiteral
  apply sum_congr rfl
  intro z hz
  obtain ⟨hu,hv⟩ := index_samples N d D _ z hz hd
  simp only [PRZZFilteredResidual.signedPrefactor,PRZZUnfrozenPoisson.arithmetic,
    PRZZMixedLiteral.leftFold,PRZZMixedLiteral.rightFold,← Nat.cast_mul,
    Nat.floor_natCast,star_one,one_mul,cutoffRaw]
  rw [basis_arithmetic_factorization,basis_arithmetic_factorization,
    weight_on_support theta T i _ (mem_Icc.mp hu).1
      ((by exact_mod_cast (mem_Icc.mp hu).2 : ((d*z.1.1:ℕ):ℝ) ≤ N).trans hNY),
    weight_on_support theta T j _ (mem_Icc.mp hv).1
      ((by exact_mod_cast (mem_Icc.mp hv).2 : ((d*z.1.2:ℕ):ℝ) ≤ N).trans hNY)]
  simp only [star_mul,raw_star,Nat.cast_mul]
  ring

/-- All 49 ordered pairs enter the same signed central collector. This
holds for every row cutoff, not just bodyCut or a common integer J. -/
theorem central_absorb (theta T : ℝ) (i j : Fin 7) (G H F Phi : ℝ → ℂ)
    (hG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hH : Function.support H ⊆ Set.Icc (1/2:ℝ) 3)
    (K N : ℕ) (ss : Finset ℕ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ)
    (eps : ℝ) (a b : ℂ) (hY : 0 < PRZZ.length theta T)
    (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZCentralGridIdentity.central (fun _ => G) (fun _ => H) F Phi K N ss
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j) cut T eps a b =
    PRZZCentralGridIdentity.central
      (fun k => normalized G (PRZZ.length theta T) ((2:ℝ)^k) i)
      (fun k => normalized H (PRZZ.length theta T) ((2:ℝ)^k) j) F Phi K N ss
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels j) n:ℂ)) cut T eps a b := by
  unfold PRZZCentralGridIdentity.central
  apply sum_congr rfl; intro p hp
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  rw [normalized_scaled G hG _ _ i hY (by positivity),
    normalized_scaled H hH _ _ j hY (by positivity)]
  unfold PRZZCentralGridIdentity.cell
  rw [positive_absorb theta T _ _ i j N d _ _ _ F G H Phi a b
    (mem_Icc.mp hd).1 hNY,
    negative_absorb theta T _ _ i j N d _ _ _ F G H Phi a b
      (mem_Icc.mp hd).1 hNY]

theorem body_basis_grid (theta T : ℝ) (i j : Fin 7) (G H F Phi : ℝ → ℂ)
    (hG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hH : Function.support H ⊆ Set.Icc (1/2:ℝ) 3)
    (N : ℕ) (ss : Finset ℕ) (eps eH : ℝ) (A B : ℂ)
    (hY : 0 < PRZZ.length theta T) (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZCentralGridIdentity.central (fun _ => G) (fun _ => H) F Phi (Nat.log 2 N+2) N ss
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)
      (PRZZCentralGridIdentity.body T eH) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
    PRZZClassSignedGrid.grid
      (fun k => normalized G (PRZZ.length theta T) ((2:ℝ)^k) i)
      (fun k => normalized H (PRZZ.length theta T) ((2:ℝ)^k) j)
      F Phi (arithmeticLabels i) (arithmeticLabels j) N ss (fun _ _ _ => 1) T eps eH A B := by
  rw [central_absorb theta T i j G H F Phi hG hH _ N ss _ eps _ _ hY hNY,
    PRZZCentralGridIdentity.body_eq_grid]

/-- Absorption also preserves the displayed common-to-body transfer.
Its sign, masks and subunit row cutoffs are not changed by the profiles. -/
theorem transfer_absorb (theta T : ℝ) (i j : Fin 7) (G H F Phi : ℝ → ℂ)
    (hG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hH : Function.support H ⊆ Set.Icc (1/2:ℝ) 3)
    (K J N : ℕ) (ss : Finset ℕ) (eps eH : ℝ) (a b : ℂ)
    (hY : 0 < PRZZ.length theta T) (hNY : (N:ℝ) ≤ PRZZ.length theta T) :
    PRZZCentralGridIdentity.transfer (fun _ => G) (fun _ => H) F Phi K J N ss
      (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j) T eps eH a b =
    PRZZCentralGridIdentity.transfer
      (fun k => normalized G (PRZZ.length theta T) ((2:ℝ)^k) i)
      (fun k => normalized H (PRZZ.length theta T) ((2:ℝ)^k) j) F Phi K J N ss
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels i) n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient (arithmeticLabels j) n:ℂ)) T eps eH a b := by
  have hc := central_absorb theta T i j G H F Phi hG hH K N ss
    (fun _ _ _ => J) eps a b hY hNY
  have hb := central_absorb theta T i j G H F Phi hG hH K N ss
    (PRZZCentralGridIdentity.body T eH) eps a b hY hNY
  simpa only [PRZZCentralGridIdentity.transfer,PRZZCentralGridIdentity.central,
    sum_sub_distrib] using congrArg₂ (fun x y : ℂ => x-y) hc hb

#print axioms raw_star
#print axioms sample_factorization
#print axioms index_samples
#print axioms positive_absorb
#print axioms negative_absorb
#print axioms parameters_doubled
#print axioms normalized_scaled
#print axioms normalized_support
#print axioms normalized_members
#print axioms central_absorb
#print axioms body_basis_grid
#print axioms transfer_absorb
end XiPrime8845.PRZZBasisGridCutoff
