import PRZZZeroArithmeticPartition
import PRZZZeroBoundarySum

/-! Exact spatial discrepancy of the completed native row. Integrals
are exchanged only after absolute gap summability has been supplied. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Finset
namespace XiPrime8845.PRZZZeroBoundaryIdentity
open PRZZZeroCompleteCell PRZZZeroBoundarySum
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem row_difference (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (L : ℕ) (T u v delta : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hu : 0 < u) (hv : 0 < v)
    (hd : delta ≠ 0) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    row P Phi L T u v sigma delta =
      (∫ x in Set.Ioi (0:ℝ), PRZZZeroGap.core Phi T (u*v) sigma delta x)-
        ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
          PRZZZeroOmittedGaps.value (PRZZWRowLimit.profile (fun y => (P y:ℂ)))
            Phi ((2:ℝ)^s) T u v delta sigma := by
  have hPc : Continuous P := by
    simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hP.continuous
  have hcore := (PRZZZeroSpatialLimit.spatial_limit P hPc hm hlo hhi hl hr
    Phi hPhi hcPhi hsPhi T (u*v) sigma delta hT (mul_pos hu hv) hs hn hd).1
  obtain ⟨hf,hc,hsp⟩ := PRZZWRowLimit.profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hr y hy])
  have hi (s : ℕ) : IntegrableOn (PRZZZeroGapExchange.row
      (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Phi ((2:ℝ)^s/v) T (u*v) sigma delta)
      (Set.Ioi (0:ℝ)) :=
    (PRZZZeroGapExchange.row_integrable _ Phi hf.continuous hPhi.continuous hsp hsPhi
      _ T (u*v) sigma delta (by positivity) hT (mul_pos hu hv) hs).integrableOn
  simp only [PRZZZeroOmittedGaps.value,PRZZZeroGap.kernel_time]
  change _ = (∫ x in Set.Ioi (0:ℝ), PRZZZeroGap.core Phi T (u*v) sigma delta x)-
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
      ∫ x in Set.Ioi (0:ℝ), PRZZZeroGapExchange.row
        (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Phi ((2:ℝ)^s/v) T (u*v) sigma delta x
  rw [← integral_finsetSum _ (fun s _ => hi s),← integral_sub hcore
    (integrable_finsetSum _ (fun s _ => hi s))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  simp only [PRZZZeroGapExchange.row,← Finset.sum_mul]
  ring

theorem pair_difference (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (L : ℕ) (T u v : ℝ) (sigma : ℂ) (n : ℕ)
    (hT : 0 < T) (hu : 0 < u) (hv : 0 < v) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    PRZZZeroBoundarySum.pair P Phi L T u v sigma n =
      (∫ x in Set.Ioi (0:ℝ), PRZZZeroCutoffLimit.corePair Phi T (u*v) sigma n x)-
        ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
          paired (PRZZWRowLimit.profile (fun y => (P y:ℂ))) Phi ((2:ℝ)^s) T u v sigma n := by
  have hPc : Continuous P := by
    simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hP.continuous
  have hi (delta : ℝ) (hd : delta ≠ 0) :=
    (PRZZZeroSpatialLimit.spatial_limit P hPc hm hlo hhi hl hr
      Phi hPhi hcPhi hsPhi T (u*v) sigma delta hT (mul_pos hu hv) hs hn hd).1
  unfold PRZZZeroBoundarySum.pair
  rw [row_difference P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi L T u v _ sigma
    hT hu hv (by positivity) hs hn,
    row_difference P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi L T u v _ sigma
    hT hu hv (neg_ne_zero.mpr (by positivity)) hs hn]
  rw [show (∫ x in Set.Ioi (0:ℝ), PRZZZeroCutoffLimit.corePair Phi T (u*v) sigma n x) =
    (∫ x in Set.Ioi (0:ℝ), PRZZZeroGap.core Phi T (u*v) sigma ((n+1:ℕ):ℝ) x)+
    (∫ x in Set.Ioi (0:ℝ), PRZZZeroGap.core Phi T (u*v) sigma (-((n+1:ℕ):ℝ)) x) from
      integral_add (hi _ (by positivity)) (hi _ (neg_ne_zero.mpr (by positivity)))]
  simp only [paired,Finset.sum_add_distrib]
  ring

theorem core_total (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T p : ℝ) (sigma : ℂ) (hT : 0 < T) (hp : 0 < p)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∑' n : ℕ, ∫ x in Set.Ioi (0:ℝ), PRZZZeroCutoffLimit.corePair Phi T p sigma n x) =
      ∫ x in Set.Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T p sigma x := by
  rw [integral_tsum_of_summable_integral_norm
    (fun n => PRZZZeroOuterMellin.pair_integrable Phi hPhi hcPhi hsPhi T p sigma n hT hp hs hn)
    (PRZZZeroOuterMellin.pair_mass_summable Phi hPhi hcPhi hsPhi T p sigma hT hp hs hn)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact PRZZZeroCosine.core_series_cosine Phi hPhi hsPhi T p x sigma hT hp hx hs

theorem series_difference (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (L : ℕ) (T u v : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hu : 0 < u) (hv : 0 < v) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∑' n : ℕ, PRZZZeroBoundarySum.pair P Phi L T u v sigma n) =
      (∫ x in Set.Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T (u*v) sigma x)-
        ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
          ∑' n : ℕ, paired (PRZZWRowLimit.profile (fun y => (P y:ℂ)))
            Phi ((2:ℝ)^s) T u v sigma n := by
  obtain ⟨hf,hc,hsp⟩ := PRZZWRowLimit.profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hr y hy])
  have hcap := PRZZZeroNativeTail.profile_cap P hm hlo hhi hl
  have hlocal (s : ℕ) := paired_summable _ Phi hf.continuous hPhi hcPhi hsp hsPhi
    (fun y hy => hcap y) ((2:ℝ)^s) T u v sigma (by positivity) hT hu hv hs hn
  have hraw : Summable (fun n : ℕ => ∫ x in Set.Ioi (0:ℝ),
      PRZZZeroCutoffLimit.corePair Phi T (u*v) sigma n x) :=
    (PRZZZeroOuterMellin.pair_mass_summable Phi hPhi hcPhi hsPhi T (u*v) sigma hT
      (mul_pos hu hv) hs hn).of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  simp_rw [pair_difference P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi L T u v sigma
    _ hT hu hv hs hn]
  rw [hraw.tsum_sub (summable_sum (fun s _ => hlocal s)),
    Summable.tsum_finsetSum (fun s _ => hlocal s),
    core_total Phi hPhi hcPhi hsPhi T (u*v) sigma hT (mul_pos hu hv) hs hn]

theorem model_primitive (P Phi : ℝ → ℂ) (L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0) :
    PRZZZeroNativeCompletion.completePart P Phi (Nat.log 2 N+2) L N a T eps alpha beta =
      ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          PRZZDiagonalAssembly.coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v*
            ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
              ∑' n : ℕ, paired (PRZZWRowLimit.profile P) Phi ((2:ℝ)^s) T u v (alpha+beta) n
        else 0 := by
  rw [PRZZZeroArithmeticPartition.model_cover P Phi L N a T eps alpha beta hl hr]
  unfold complete
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had,← mul_sum]
  · simp [had]

theorem total_difference (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (L N : ℕ) (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    total P Phi L N a T alpha beta =
      PRZZZeroOuterMellin.arithmeticZero N a (fun _ => 1) (fun _ => 1) Phi alpha beta T-
        PRZZZeroNativeCompletion.completePart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2)
          L N a T eps alpha beta := by
  rw [model_primitive _ Phi L N a T eps alpha beta
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hr y hy])]
  unfold total PRZZZeroOuterMellin.arithmeticZero
  simp only [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    rw [series_difference P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi L T u v
      (alpha+beta) hT (by exact_mod_cast (mem_Icc.mp hu).1)
      (by exact_mod_cast (mem_Icc.mp hv).1) hs hn]
    ring
  · simp [had]

/-- Both actual time integrals, including the Gamma multiplier, are the
unrestricted arithmetic zero series. -/
theorem zero_pair (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (alpha beta : ℂ)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
      PRZZZeroOuterMellin.arithmeticZero N a (fun _ => 1) (fun _ => 1) Phi alpha beta T)
        Phi T alpha beta = PRZZZeroCoupled.zeroPair N a alpha beta T
          (PRZZMellinSeparation.scaledCutoff Phi T) := by
  have h1 := PRZZZeroExhaustionCross.actual_zero_time N a Phi alpha beta T hPhi hcPhi hsPhi hT hs hn
  have h2 := PRZZZeroDualExhaustion.actual_dual_zero_time N a Phi alpha beta ha hb T
    hPhi hcPhi hsPhi hT hs hn
  unfold PRZZCentralMainAssembly.branchPair PRZZZeroCoupled.zeroPair
  dsimp only
  change _ + PRZZZeroOuterMellin.arithmeticZero N a (fun _ => 1) (fun _ => 1)
    (PRZZZeroDualExhaustion.dualCutoff Phi alpha beta T) (-beta) (-alpha) T = _
  rw [h1,h2]
  congr 1 <;> apply integral_congr_ae <;> apply Filter.Eventually.of_forall <;>
    intro t <;> simp only [PRZZMellinSeparation.scaledCutoff,inv_mul_eq_div]

/-- Exact total native mismatch after arithmetic partition removal.
Every boundary and omitted-gap term has the original d,u,v coefficients;
the second branch retains the genuine time-dependent Gamma multiplier. -/
theorem mismatch_boundary_gaps (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (N : ℕ) (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    PRZZCentralMainAssembly.zeroMismatch (fun y => (P y:ℂ)) (fun y => (P y:ℂ))
      Phi (Nat.log 2 N+2) N a T eps alpha beta =
      -PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
        total P Phi (PRZZLiteralExhaustion.spatialLength T) N a T alpha beta+
          PRZZZeroNativeCompletion.gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2)
            (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta := by
  obtain ⟨hf,hc,hsp⟩ := PRZZZeroDualExhaustion.cutoff_regular Phi hPhi hcPhi hsPhi alpha beta ha hb T
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  have h1 := total_difference P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi
    (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta hT hs hn
  have h2 := total_difference P hP hm hlo hhi hl hr
    (PRZZKeptLiteral.dualProfile Phi T alpha beta) hf hc hsp
    (PRZZLiteralExhaustion.spatialLength T) N a T eps (-beta) (-alpha) hT hs' hn'
  rw [PRZZZeroNativeCompletion.mismatch_eq P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi
    (Nat.log 2 N+2) N a T eps alpha beta hT ha hb hs hn]
  unfold PRZZZeroNativeCompletion.spatialMismatch
  rw [← zero_pair Phi hPhi hcPhi hsPhi N a T alpha beta hT ha hb hs hn]
  unfold PRZZCentralMainAssembly.branchPair
  dsimp only at h1 h2 ⊢
  rw [h1,h2]
  ring

/-- The primal spatial boundaries and omitted native gaps together have
arbitrary polynomial decay, including the full outer coefficient mass.
This does not apply fixed-Phi constants to a height-varying dual profile. -/
theorem primal_error_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S theta rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^theta → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖total P Phi (PRZZLiteralExhaustion.spatialLength T) N
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))+
        PRZZZeroNativeCompletion.gapPart (fun y => (P y:ℂ)) Phi (Nat.log 2 N+2)
          (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  have hPc : Continuous P := by
    simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hP.continuous
  obtain ⟨C,hC,hb⟩ := actual_total_power P hPc hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js r S theta rate hr hS htheta hrate
  obtain ⟨D,hD,hg⟩ := PRZZZeroNativeCompletion.model_gap_eventually P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eps r S rate heps hr hS
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hg,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    Filter.eventually_ge_atTop (4:ℝ)] with T hg hsmall hT
  intro N A B hN hNtheta hNT hA hB hsep
  have hlog : 0 < Real.log T := by linarith [hsmall.1]
  have hz (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hlog]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hlog.le
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  have h1 := hb _ N T A B le_rfl hT hN hNtheta hNT hsep hn (hz A hA) (hz B hB)
  have h2 := hg (PRZZLiteralExhaustion.spatialLength T) N A B hN hNT hA hB hsep
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

#print axioms primal_error_power
#print axioms zero_pair
#print axioms mismatch_boundary_gaps
#print axioms model_primitive
#print axioms total_difference
#print axioms core_total
#print axioms series_difference
#print axioms row_difference
#print axioms pair_difference
end XiPrime8845.PRZZZeroBoundaryIdentity
