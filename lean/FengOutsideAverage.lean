import CoprimeEulerError
import FengPrimeWindow
import FengOutsidePrime
import FengOutsideBounds

/-! Actual inner-to-proxy replacement in the outside block. A moving endpoint
is paid by a short interval of the full prime-power measure; the interior is
averaged in g before estimating. All cutoffs and all prime powers are retained. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengOutsideAverage
open CoprimeEulerError CoprimeApproximation CoprimeEulerCompletion
open SupportTail FengPrimeExclusion FengPrimeWindow CoprimeEndpoint
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def rowBudget (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ) : ℝ :=
  ∑ r ∈ Icc 1 (cutoff L u), (mass r/L^2)*innerError L g (u-Real.log r/L) θ G A

theorem rowBudget_nonneg (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ) :
    0 ≤ rowBudget L u θ g G A := by
  apply sum_nonneg
  intro r hr
  exact mul_nonneg (div_nonneg (mass_nonneg r) (sq_nonneg L)) (norm_nonneg _)

theorem translated_mem (L u U : ℝ) (hL : 0 < L) (hu : u ∈ Set.Icc 0 U)
    (r : ℕ) (hr : r ∈ Icc 1 (cutoff L u)) : u-Real.log r/L ∈ Set.Icc 0 U := by
  have hr1 : (1:ℝ)≤r := by exact_mod_cast (mem_Icc.mp hr).1
  have hx := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2
  have ht := ShiftWeights.normalized_log_mem r L u hr1 hL
    ((Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hr1)).mpr hx)
  exact ⟨by linarith [ht.2],by linarith [ht.1,hu.2]⟩

theorem block_error_bound (L u θ C U : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ)
    (hL : 0 < L) (hu : u ∈ Set.Icc 0 U) (hA : ‖A‖ ≤ C) :
    ‖FengAtG.outsideBlock (cutoff L u) g L u θ G A-
      FengOutside.mainProxy (cutoff L u) g L u θ G A‖ ≤
      Real.exp (C*U)*rowBudget L u θ g G A := by
  have hh := FengOutside.outsideBlock_main_error (cutoff L u) g L u θ G A
  rw [abs_of_pos hL] at hh
  apply hh.trans
  have hs : (∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r => r.Coprime g),
      ‖FengAtG.mark r*CoprimeShift.supportFactor r L A‖ *
      ‖FengAtG.coprimeScaled (cutoff L u/r) g L (u-Real.log r/L) θ G A-
        zeroEulerMain g (u-Real.log r/L) θ G A‖) ≤
      Real.exp (C*U)*∑ r ∈ Icc 1 (cutoff L u), mass r*innerError L g (u-Real.log r/L) θ G A := by
    calc
      _ ≤ ∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r => r.Coprime g),
          Real.exp (C*U)*(mass r*innerError L g (u-Real.log r/L) θ G A) := by
        apply sum_le_sum
        intro r hr
        have hr' := (mem_filter.mp hr).1
        have hr0 : r ≠ 0 := by have := (mem_Icc.mp hr').1; omega
        have hru : r ∈ Icc 1 (cutoff L U) := Icc_subset_Icc le_rfl
          (Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hL.le))) hr'
        dsimp only [cutoff]
        rw [CoprimeShift.translated_cutoff L u r hL.ne' hr0]
        have h := mul_le_mul_of_nonneg_right
          (FengOutsideBounds.mark_support_bound r L U C A hL hA hru)
          (norm_nonneg (CoprimeApproximation.actual L g (u-Real.log r/L) θ G A-
            zeroEulerMain g (u-Real.log r/L) θ G A))
        convert h using 1
        all_goals dsimp only [mass,innerError,actual,FengAtG.coprimeScaled]
        all_goals ring
      _ ≤ _ := by
        rw [mul_sum]
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro r _ _
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mass_nonneg r) (norm_nonneg _))
  have h := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤1/L^2)
  convert h using 1
  unfold rowBudget
  simp only [mul_sum]
  apply sum_congr rfl
  intros; ring

/-- Clip the interior cutoff up to delta. The error caused by clipping is
bounded using the short prime-power window, uniformly in the original u. -/
theorem rowBudget_split (L u θ U δ D : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ)
    (hL : 0 < L) (hu : u ∈ Set.Icc 0 U) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (he : 0 ≤ eulerMass g 0)
    (hb : ∀ v ∈ Set.Icc 0 U, innerError L g v θ G A ≤ D*eulerMass g 0) :
    rowBudget L u θ g G A ≤
      (∑ r ∈ Icc 1 (cutoff L U), (mass r/L^2)*
        innerError L g (max δ (u-Real.log r/L)) θ G A)+
      D*eulerMass g 0*(2*U*δ+windowError L U) := by
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 (cutoff L u))
    (fun r : ℕ => δ ≤ u-Real.log r/L)
    (fun r => (mass r/L^2)*innerError L g (u-Real.log r/L) θ G A)
  have hi : (∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r : ℕ => δ ≤ u-Real.log r/L),
      (mass r/L^2)*innerError L g (u-Real.log r/L) θ G A) ≤
      ∑ r ∈ Icc 1 (cutoff L U), (mass r/L^2)*innerError L g (max δ (u-Real.log r/L)) θ G A := by
    calc
      _ = ∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r : ℕ => δ ≤ u-Real.log r/L),
          (mass r/L^2)*innerError L g (max δ (u-Real.log r/L)) θ G A := by
        apply sum_congr rfl
        intro r hr
        rw [max_eq_right (mem_filter.mp hr).2]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        ((filter_subset _ _).trans (Icc_subset_Icc le_rfl (Nat.floor_mono
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hL.le)))))
        (fun r _ _ => mul_nonneg (div_nonneg (mass_nonneg r) (sq_nonneg L)) (norm_nonneg _))
  have ht : (∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r : ℕ => ¬δ ≤ u-Real.log r/L),
      (mass r/L^2)*innerError L g (u-Real.log r/L) θ G A) ≤
      D*eulerMass g 0*(2*U*δ+windowError L U) := by
    calc
      _ ≤ ∑ r ∈ (Icc 1 (cutoff L u)).filter (fun r : ℕ => ¬δ ≤ u-Real.log r/L),
          (mass r/L^2)*(D*eulerMass g 0) := by
        apply sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hb _ (translated_mem L u U hL hu r (mem_filter.mp hr).1))
          (div_nonneg (mass_nonneg r) (sq_nonneg L))
      _ = D*eulerMass g 0*((∑ r ∈ (Icc 1 (cutoff L u)).filter
          (fun r : ℕ => u-Real.log r/L<δ), mass r)/L^2) := by
        simp only [not_le,sum_div,mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (endpoint_mass L u U δ hL hu hδ) (mul_nonneg hD he)
  unfold rowBudget
  linarith

/-- The two sums are finite; swapping them puts the growing-g estimate on
an interior cutoff array for each prime power separately. -/
theorem rowBudget_average (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u : ℕ → ℝ) (A : ℂ),
      ‖A‖ ≤ C → (∀ g ∈ Icc 1 N, u g ∈ Set.Icc 0 U) →
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*rowBudget L (u g) θ g G A) ≤
        SupportTail.harmonic N*eps := by
  obtain ⟨D,hD,hbound⟩ := innerError_bound G hG θ C U hθ hC hU.le
  let K := 1+2*SupportProductTail.productConstant
  have hK : 0 ≤ K := by dsimp [K,SupportProductTail.productConstant]; positivity
  intro eps heps
  let δ := min U (eps/(8*(D*K*U+1)))
  have hd : 0 < δ := lt_min hU (by positivity)
  have hdU : δ ≤ U := min_le_left _ _
  have hdsmall : D*K*U*δ ≤ eps/8 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right U (eps/(8*(D*K*U+1))))
      (show 0≤D*K*U+1 by positivity)
    have he : (D*K*U+1)*(eps/(8*(D*K*U+1))) = eps/8 := by field_simp
    rw [he] at h
    nlinarith
  let eta := eps/(8*(U^2+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have htail : Tendsto (fun L => D*K*windowError L U) atTop (nhds 0) := by
    simpa using (windowError_tendsto U).const_mul (D*K)
  filter_upwards [eventually_gt_atTop (0:ℝ),innerError_average G hG θ C δ U hθ hC hd hU eta heta,
    htail.eventually (gt_mem_nhds (show (0:ℝ)<eps/4 by positivity))] with L hL hi ht
  intro N u A hA hu
  let m := fun r => mass r/L^2
  have hm : ∀ r, 0 ≤ m r := fun r => div_nonneg (mass_nonneg r) (sq_nonneg L)
  have hin : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*
      (∑ r ∈ Icc 1 (cutoff L U), m r*innerError L g (max δ (u g-Real.log r/L)) θ G A)) ≤
      SupportTail.harmonic N*eta*(2*U^2) := by
    simp only [mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ r ∈ Icc 1 (cutoff L U), m r*
          ∑ g ∈ Icc 1 N, (1/(g:ℝ))*innerError L g (max δ (u g-Real.log r/L)) θ G A*eulerMass g 0 := by
        apply sum_congr rfl; intro r hr; rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ ∑ r ∈ Icc 1 (cutoff L U), m r*(SupportTail.harmonic N*eta) := by
        apply sum_le_sum
        intro r hr
        apply mul_le_mul_of_nonneg_left (hi N _ A hA ?_) (hm r)
        intro g hg
        have hr1 : (1:ℝ)≤r := by exact_mod_cast (mem_Icc.mp hr).1
        have hlog : 0 ≤ Real.log r/L := div_nonneg (Real.log_nonneg hr1) hL.le
        exact ⟨le_max_left _ _,max_le hdU (by linarith [(hu g hg).2])⟩
      _ = (SupportTail.harmonic N*eta)*(FengPrimeMass.mass (cutoff L U)/L^2) := by
        rw [← mass_Icc,sum_div,mul_sum]
        apply sum_congr rfl; intros; dsimp [m]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (FengPrimeMass.scaled_mass_bound L U hL hU.le)
        (by unfold SupportTail.harmonic; positivity)
  have hsq : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0^2) ≤ SupportTail.harmonic N*K := by
    have he : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
    simpa only [he,K] using FengSharedInterior.euler_square_average N
  have he : 0 ≤ 2*U*δ+windowError L U := add_nonneg (by positivity)
    (windowError_nonneg L U hL.le hU.le)
  have hs : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*rowBudget L (u g) θ g G A) ≤
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*
        (∑ r ∈ Icc 1 (cutoff L U), m r*innerError L g (max δ (u g-Real.log r/L)) θ G A))+
      D*(2*U*δ+windowError L U)*(∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0^2) := by
    rw [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro g hg
    have hg0 : g ≠ 0 := by have := (mem_Icc.mp hg).1; omega
    have hE := euler_nonneg g hg0
    have hh := mul_le_mul_of_nonneg_left
      (rowBudget_split L (u g) θ U δ D g G A hL (hu g hg) hd.le hD hE
        (fun v hv => hbound L hL g hg0 v hv A hA))
      (mul_nonneg (by positivity : (0:ℝ)≤1/(g:ℝ)) hE)
    convert hh using 1
    dsimp only [m]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hD he)
  have hcoef : eta*(2*U^2)+D*(2*U*δ+windowError L U)*K ≤ eps := by
    have heta' : eta*(2*U^2) ≤ eps/4 := by
      dsimp [eta]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show 0<8*(U^2+1) by positivity)).mpr
      nlinarith
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hcoef
    (show 0≤SupportTail.harmonic N by unfold SupportTail.harmonic; positivity)
  nlinarith

def replacementError (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ) : ℝ :=
  ‖FengAtG.outsideBlock (cutoff L u) g L u θ G A-
    FengOutside.mainProxy (cutoff L u) g L u θ G A‖

/-- Actual outsideBlock, not its model: the Euler-weighted harmonic average
of its mainProxy replacement error is arbitrarily small, uniformly in N. -/
theorem replacement_average (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u : ℕ → ℝ) (A : ℂ),
      ‖A‖ ≤ C → (∀ g ∈ Icc 1 N, u g ∈ Set.Icc 0 U) →
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*replacementError L (u g) θ g G A) ≤
        SupportTail.harmonic N*eps := by
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),rowBudget_average G hG θ C U hθ hC hU
    (eps/Real.exp (C*U)) (by positivity)] with L hL hh
  intro N u A hA hu
  have hs : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*replacementError L (u g) θ g G A) ≤
      Real.exp (C*U)*∑ g ∈ Icc 1 N, (1/(g:ℝ))*eulerMass g 0*rowBudget L (u g) θ g G A := by
    rw [mul_sum]
    apply sum_le_sum
    intro g hg
    have he := euler_nonneg g (by have := (mem_Icc.mp hg).1; omega)
    have h := mul_le_mul_of_nonneg_left (block_error_bound L (u g) θ C U g G A hL (hu g hg) hA)
      (mul_nonneg (by positivity : (0:ℝ)≤1/(g:ℝ)) he)
    simpa only [replacementError,mul_assoc,mul_left_comm,mul_comm] using h
  apply hs.trans
  have h := mul_le_mul_of_nonneg_left (hh N u A hA hu) (Real.exp_pos (C*U)).le
  convert h using 1
  field_simp

def averageError (L U θ : ℝ) (G : Polynomial ℂ) (A : ℂ) : ℝ :=
  (∑ g ∈ Icc 1 (cutoff L U), (1/(g:ℝ))*eulerMass g 0*
    replacementError L (LogProfileSum.coordinate L U g) θ g G A)/L

theorem averageError_nonneg (L U θ : ℝ) (G : Polynomial ℂ) (A : ℂ) (hL : 0 ≤ L) :
    0 ≤ averageError L U θ G A := by
  apply div_nonneg _ hL
  apply sum_nonneg
  intro g hg
  exact mul_nonneg (mul_nonneg (by positivity)
    (euler_nonneg g (by have := (mem_Icc.mp hg).1; omega))) (norm_nonneg _)

/-- Growing g up to exp(L U), with the exact outer cutoff coordinate. -/
theorem averageError_uniform (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    TendstoUniformlyOn (fun L A => averageError L U θ G A) (fun _ => 0)
      atTop {A | ‖A‖ ≤ C} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hH := (harmonic_normalized U hU.le).eventually
    (gt_mem_nhds (show U<U+1 by linarith))
  filter_upwards [eventually_gt_atTop (0:ℝ),hH,
    replacement_average G hG θ C U hθ hC hU (eps/(2*(U+1))) (by positivity)] with L hL hHL hh
  intro A hA
  have hs := hh (cutoff L U) (fun g => LogProfileSum.coordinate L U g) A hA
    (fun g hg => translated_mem L U U hL ⟨hU.le,le_rfl⟩ g hg)
  have hb := div_le_div_of_nonneg_right hs hL.le
  have hc := mul_le_mul_of_nonneg_right hHL.le (show 0≤eps/(2*(U+1)) by positivity)
  have he : (U+1)*(eps/(2*(U+1))) = eps/2 := by field_simp
  rw [he] at hc
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (averageError_nonneg L U θ G A hL.le)]
  change _/L < eps
  rw [mul_div_right_comm] at hb
  exact (hb.trans hc).trans_lt (by linarith)

/-- Both reflected bidiscs are covered by one norm-bounded estimate. -/
theorem averageError_twoBidiscs (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ U : ℝ) (hθ : 0 < θ) (hU : 0 < U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageError L U θ G p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs := by
  have hh := averageError_uniform G hG θ (5*PRZZAsymptotic.R/4) U hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hh eps heps] with L hL
  intro p hp
  exact hL p.2 (ShiftedMobius.twoBidiscs_norm p hp).2

#print axioms replacement_average
#print axioms averageError_uniform
#print axioms averageError_twoBidiscs
#print axioms block_error_bound
#print axioms rowBudget_split
#print axioms rowBudget_average
end XiPrime8845.FengOutsideAverage
