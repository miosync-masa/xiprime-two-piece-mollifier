import FengSharedInterior

/-! Actual Conrey/shared product errors, uniformly including the cutoff endpoint.
The Conrey factor retains mu(g); the shared marked factor is not discarded. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengMixedInterior
open FengSharedTail FengSharedBounds FengAtG CoprimeApproximation
open CoprimeEndpoint CoprimeEulerCompletion LogProfileSum SupportTail
set_option maxHeartbeats 1000000

def conrey (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (μ g:ℂ)*actual L g u θ P A

def conreyMain (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (μ g:ℂ)*zeroEulerMain g u θ P A

/-- Literal finite Conrey sum at g*n, including its exact Mobius sign. -/
theorem conrey_eq (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    conrey L g u θ P A = (L:ℂ)*∑ n ∈ Icc 1 ⌊Real.exp (L*u)⌋₊,
      (μ (g*n):ℂ)/n * ShiftWeights.weight A u θ P (Real.log n/L) := by
  rw [conrey,actual,CoprimeShift.coprimeInner,Finset.sum_filter]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [SmoothMobius.moebius_mul_indicator]
  by_cases hc : n.Coprime g
  · simp only [if_pos hc]
    ring
  · simp [hc]

theorem moebius_norm (g : ℕ) : ‖(μ g:ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_intCast] using
    (show |(μ g:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g))

theorem head_product_error (L V u θ : ℝ) (g : ℕ) (hg : g ≠ 0) (hL : 0 < L)
    (ht : |Real.log g/L| ≤ V) (P G : Polynomial ℂ) (A B : ℂ) :
    ‖conrey L g u θ P A*(mark g L*actual L g u θ G B)-
      conreyMain g u θ P A*FengSharedInterior.main L g u θ G B‖ ≤
      V^2*productError L g u u θ P G A B := by
  rw [show conrey L g u θ P A*(mark g L*actual L g u θ G B)-
      conreyMain g u θ P A*FengSharedInterior.main L g u θ G B =
      ((μ g:ℂ)*mark g L)*(actual L g u θ P A*actual L g u θ G B-
        zeroEulerMain g u θ P A*zeroEulerMain g u θ G B) by
        unfold conrey conreyMain FengSharedInterior.main; ring, norm_mul]
  have hb : ‖(μ g:ℂ)*mark g L‖ ≤ V^2 := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (moebius_norm g)
      (mark_bound g hg L V hL ht) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem mixed_product_error_bound (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        ‖conrey L g u θ P A * sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B -
          conreyMain g u θ P A * FengSharedInterior.main L g u θ G B‖ ≤
          (D/L)*eulerMass g 0^2 + V^2*productError L g u u θ P G A B := by
  obtain ⟨DG,hDG,hEG⟩ := shared_head_error G hG θ C U V hθ hC hU hV
  obtain ⟨BP,hBP,hBP'⟩ := FengSharedInterior.actual_coprime_bound P hP θ C U hθ hC hU
  refine ⟨BP*DG,by positivity,?_⟩
  intro L hL g hg ht u hu A B hA hB
  have hE := euler_nonneg g hg
  have hx : ‖conrey L g u θ P A‖ ≤ BP*eulerMass g 0 := by
    rw [conrey,norm_mul]
    simpa only [one_mul] using mul_le_mul (moebius_norm g)
      (hBP' L hL g hg u hu A hA) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hy := hEG L hL g hg ht u hu B hB
  have hxy : ‖conrey L g u θ P A*sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B-
      conrey L g u θ P A*(mark g L*actual L g u θ G B)‖ ≤
      ((BP*DG)/L)*eulerMass g 0^2 := by
    rw [← mul_sub,norm_mul]
    have hh := mul_le_mul hx hy (norm_nonneg _) (by positivity : 0≤BP*eulerMass g 0)
    calc
      _ ≤ (BP*eulerMass g 0)*((DG/L)*eulerMass g 0) := hh
      _ = _ := by ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ (conrey L g u θ P A*(mark g L*actual L g u θ G B)) _).trans
    (add_le_add hxy (head_product_error L V u θ g hg hL ht P G A B))

def averageRemainder (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℝ :=
  (∑ g ∈ Ioc 0 (cutoff L U), (1/(g:ℝ))*
    ‖conrey L g (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B -
      conreyMain g (coordinate L U g) θ P A * FengSharedInterior.main L g (coordinate L U g) θ G B‖)/L

theorem averageRemainder_bound (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
      averageRemainder L U θ P G A B ≤
        (D/L)*(SupportTail.harmonic (cutoff L U)/L)*(1+2*SupportProductTail.productConstant) +
        U^2*CoprimeGluing.averageError L U θ P G A B := by
  obtain ⟨D,hD,h⟩ := mixed_product_error_bound P G hP hG θ C U U hθ hC hU.le hU.le
  refine ⟨D,hD,?_⟩
  intro L hL A B hA hB
  have hs : ∀ g ∈ Ioc 0 (cutoff L U),
      0 < (g:ℝ) ∧ (g:ℝ) ≤ Real.exp (L*U) := by
    intro g hg
    exact ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
      (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩
  have hb : averageRemainder L U θ P G A B ≤
      ((D/L)*(∑ g ∈ Ioc 0 (cutoff L U),(1/(g:ℝ))*eulerMass g 0^2))/L+
        U^2*CoprimeGluing.averageError L U θ P G A B := by
    unfold averageRemainder CoprimeGluing.averageError
    rw [← mul_div_assoc,← add_div]
    apply div_le_div_of_nonneg_right _ hL.le
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro g hg
    have hg1 : (1:ℝ)≤g := by exact_mod_cast (mem_Ioc.mp hg).1
    have ht := ShiftWeights.normalized_log_mem (g:ℝ) L U hg1 hL
      ((Real.log_le_iff_le_exp (hs g hg).1).mpr (hs g hg).2)
    have hu := coordinate_mem L U g hL ⟨hg1,(hs g hg).2⟩
    have hh := mul_le_mul_of_nonneg_left (h L hL g (by have := (mem_Ioc.mp hg).1; omega)
      (by rw [abs_of_nonneg ht.1]; exact ht.2) _ hu A B hA hB) (by positivity : 0≤1/(g:ℝ))
    convert hh using 1; ring
  apply hb.trans
  apply add_le_add _ le_rfl
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (FengSharedInterior.euler_square_average (cutoff L U)) (by positivity : 0≤D/L)) hL.le
  convert hh using 1; ring

theorem averageRemainder_uniform (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageRemainder L U θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hbound⟩ := averageRemainder_bound P G hP hG θ C U hθ hC hU
  have hd : Tendsto (fun L : ℝ => D/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul D
  have ht : Tendsto (fun L : ℝ => (D/L)*(SupportTail.harmonic (cutoff L U)/L)*(1+2*SupportProductTail.productConstant))
      atTop (nhds 0) := by
    simpa using (hd.mul (CoprimeEndpoint.harmonic_normalized U hU.le)).mul_const (1+2*SupportProductTail.productConstant)
  have hi := CoprimeGluing.averageError_uniform P G hP hG θ C U hθ hC hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps/(2*(U^2+1)) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<eps/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp hi _ he] with L hL htail hinner
  intro p hp
  have hh := hinner p hp
  rw [dist_comm,Real.dist_eq,sub_zero] at hh
  have hin : CoprimeGluing.averageError L U θ P G p.1 p.2 < eps/(2*(U^2+1)) :=
    (le_abs_self _).trans_lt hh
  have hz : U^2*CoprimeGluing.averageError L U θ P G p.1 p.2 < eps/2 := by
    have hh := (lt_div_iff₀ (show 0<2*(U^2+1) by positivity)).mp hin
    have hn : 0 ≤ CoprimeGluing.averageError L U θ P G p.1 p.2 := by
      unfold CoprimeGluing.averageError productError; positivity
    nlinarith
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (show 0≤averageRemainder L U θ P G p.1 p.2 by
    unfold averageRemainder; positivity)]
  exact (hbound L hL p.1 p.2 hp.1 hp.2).trans_lt (by linarith)

theorem averageRemainder_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (θ U : ℝ) (hθ : 0 < θ) (hU : 0 < U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageRemainder L U θ P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs :=
  (averageRemainder_uniform P G hP hG θ (5*PRZZAsymptotic.R/4) U hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hU).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

#print axioms conrey_eq
#print axioms moebius_norm
#print axioms head_product_error
#print axioms mixed_product_error_bound
#print axioms averageRemainder_bound
#print axioms averageRemainder_uniform
#print axioms averageRemainder_twoBidiscs
end XiPrime8845.FengMixedInterior

