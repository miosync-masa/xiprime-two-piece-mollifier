import FengSharedTail
import CoprimeGluing

/-! Actual averaged shared-product remainder. The retained marked-prime
main term is not identified with its limiting outer profile integral here. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSharedInterior
open FengSharedTail FengSharedBounds FengAtG CoprimeApproximation
open CoprimeEndpoint CoprimeEulerCompletion LogProfileSum SupportTail
set_option maxHeartbeats 1000000

def main (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  mark g L * zeroEulerMain g u θ P A

theorem head_product_error (L V u θ : ℝ) (g : ℕ) (hg : g ≠ 0) (hL : 0 < L)
    (ht : |Real.log g/L| ≤ V) (P G : Polynomial ℂ) (A B : ℂ) :
    ‖(mark g L*actual L g u θ P A)*(mark g L*actual L g u θ G B)-
      main L g u θ P A*main L g u θ G B‖ ≤
      V^4*productError L g u u θ P G A B := by
  rw [show (mark g L*actual L g u θ P A)*(mark g L*actual L g u θ G B)-
      main L g u θ P A*main L g u θ G B =
      (mark g L)^2*(actual L g u θ P A*actual L g u θ G B-
        zeroEulerMain g u θ P A*zeroEulerMain g u θ G B) by unfold main; ring,
    norm_mul,norm_pow]
  have h := pow_le_pow_left₀ (norm_nonneg _) (mark_bound g hg L V hL ht) 2
  have he : (V^2)^2 = V^4 := by ring
  rw [he] at h
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem actual_coprime_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖actual L g u θ P A‖ ≤ D*eulerMass g 0 := by
  obtain ⟨K,hK,h⟩ := ShiftedEndpoint.absoluteError_bounded
  have hD : 0 ≤ ShiftedEndpoint.coprimeCap P θ C U K := mul_nonneg (Real.exp_pos _).le
    (ShiftedEndpoint.scaledCap_nonneg P θ C U K hθ hC hU hK)
  refine ⟨_,hD,?_⟩
  intro L hL g hg u hu A hA
  exact (ShiftedEndpoint.scaled_coprime_common_bound P hP A g L u θ C U K hL hθ hA hu hK h).trans
    (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hD)

theorem shared_product_error_bound (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A * sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B -
          main L g u θ P A * main L g u θ G B‖ ≤
          (D/L)*eulerMass g 0^2 + V^4*productError L g u u θ P G A B := by
  obtain ⟨DP,hDP,hEP⟩ := shared_head_error P hP θ C U V hθ hC hU hV
  obtain ⟨DG,hDG,hEG⟩ := shared_head_error G hG θ C U V hθ hC hU hV
  obtain ⟨BG,hBG,hBG'⟩ := sharedBlock_euler_bound G hG θ C U V hθ hC hU
  obtain ⟨BP,hBP,hBP'⟩ := actual_coprime_bound P hP θ C U hθ hC hU
  refine ⟨DP*BG+V^2*BP*DG,by positivity,?_⟩
  intro L hL g hg ht u hu A B hA hB
  let x := sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A
  let y := sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B
  let x₀ := mark g L*actual L g u θ P A
  let y₀ := mark g L*actual L g u θ G B
  have hE := euler_nonneg g hg
  have hx : ‖x-x₀‖ ≤ (DP/L)*eulerMass g 0 := hEP L hL g hg ht u hu A hA
  have hy : ‖y-y₀‖ ≤ (DG/L)*eulerMass g 0 := hEG L hL g hg ht u hu B hB
  have hyb : ‖y‖ ≤ BG*eulerMass g 0 := hBG' L hL g hg ht u hu B hB
  have hxb : ‖x₀‖ ≤ (V^2*BP)*eulerMass g 0 := by
    dsimp only [x₀]; rw [norm_mul]
    have h := mul_le_mul (mark_bound g hg L V hL ht) (hBP' L hL g hg u hu A hA)
      (norm_nonneg _) (sq_nonneg V)
    simpa only [mul_assoc] using h
  have hxy : ‖x*y-x₀*y₀‖ ≤ ((DP*BG+V^2*BP*DG)/L)*eulerMass g 0^2 := by
    rw [show x*y-x₀*y₀=(x-x₀)*y+x₀*(y-y₀) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    have h1 := mul_le_mul hx hyb (norm_nonneg _) (by positivity : 0≤(DP/L)*eulerMass g 0)
    have h2 := mul_le_mul hxb hy (norm_nonneg _) (by positivity : 0≤(V^2*BP)*eulerMass g 0)
    convert add_le_add h1 h2 using 1; ring
  exact (norm_sub_le_norm_sub_add_norm_sub (x*y) (x₀*y₀) _).trans
    (add_le_add hxy (head_product_error L V u θ g hg hL ht P G A B))

def averageRemainder (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℝ :=
  (∑ g ∈ Ioc 0 (cutoff L U), (1/(g:ℝ))*
    ‖sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B -
      main L g (coordinate L U g) θ P A * main L g (coordinate L U g) θ G B‖)/L

theorem euler_square_average (N : ℕ) :
    (∑ g ∈ Ioc 0 N, (1/(g:ℝ))*eulerMass g 0^2) ≤
      SupportTail.harmonic N*(1+2*SupportProductTail.productConstant) := by
  have h := full_window 0 N 1 (Nat.zero_le _) (by norm_num)
  have h0 : SupportTail.harmonic 0 = 0 := by simp [SupportTail.harmonic]
  have h1 : SupportTail.harmonic 1 = 1 := by norm_num [SupportTail.harmonic]
  rw [h0,h1] at h
  norm_num at h
  simp only [one_div]
  nlinarith [h]

theorem averageRemainder_bound (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
      averageRemainder L U θ P G A B ≤
        (D/L)*(SupportTail.harmonic (cutoff L U)/L)*(1+2*SupportProductTail.productConstant) +
        U^4*CoprimeGluing.averageError L U θ P G A B := by
  obtain ⟨D,hD,h⟩ := shared_product_error_bound P G hP hG θ C U U hθ hC hU.le hU.le
  refine ⟨D,hD,?_⟩
  intro L hL A B hA hB
  have hs : ∀ g ∈ Ioc 0 (cutoff L U),
      0 < (g:ℝ) ∧ (g:ℝ) ≤ Real.exp (L*U) := by
    intro g hg
    exact ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
      (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩
  have hb : averageRemainder L U θ P G A B ≤
      ((D/L)*(∑ g ∈ Ioc 0 (cutoff L U),(1/(g:ℝ))*eulerMass g 0^2))/L+
        U^4*CoprimeGluing.averageError L U θ P G A B := by
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
    (euler_square_average (cutoff L U)) (by positivity : 0≤D/L)) hL.le
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
  have he : 0 < eps/(2*(U^4+1)) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<eps/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp hi _ he] with L hL htail hinner
  intro p hp
  have hh := hinner p hp
  rw [dist_comm,Real.dist_eq,sub_zero] at hh
  have hin : CoprimeGluing.averageError L U θ P G p.1 p.2 < eps/(2*(U^4+1)) :=
    (le_abs_self _).trans_lt hh
  have hz : U^4*CoprimeGluing.averageError L U θ P G p.1 p.2 < eps/2 := by
    have hh := (lt_div_iff₀ (show 0<2*(U^4+1) by positivity)).mp hin
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

#print axioms head_product_error
#print axioms actual_coprime_bound
#print axioms shared_product_error_bound
#print axioms euler_square_average
#print axioms averageRemainder_bound
#print axioms averageRemainder_uniform
#print axioms averageRemainder_twoBidiscs
end XiPrime8845.FengSharedInterior
