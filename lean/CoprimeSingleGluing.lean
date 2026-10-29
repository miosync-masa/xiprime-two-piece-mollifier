import CoprimeEulerError
import FengLogEndpoint

/-! The single-inner error with its Euler envelope, including the outer endpoint.
This supplies an actual averaged replacement, not pointwise uniformity in g. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.CoprimeSingleGluing
open CoprimeEulerError CoprimeEndpoint LogProfileSum
set_option maxHeartbeats 1000000

def average (L U θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℝ :=
  (∑ g ∈ Ioc 0 (cutoff L U), (1/(g:ℝ))*innerError L g (coordinate L U g) θ P A*
    SupportTail.eulerMass g 0)/L

theorem average_nonneg (L U θ : ℝ) (P : Polynomial ℂ) (A : ℂ) (hL : 0 ≤ L) :
    0 ≤ average L U θ P A := by
  unfold average
  apply div_nonneg _ hL
  apply sum_nonneg
  intro g hg
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (euler_nonneg g (mem_Ioc.mp hg).1.ne')

theorem average_uniform (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    TendstoUniformlyOn (fun L A => average L U θ P A) (fun _ => 0) atTop {A | ‖A‖ ≤ C} := by
  obtain ⟨D,hD,hdom⟩ := innerError_bound P hP θ C U hθ hC hU.le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨δ,hd,hdU,hend⟩ := FengLogEndpoint.euler_window_small U D (eps/2) hU hD (by positivity)
  let eta := eps/(4*(U+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),hend,
    innerError_average P hP θ C δ U hθ hC hd hU eta heta,
    (harmonic_normalized U hU.le).eventually (gt_mem_nhds (show U < U+1 by linarith))]
      with L hL hendL hiL hH
  intro A hA
  let M := cutoff L (U-δ)
  let N := cutoff L U
  have hMN : M ≤ N := Nat.floor_mono (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (by linarith : U-δ ≤ U) hL.le))
  have heq : Icc 1 M = Ioc 0 M := by ext g; simp only [mem_Icc,mem_Ioc]; omega
  have hint := hiL M (fun g => coordinate L U g) A hA
    (fun g hg => CoprimeGluing.head_coordinate L U δ hL hdU g (heq ▸ hg))
  rw [heq] at hint
  have hhead : (∑ g ∈ Ioc 0 M, (1/(g:ℝ))*innerError L g (coordinate L U g) θ P A*
      SupportTail.eulerMass g 0)/L < eps/2 := by
    have hb := div_le_div_of_nonneg_right (hint.trans
      (mul_le_mul_of_nonneg_right (SupportTail.harmonic_mono hMN) heta.le)) hL.le
    have hc := mul_lt_mul_of_pos_right hH heta
    have he : (U+1)*eta = eps/4 := by dsimp [eta]; field_simp
    rw [he] at hc
    have hbc : (SupportTail.harmonic N*eta)/L < eps/4 := by
      simpa only [mul_div_assoc,div_mul_eq_mul_div,N] using hc
    exact hb.trans_lt (hbc.trans (by linarith))
  have htail := hendL (fun g => innerError L g (coordinate L U g) θ P A*SupportTail.eulerMass g 0)
    (by
      intro g hg
      have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
      have hu := EndpointAverage.endpoint_cutoff_mem L U δ hL g hg
      have hh := mul_le_mul_of_nonneg_right
        (hdom L hL g hg0 _ ⟨hu.1,hu.2.trans hdU⟩ A hA) (euler_nonneg g hg0)
      simpa only [pow_two,mul_assoc,coordinate] using hh)
  have hsplit := sum_Ioc_consecutive
    (fun g : ℕ => (1/(g:ℝ))*innerError L g (coordinate L U g) θ P A*SupportTail.eulerMass g 0)
    (Nat.zero_le M) hMN
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (average_nonneg L U θ P A hL.le)]
  unfold average
  rw [← hsplit,add_div]
  simp only [← mul_assoc] at htail
  linarith

#print axioms average_nonneg
#print axioms average_uniform
end XiPrime8845.CoprimeSingleGluing
