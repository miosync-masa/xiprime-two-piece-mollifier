import CoprimeEndpoint

/-! Glue interior coprime-product asymptotics to the cutoff endpoint in the
actual harmonic average. All endpoint and PNT bounds are discharged. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.CoprimeGluing
open CoprimeEndpoint CoprimeEulerCompletion LogProfileSum
set_option maxHeartbeats 1000000

def averageError (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℝ :=
  (∑ g ∈ Ioc 0 (cutoff L U), (1/(g:ℝ))*
    productError L g (coordinate L U g) (coordinate L U g) θ P G A B)/L

theorem harmonic_pos (N : ℕ) (hN : 1 ≤ N) : 0 < SupportTail.harmonic N := by
  have h : (1/(1:ℝ)) ≤ SupportTail.harmonic N := by
    simpa only [SupportTail.harmonic, Nat.cast_one] using
      (Finset.single_le_sum (f := fun n : ℕ => 1/(n:ℝ)) (fun n _ => by positivity)
        (Finset.mem_Icc.mpr ⟨le_rfl,hN⟩))
  norm_num at h
  linarith

theorem head_coordinate (L U delta : ℝ) (hL : 0 < L) (_hd : delta ≤ U)
    (g : ℕ) (hg : g ∈ Ioc 0 (cutoff L (U-delta))) :
    coordinate L U g ∈ Set.Icc delta U := by
  have hg0 : (0:ℝ) < g := by exact_mod_cast (mem_Ioc.mp hg).1
  have hcut := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  have hlog := (Real.log_le_iff_le_exp hg0).mpr hcut
  have hn : 0 ≤ Real.log g := Real.log_nonneg (by exact_mod_cast (mem_Ioc.mp hg).1)
  have hu : Real.log g/L ≤ U-delta := (div_le_iff₀ hL).mpr (by nlinarith)
  have hl := div_nonneg hn hL.le
  unfold coordinate
  exact ⟨by linarith,by linarith⟩

/-- The endpoint has now been glued to the interior. Uniformity includes
both reflected shift regions through the common norm bound C. -/
theorem averageError_uniform (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageError L U θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hdom⟩ := product_error_dominated P G hP hG θ C U hθ hC hU.le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨delta,hd,hdU,hend⟩ := endpoint_small P G θ C U D hU hD hdom (eps/2) (by positivity)
  let eta := eps/(2*(U+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hi := actual_product_average_uniform P G hP hG θ C delta U hθ hC hd hU eta heta
  filter_upwards [eventually_gt_atTop (0:ℝ),hend,hi,
    (harmonic_normalized U hU.le).eventually (gt_mem_nhds (show U < U+1 by linarith))]
      with L hL hendL hiL hH
  intro p hp
  let M := cutoff L (U-delta)
  let N := cutoff L U
  have hMN : M ≤ N := Nat.floor_mono (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (by linarith : U-delta ≤ U) hL.le))
  have hM : 1 ≤ M := (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by
    simpa using Real.one_le_exp_iff.mpr (mul_nonneg hL.le (sub_nonneg.mpr hdU)))
  have heq : Icc 1 M = Ioc 0 M := by ext g; simp only [mem_Icc,mem_Ioc]; omega
  have hint := hiL M (fun g => coordinate L U g) (fun g => coordinate L U g) p.1 p.2 hp.1 hp.2
    (fun g hg => head_coordinate L U delta hL hdU g (heq ▸ hg))
    (fun g hg => head_coordinate L U delta hL hdU g (heq ▸ hg))
  rw [heq] at hint
  change (∑ g ∈ Ioc 0 M, (1/(g:ℝ))*productError L g (coordinate L U g) (coordinate L U g) θ P G p.1 p.2)/
    SupportTail.harmonic M < eta at hint
  have hhead : (∑ g ∈ Ioc 0 M, (1/(g:ℝ))*productError L g (coordinate L U g) (coordinate L U g) θ P G p.1 p.2)/L < eps/2 := by
    have hs := (div_lt_iff₀ (harmonic_pos M hM)).mp hint
    have hh := mul_le_mul_of_nonneg_left (SupportTail.harmonic_mono hMN) heta.le
    have hsum : (∑ g ∈ Ioc 0 M, (1/(g:ℝ))*productError L g (coordinate L U g) (coordinate L U g) θ P G p.1 p.2) <
        SupportTail.harmonic N*eta := by nlinarith [hs,hh]
    have hb := (div_lt_div_of_pos_right hsum hL)
    have hc := mul_lt_mul_of_pos_right hH heta
    have he : (U+1)*eta = eps/2 := by dsimp [eta]; field_simp
    rw [he] at hc
    apply hb.trans
    convert hc using 1
    ring
  have htail := hendL p.1 p.2 hp.1 hp.2
  have hsplit := Finset.sum_Ioc_consecutive
    (fun g : ℕ => (1/(g:ℝ))*productError L g (coordinate L U g) (coordinate L U g) θ P G p.1 p.2)
    (Nat.zero_le M) hMN
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (show 0 ≤ averageError L U θ P G p.1 p.2 by
    unfold averageError productError; positivity)]
  unfold averageError
  rw [← hsplit,add_div]
  linarith

#print axioms averageError_uniform
end XiPrime8845.CoprimeGluing
