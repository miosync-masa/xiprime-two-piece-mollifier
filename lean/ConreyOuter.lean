import BareEulerUniform
import CoprimeGluing

/-! The actual diagonal Conrey product sum, with its literal generalized-totient
prefactor, converges to H00. Identification with a chosen PRZZ coefficient sum,
the Feng terms and zero counting are separate obligations. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.ConreyOuter
open CoprimeEndpoint CoprimeEulerCompletion LogProfileSum OuterProfile
set_option maxHeartbeats 1000000

def actualSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), BareEuler.weight (A/L) (B/L) g *
    CoprimeApproximation.actual L g (coordinate L θ g) θ P A *
    CoprimeApproximation.actual L g (coordinate L θ g) θ G B)/(L:ℂ)

def zeroModel (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), BareEuler.weight (A/L) (B/L) g *
    zeroEulerMain g (coordinate L θ g) θ P A *
    zeroEulerMain g (coordinate L θ g) θ G B)/(L:ℂ)

theorem actual_sub_zero_bound (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hL : 0 < L)
    (hw : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.weight (A/L) (B/L) g‖ ≤ 2/(g:ℝ)) :
    ‖actualSum L θ P G A B-zeroModel L θ P G A B‖ ≤
      2*CoprimeGluing.averageError L θ θ P G A B := by
  rw [actualSum,zeroModel,← sub_div,← Finset.sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  unfold CoprimeGluing.averageError
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro g hg
  rw [show BareEuler.weight (A/L) (B/L) g * CoprimeApproximation.actual L g (coordinate L θ g) θ P A *
      CoprimeApproximation.actual L g (coordinate L θ g) θ G B-
      BareEuler.weight (A/L) (B/L) g * zeroEulerMain g (coordinate L θ g) θ P A *
      zeroEulerMain g (coordinate L θ g) θ G B =
      BareEuler.weight (A/L) (B/L) g *
      (CoprimeApproximation.actual L g (coordinate L θ g) θ P A *
       CoprimeApproximation.actual L g (coordinate L θ g) θ G B-
       zeroEulerMain g (coordinate L θ g) θ P A * zeroEulerMain g (coordinate L θ g) θ G B) by ring,
    norm_mul]
  convert mul_le_mul_of_nonneg_right (hw g hg) (norm_nonneg _) using 1
  simp only [productError]
  ring

theorem actual_sub_zero_uniform (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => actualSum L θ P G p.1 p.2-zeroModel L θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have h := CoprimeGluing.averageError_uniform P G hP hG θ C θ hθ hC hθ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ), BareEulerUniform.weight_bound_eventually C θ hsize,
    Metric.tendstoUniformlyOn_iff.mp h (eps/2) (by positivity)] with L hL hw he
  intro p hp
  have hb := actual_sub_zero_bound L θ P G p.1 p.2 hL (by
    intro g hg
    exact hw g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2)
  have hh := he p hp
  rw [dist_comm,Real.dist_eq,sub_zero] at hh
  rw [dist_comm,dist_eq_norm,sub_zero]
  exact hb.trans_lt (by linarith [le_abs_self (CoprimeGluing.averageError L θ θ P G p.1 p.2)])

theorem zero_sub_model_bound (L θ C eta : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hL : 0 < L) (hθ : 0 < θ) (heta : 0 ≤ eta) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hw : ∀ g ∈ Ioc 0 (cutoff L θ),
      ‖BareEuler.weight (A/L) (B/L) g *
        (ShiftedTotient.euler 0 g*ShiftedTotient.euler 0 g-
          ShiftedTotient.euler (A/L) g*ShiftedTotient.euler (B/L) g)‖ ≤
        ((μ g:ℝ)^2/g.totient)*eta) :
    ‖zeroModel L θ P G A B-modelSum L θ P G A B‖ ≤
      (TotientHarmonic.summatory (Real.exp (L*θ))/L)*eta*valueCap P G θ C θ := by
  have hcut : ⌊Real.exp (L*θ)⌋₊ = cutoff L θ := rfl
  rw [zeroModel,modelSum,hcut,← sub_div,← Finset.sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hcap : 0 ≤ valueCap P G θ C θ := mul_nonneg
    (WeightDerivatives.firstCap_nonneg _ _ _ _ hθ ((norm_nonneg A).trans hA) hθ.le)
    (WeightDerivatives.firstCap_nonneg _ _ _ _ hθ ((norm_nonneg A).trans hA) hθ.le)
  have hs : (∑ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.weight (A/L) (B/L) g *
      zeroEulerMain g (coordinate L θ g) θ P A * zeroEulerMain g (coordinate L θ g) θ G B-
      BareEuler.weight (A/L) (B/L) g * eulerMain L g (coordinate L θ g) θ P A *
        eulerMain L g (coordinate L θ g) θ G B‖) ≤
      TotientHarmonic.summatory (Real.exp (L*θ))*eta*valueCap P G θ C θ := by
    unfold TotientHarmonic.summatory
    rw [hcut,Finset.sum_mul,Finset.sum_mul]
    apply sum_le_sum
    intro g hg
    have hg0 : g ≠ 0 := (mem_Ioc.mp hg).1.ne'
    rw [zeroEulerMain_eq,zeroEulerMain_eq]
    have he : BareEuler.weight (A/L) (B/L) g *
        (ShiftedTotient.euler 0 g*ShiftedMobius.mainTerm (coordinate L θ g) θ P A) *
        (ShiftedTotient.euler 0 g*ShiftedMobius.mainTerm (coordinate L θ g) θ G B)-
        BareEuler.weight (A/L) (B/L) g * eulerMain L g (coordinate L θ g) θ P A *
        eulerMain L g (coordinate L θ g) θ G B =
        (BareEuler.weight (A/L) (B/L) g * (ShiftedTotient.euler 0 g*ShiftedTotient.euler 0 g-
          ShiftedTotient.euler (A/L) g*ShiftedTotient.euler (B/L) g))*
          profile θ P G A B (coordinate L θ g) := by unfold eulerMain profile; ring
    rw [he,norm_mul]
    exact mul_le_mul (hw g hg) (profile_bound θ C θ _ P G A B hθ hA hB
      (coordinate_mem L θ g hL ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
        (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩))
      (norm_nonneg _) (by positivity)
  have hh := div_le_div_of_nonneg_right ((norm_sum_le _ _).trans hs) hL.le
  convert hh using 1
  · rfl
  · rfl
  · ring

theorem zero_sub_model_uniform (P G : Polynomial ℂ) (θ C : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => zeroModel L θ P G p.1 p.2-modelSum L θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  let V := valueCap P G θ C θ
  have hV : 0 ≤ V := mul_nonneg
    (WeightDerivatives.firstCap_nonneg _ _ _ _ hθ hC hθ.le)
    (WeightDerivatives.firstCap_nonneg _ _ _ _ hθ hC hθ.le)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  let eta := eps/(2*((θ+1)*V+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have ht := Metric.tendstoUniformlyOn_iff.mp TotientHarmonic.normalized_uniform 1 (by norm_num)
  filter_upwards [eventually_gt_atTop (0:ℝ),ht,
    BareEulerUniform.weighted_Euler_error_uniform C θ hsize eta heta] with L hL htL hw
  intro p hp
  have hmass : TotientHarmonic.summatory (Real.exp (L*θ))/L ≤ θ+1 := by
    have h := htL θ hθ.le
    rw [dist_comm,Real.dist_eq] at h
    linarith [le_abs_self (TotientHarmonic.summatory (Real.exp (L*θ))/L-θ)]
  have hb := zero_sub_model_bound L θ C eta P G p.1 p.2 hL hθ heta.le hp.1 hp.2 (by
    intro g hg
    exact hw g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2)
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass heta.le) hV
  have he : eta*((θ+1)*V+1) = eps/2 := by dsimp [eta]; field_simp
  rw [dist_comm,dist_eq_norm,sub_zero]
  exact hb.trans_lt (by change _ < eps; nlinarith [hc])

/-- The literal diagonal Conrey sum, including its endpoint, on BOTH domains. -/
theorem actualSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P G)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hC : 0 ≤ 5*PRZZAsymptotic.R/4 := by have := PRZZAsymptotic.radius_pos; positivity
  have h1 := (actual_sub_zero_uniform P G hP hG _ _ hθ hC ShiftedEulerUniform.witness_size).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have h2 := (zero_sub_model_uniform P G _ _ hθ hC ShiftedEulerUniform.witness_size).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have h3 := modelSum_twoBidiscs P G
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h1 (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp h2 (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp h3 (eps/3) (by positivity)] with L h1L h2L h3L
  intro p hp
  have ha := h1L p hp
  have hb := h2L p hp
  have hc := h3L p hp
  rw [dist_comm,dist_eq_norm,sub_zero] at ha hb
  rw [dist_comm,dist_eq_norm] at hc ⊢
  have h := norm_sub_le_norm_sub_add_norm_sub
    (actualSum L PRZZAsymptotic.theta P G p.1 p.2) (zeroModel L PRZZAsymptotic.theta P G p.1 p.2)
    (BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P G)
  have h' := norm_sub_le_norm_sub_add_norm_sub
    (zeroModel L PRZZAsymptotic.theta P G p.1 p.2) (modelSum L PRZZAsymptotic.theta P G p.1 p.2)
    (BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P G)
  linarith

theorem actualSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => BetaKernel.H 0 0 (-p.2) (-p.1) PRZZAsymptotic.theta P G)
      atTop PRZZAsymptotic.witnessBidisc := by
  have h := actualSum_twoBidiscs P G hP hG
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  exact hL (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)

#print axioms actual_sub_zero_uniform
#print axioms zero_sub_model_uniform
#print axioms actualSum_twoBidiscs
#print axioms actualSum_reflected
end XiPrime8845.ConreyOuter
