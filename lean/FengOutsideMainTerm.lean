import FengOutsideProxy

/-! The actual Conrey/outside limit and the discharged Conrey/Feng block sum.
These are arithmetic limits before the common theta^-2 normalization, not
the full K22 calculation or a zero-counting assertion. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.FengOutsideMainTerm
open FengCrossAssembly FengOutsideProxy FengInverseProfile LogProfileSum BetaKernel

theorem outsideProxy_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 (-1) 1)
      atTop ElementaryGcd.twoBidiscs := by
  let θ := PRZZAsymptotic.theta
  let C := 5*PRZZAsymptotic.R/4
  have hθ : 0 < θ := by norm_num [θ,PRZZAsymptotic.theta]
  have hC : 0 ≤ C := by dsimp [C]; have := PRZZAsymptotic.radius_pos; positivity
  have h1 := (proxy_sub_zero_uniform P G hP hG θ C hθ hC ShiftedEulerUniform.witness_size).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have h2 := (zeroModel_sub_profile_uniform P G θ C hθ hC ShiftedEulerUniform.witness_size).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have h3 := (zero_profile_uniform P G θ C θ hθ hC hθ.le).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  simp only [integral_kernel] at h3
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h1 (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp h2 (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp h3 (eps/3) (by positivity)] with L he1 he2 he3
  intro p hp
  have ha := he1 p hp
  have hb := he2 p hp
  have hc := he3 p hp
  rw [dist_comm,dist_eq_norm,sub_zero] at ha hb
  rw [dist_comm,dist_eq_norm] at hc ⊢
  have ht := norm_sub_le_norm_sub_add_norm_sub (outsideProxy L θ P G p.1 p.2)
    (zeroModel L θ P G p.1 p.2) (monomialIntegral p.1 p.2 θ P G 1 (-1) 1)
  have ht' := norm_sub_le_norm_sub_add_norm_sub (zeroModel L θ P G p.1 p.2)
    (zeroSum L θ (profile θ P G p.1 p.2)) (monomialIntegral p.1 p.2 θ P G 1 (-1) 1)
  linarith

theorem outsideProxy_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideProxy L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 (-1) 1)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (outsideProxy_twoBidiscs P G hP hG)

/-- Discharges the previously named actual outside arithmetic obligation. -/
theorem outsideAsymptotic (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    OutsideAsymptotic P G := by
  have he := FengOutsideReplacement.outside_sub_proxy_twoBidiscs P G hP hG
  have hm := outsideProxy_twoBidiscs P G hP hG
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp he (eps/2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hm (eps/2) (by positivity)] with L heL hmL
  intro p hp
  have hx := heL p hp
  have hy := hmL p hp
  rw [dist_comm,dist_eq_norm,sub_zero] at hx
  rw [dist_comm,dist_eq_norm] at hy ⊢
  exact (norm_sub_le_norm_sub_add_norm_sub _ (outsideProxy L PRZZAsymptotic.theta P G p.1 p.2) _).trans_lt
    (by linarith)

theorem outsideSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 (-1) 1)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (outsideAsymptotic P G hP hG)

/-- All three actual blocks, with no remaining outside premise. -/
theorem fullSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => poleSum 0 2 (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs :=
  fullSum_twoBidiscs_of_outside P G hP hG (outsideAsymptotic P G hP hG)

theorem fullSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => poleSum 0 2 (monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (fullSum_twoBidiscs P G hP hG)

#print axioms outsideProxy_twoBidiscs
#print axioms outsideProxy_reflected
#print axioms outsideAsymptotic
#print axioms outsideSum_reflected
#print axioms fullSum_twoBidiscs
#print axioms fullSum_reflected
end XiPrime8845.FengOutsideMainTerm
