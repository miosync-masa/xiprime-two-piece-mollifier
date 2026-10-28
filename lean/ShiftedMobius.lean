import WeightedMobius
import WeightDerivatives
import FiniteJet

/-! Shifted profile main terms, uniformly away from the cutoff endpoint.
Both signs are covered by the same norm-bounded theorem, not continuation.
This is the unrestricted inner Mobius sum, not the gcd or Feng asymptotic. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.ShiftedMobius
open ShiftWeights WeightDerivatives WeightedMobius

def scaledSum (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (L : ℂ) * weightedSum L u (weight A u θ P)

def mainTerm (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  A * P.eval ((u/θ : ℝ) : ℂ) + P.derivative.eval ((u/θ : ℝ) : ℂ) / θ

def profileSet (C u₀ U : ℝ) : Set (ℂ × ℝ) :=
  {p | ‖p.1‖ ≤ C ∧ p.2 ∈ Set.Icc u₀ U}

theorem shifted_main_term_uniform (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U) :
    TendstoUniformlyOn (fun L p => scaledSum L p.2 θ P p.1)
      (fun p => mainTerm p.2 θ P p.1) atTop (profileSet C u₀ U) := by
  have h := weighted_family_uniform (profileSet C u₀ U) Prod.snd
    (fun p => weight p.1 p.2 θ P) (fun p => first p.1 p.2 θ P)
    (fun p => second p.1 p.2 θ P) u₀ U (firstCap P θ C U) (secondCap P θ C U)
    hu₀ hU (secondCap_nonneg P θ C U hθ hC hU.le)
    (fun p hp => hp.2)
    (fun p _ v => weight_hasDerivAt p.1 p.2 θ v P)
    (fun p _ v => first_hasDerivAt p.1 p.2 θ v P)
    (fun p _ => second_continuous p.1 p.2 θ P)
    (fun p _ => by simp [weight, hP])
    (fun p hp => first_bound p.1 p.2 θ p.2 C U P hθ hp.1 hp.2.2
      ⟨hu₀.le.trans hp.2.1, le_rfl⟩)
    (fun p hp v hv => second_bound p.1 p.2 θ v C U P hθ hp.1 hp.2.2 hv)
  simpa only [scaledSum, first_zero, mainTerm] using h

theorem twoBidiscs_norm (p : ℂ × ℂ) (hp : p ∈ ElementaryGcd.twoBidiscs) :
    ‖p.1‖ ≤ 5*PRZZAsymptotic.R/4 ∧ ‖p.2‖ ≤ 5*PRZZAsymptotic.R/4 := by
  rcases hp with hp | hp
  · have h := PRZZAsymptotic.witnessBidisc_subset hp
    exact ⟨h.1, h.2.1⟩
  · have h := PRZZAsymptotic.witnessBidisc_subset
      ((ElementaryGcd.mem_reflectedBidisc p).mp hp)
    simpa only [ElementaryGcd.reflect, norm_neg] using And.intro h.2.1 h.1

/-- Either coordinate, on the UNION of the two bidiscs, with a common cutoff. -/
theorem shifted_main_term_twoBidiscs (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ u₀ U : ℝ) (hθ : 0 < θ) (hu₀ : 0 < u₀) (hU : 0 < U) (right : Bool) :
    TendstoUniformlyOn
      (fun (L : ℝ) (p : (ℂ × ℂ) × ℝ) => scaledSum L p.2 θ P (if right then p.1.2 else p.1.1))
      (fun p => mainTerm p.2 θ P (if right then p.1.2 else p.1.1)) atTop
      {p | p.1 ∈ ElementaryGcd.twoBidiscs ∧ p.2 ∈ Set.Icc u₀ U} := by
  have h := shifted_main_term_uniform P hP θ (5*PRZZAsymptotic.R/4) u₀ U hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hu₀ hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  apply hL ⟨if right then p.1.2 else p.1.1, p.2⟩
  refine ⟨?_, hp.2⟩
  split
  · exact (twoBidiscs_norm p.1 hp.1).2
  · exact (twoBidiscs_norm p.1 hp.1).1

theorem scaledSum_entire (L u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℂ ⊤ (scaledSum L u θ P) := by
  unfold scaledSum weightedSum weight
  fun_prop

theorem mainTerm_entire (u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℂ ⊤ (mainTerm u θ P) := by unfold mainTerm; fun_prop

/-- Cauchy transfer on a larger norm ball. The positive radius margin is
explicit, and the estimate is uniform in the cutoff as well as the shift. -/
theorem shifted_derivative_uniform (n : ℕ) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C ρ u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hu₀ : 0 < u₀) (hU : 0 < U) :
    TendstoUniformlyOn (fun L p => iteratedDeriv n (scaledSum L p.2 θ P) p.1)
      (fun p => iteratedDeriv n (mainTerm p.2 θ P) p.1) atTop (profileSet C u₀ U) := by
  have h := shifted_main_term_uniform P hP θ (C+ρ) u₀ U hθ (by linarith) hu₀ hU
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps * ρ^n / (2 * n.factorial) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h _ he] with L hL
  intro p hp
  have hs := scaledSum_entire L p.2 θ P
  have hm := mainTerm_entire p.2 θ P
  have hb : ∀ z ∈ Metric.sphere p.1 ρ,
      ‖scaledSum L p.2 θ P z - mainTerm p.2 θ P z‖ ≤ eps*ρ^n/(2*n.factorial) := by
    intro z hz
    have hnorm : ‖z‖ ≤ C+ρ := by
      have hh := norm_add_le (z-p.1) p.1
      rw [sub_add_cancel, mem_sphere_iff_norm.mp hz] at hh
      linarith [hp.1]
    have hh := hL (z,p.2) ⟨hnorm,hp.2⟩
    rw [dist_comm, dist_eq_norm] at hh
    exact hh.le
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ
    ((hs.sub hm).differentiable (by simp)).diffContOnCl hb
  rw [iteratedDeriv_fun_sub (hs.contDiffAt.of_le (by simp))
    (hm.contDiffAt.of_le (by simp))] at hc
  have heq : (n.factorial : ℝ) * (eps*ρ^n/(2*n.factorial)) / ρ^n = eps/2 := by
    field_simp
  rw [heq] at hc
  rw [dist_comm, dist_eq_norm]
  exact hc.trans_lt (by linarith)

/-- The normalized jet convention already used by the finite evaluator. -/
theorem shifted_jet_uniform (n : ℕ) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C ρ u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hu₀ : 0 < u₀) (hU : 0 < U) :
    TendstoUniformlyOn (fun L p => FiniteJet.jet n (scaledSum L p.2 θ P) p.1)
      (fun p => FiniteJet.jet n (mainTerm p.2 θ P) p.1) atTop (profileSet C u₀ U) := by
  have h := shifted_derivative_uniform n P hP θ C ρ u₀ U hθ hC hρ hu₀ hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  have hh := hL p hp
  rw [dist_comm, dist_eq_norm] at hh ⊢
  simp only [FiniteJet.jet, ← sub_div, norm_div]
  have hn : (1 : ℝ) ≤ ‖(n.factorial : ℂ)‖ := by
    simpa only [Complex.norm_natCast] using (show (1 : ℝ) ≤ n.factorial by
      exact_mod_cast Nat.factorial_pos n)
  exact (div_le_self (norm_nonneg _) hn).trans_lt hh

/-- All normalized shift jets on either coordinate of BOTH bidiscs.
The radius margin may be chosen independently of the derivative order. -/
theorem shifted_jet_twoBidiscs (n : ℕ) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ ρ u₀ U : ℝ) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hu₀ : 0 < u₀) (hU : 0 < U) (right : Bool) :
    TendstoUniformlyOn
      (fun (L : ℝ) (p : (ℂ × ℂ) × ℝ) =>
        FiniteJet.jet n (scaledSum L p.2 θ P) (if right then p.1.2 else p.1.1))
      (fun p => FiniteJet.jet n (mainTerm p.2 θ P) (if right then p.1.2 else p.1.1))
      atTop {p | p.1 ∈ ElementaryGcd.twoBidiscs ∧ p.2 ∈ Set.Icc u₀ U} := by
  have h := shifted_jet_uniform n P hP θ (5*PRZZAsymptotic.R/4) ρ u₀ U hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hρ hu₀ hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  apply hL ⟨if right then p.1.2 else p.1.1, p.2⟩
  refine ⟨?_, hp.2⟩
  split
  · exact (twoBidiscs_norm p.1 hp.1).2
  · exact (twoBidiscs_norm p.1 hp.1).1

/-- Jets evaluated at the swapped reflected shifts (-B,-A). These are jets
in the evaluation variable, BEFORE applying any chain-rule reflection signs. -/
theorem shifted_jet_reflected (n : ℕ) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ ρ u₀ U : ℝ) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hu₀ : 0 < u₀) (hU : 0 < U) (right : Bool) :
    TendstoUniformlyOn
      (fun (L : ℝ) (p : (ℂ × ℂ) × ℝ) =>
        FiniteJet.jet n (scaledSum L p.2 θ P) (if right then -p.1.1 else -p.1.2))
      (fun p => FiniteJet.jet n (mainTerm p.2 θ P) (if right then -p.1.1 else -p.1.2))
      atTop {p | p.1 ∈ PRZZAsymptotic.witnessBidisc ∧ p.2 ∈ Set.Icc u₀ U} := by
  have h := shifted_jet_twoBidiscs n P hP θ ρ u₀ U hθ hρ hu₀ hU right
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  exact hL (ElementaryGcd.reflect p.1, p.2) ⟨Or.inr ⟨p.1, hp.1, rfl⟩, hp.2⟩

#print axioms shifted_jet_twoBidiscs
#print axioms shifted_jet_reflected
#print axioms scaledSum_entire
#print axioms mainTerm_entire
#print axioms shifted_derivative_uniform
#print axioms shifted_jet_uniform
#print axioms shifted_main_term_uniform
#print axioms twoBidiscs_norm
#print axioms shifted_main_term_twoBidiscs
end XiPrime8845.ShiftedMobius
