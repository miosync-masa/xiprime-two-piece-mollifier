import PRZZInterface
import KernelAlgebra

/-! Uniform normalized PRZZ error for the fixed witness.
This module does not evaluate the literal gcd sum by Euler poles or Mellin inversion.
The only external analytic input is the explicitly named PRZZ profile axiom. -/
noncomputable section
open Filter Topology

namespace XiPrime8845.PRZZAsymptotic
open PRZZ

def theta : ℝ := 4/7 - 1/1000000
def R : ℝ := (XiPrime8845.radiusParameter : ℝ)

def shiftSet (bound gap : ℝ) : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ ≤ bound ∧ ‖p.2‖ ≤ bound ∧ gap ≤ ‖p.1+p.2‖}

def normalizedMoment (Phi : ℝ → ℝ) (T : ℝ) (p : ℂ × ℂ) : ℂ :=
  twistedMoment witness witness theta T Phi p.1 p.2 / (T : ℂ)

def normalizedGcd (Phi : ℝ → ℝ) (T : ℝ) (p : ℂ × ℂ) : ℂ :=
  gcdMainTerm witness witness theta T Phi p.1 p.2 / (T : ℂ)

def errorEnvelope (T : ℝ) : ℝ :=
  Real.rpow T (7/16000000) *
    (Real.rpow (length theta T) (7/4) +
      Real.rpow (length theta T) (7/8) * Real.rpow T (1/2)) / T

theorem errorEnvelope_tendsto : Tendsto errorEnvelope atTop (nhds 0) :=
  witness_normalized_error_tendsto_zero

/-- The bound is simultaneous in both shifts, with C and T0 independent of them. -/
theorem normalized_difference_bound (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (bound gap : ℝ) (hb : 0 < bound) (hg : 0 < gap) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T, T0 ≤ T →
      ∀ p ∈ shiftSet bound gap,
        ‖normalizedMoment Phi T p - normalizedGcd Phi T p‖ ≤ C * errorEnvelope T := by
  obtain ⟨C, T0, hC, hT0, h⟩ := witness_przz_estimate Phi hPhi bound gap hb hg
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT p hp
  have hpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have he := div_le_div_of_nonneg_right
    (h T hT p.1 p.2 hp.1 hp.2.1 hp.2.2) hpos.le
  simpa only [normalizedMoment, normalizedGcd, ← sub_div, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, errorEnvelope, theta,
    mul_div_assoc, mul_assoc] using he

theorem normalized_difference_uniform (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (bound gap : ℝ) (hb : 0 < bound) (hg : 0 < gap) :
    TendstoUniformlyOn
      (fun T p => normalizedMoment Phi T p - normalizedGcd Phi T p)
      (fun _ => 0) atTop (shiftSet bound gap) := by
  obtain ⟨C, T0, hC, hT0, h⟩ := normalized_difference_bound Phi hPhi bound gap hb hg
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hlim : Tendsto (fun T => C * errorEnvelope T) atTop (nhds 0) := by
    simpa using errorEnvelope_tendsto.const_mul C
  filter_upwards [eventually_ge_atTop T0, hlim.eventually (gt_mem_nhds heps)] with T hT hsmall
  intro p hp
  simpa only [dist_zero_left] using (h T hT p hp).trans_lt hsmall

/-- A closed bidisc with an explicit gap, suitable for later Cauchy estimates. -/
def witnessBidisc : Set (ℂ × ℂ) :=
  {p | ‖p.1 + (R : ℂ)‖ ≤ R/4 ∧ ‖p.2 + (R : ℂ)‖ ≤ R/4}

theorem radius_pos : 0 < R := by norm_num [R, XiPrime8845.radiusParameter]

theorem witnessBidisc_subset : witnessBidisc ⊆ shiftSet (5*R/4) (3*R/2) := by
  intro p hp
  have hr : ‖(R : ℂ)‖ = R := by simp [abs_of_pos radius_pos]
  have hnorm (z : ℂ) (hz : ‖z+(R:ℂ)‖ ≤ R/4) : ‖z‖ ≤ 5*R/4 := by
    have h := norm_sub_le (z+(R:ℂ)) (R:ℂ)
    rw [add_sub_cancel_right, hr] at h
    linarith
  refine ⟨hnorm p.1 hp.1, hnorm p.2 hp.2, ?_⟩
  have h := norm_sub_le ((p.1+(R:ℂ))+(p.2+(R:ℂ))) (p.1+p.2)
  have he : (p.1+(R:ℂ))+(p.2+(R:ℂ))-(p.1+p.2) = (2:ℂ)*R := by ring
  rw [he, norm_mul, hr] at h
  have htri := norm_add_le (p.1+(R:ℂ)) (p.2+(R:ℂ))
  norm_num at h
  linarith [hp.1, hp.2]

theorem witnessBidisc_sum_ne_zero (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    p.1+p.2 ≠ 0 := by
  have h := (witnessBidisc_subset hp).2.2
  intro hz
  rw [hz, norm_zero] at h
  linarith [radius_pos]

theorem normalized_difference_on_bidisc (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T p => normalizedMoment Phi T p - normalizedGcd Phi T p)
      (fun _ => 0) atTop witnessBidisc :=
  (normalized_difference_uniform Phi hPhi (5*R/4) (3*R/2)
    (by have hR := radius_pos; positivity) (by have hR := radius_pos; positivity)).mono
      witnessBidisc_subset

/-- Transfer a separately PROVED gcd-sum limit. The hypothesis is deliberately
visible; this theorem is not a leading-pole evaluation. -/
theorem moment_limit_of_gcd_limit (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) (L : ℂ)
    (hmain : Tendsto (fun T => normalizedGcd Phi T p) atTop (nhds L)) :
    Tendsto (fun T => normalizedMoment Phi T p) atTop (nhds L) := by
  have h := ((normalized_difference_on_bidisc Phi hPhi).tendsto_at hp).add hmain
  simpa only [sub_add_cancel, zero_add] using h

/-- Uniform version of the transfer; all evaluation of the arithmetic main
term is confined to the explicit hmain premise. -/
theorem moment_uniform_limit_of_gcd_limit (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (L : ℂ × ℂ → ℂ)
    (hmain : TendstoUniformlyOn (normalizedGcd Phi) L atTop witnessBidisc) :
    TendstoUniformlyOn (normalizedMoment Phi) L atTop witnessBidisc := by
  have h := (normalized_difference_on_bidisc Phi hPhi).add hmain
  simpa only [Pi.add_def, sub_add_cancel, zero_add] using h

/-- Two successive Cauchy estimates. Both slice regularity hypotheses are
explicit; a uniform bound alone never justifies differentiation. -/
theorem mixed_cauchy_bound (f : ℂ → ℂ → ℂ) (c : ℂ) (r C : ℝ) (a b : ℕ)
    (hr : 0 < r)
    (hy : ∀ x ∈ Metric.sphere c r, DiffContOnCl ℂ (f x) (Metric.ball c r))
    (hx : DiffContOnCl ℂ (fun x => iteratedDeriv b (f x) c) (Metric.ball c r))
    (hbound : ∀ x ∈ Metric.sphere c r, ∀ y ∈ Metric.sphere c r, ‖f x y‖ ≤ C) :
    ‖iteratedDeriv a (fun x => iteratedDeriv b (f x) c) c‖ ≤
      (a.factorial : ℝ) * b.factorial * C / r^(a+b) := by
  calc
    _ ≤ (a.factorial : ℝ) * ((b.factorial : ℝ) * C / r^b) / r^a := by
      apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le a hr hx
      intro x hxs
      exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le b hr
        (hy x hxs) (hbound x hxs)
    _ = _ := by rw [pow_add]; ring

def normalizedError (Phi : ℝ → ℝ) (T : ℝ) (x y : ℂ) : ℂ :=
  normalizedMoment Phi T (x,y) - normalizedGcd Phi T (x,y)

/-- Conditional Cauchy transfer for the actual PRZZ residual, at arbitrary
finite mixed order (in particular 0..6 on each side). The two holomorphic
slice premises are explicit here and discharged for the actual arithmetic
functions in ArithmeticRegularity. This generic transfer does not identify
derivatives of a moment integral with explicit zeta-derivative moments. -/
theorem normalized_mixed_error_tendsto (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (a b : ℕ)
    (hy : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Metric.sphere (-(R:ℂ)) (R/4),
      DiffContOnCl ℂ (normalizedError Phi T x) (Metric.ball (-(R:ℂ)) (R/4)))
    (hx : ∀ᶠ T : ℝ in atTop,
      DiffContOnCl ℂ (fun x => iteratedDeriv b (normalizedError Phi T x) (-R))
        (Metric.ball (-(R:ℂ)) (R/4))) :
    Tendsto (fun T : ℝ =>
      iteratedDeriv a (fun x => iteratedDeriv b (normalizedError Phi T x) (-R)) (-R))
      atTop (nhds 0) := by
  have hr : 0 < R/4 := by have hR := radius_pos; positivity
  obtain ⟨C, T0, hC, hT0, h⟩ := normalized_difference_bound Phi hPhi (5*R/4) (3*R/2)
    (by have hR := radius_pos; positivity) (by have hR := radius_pos; positivity)
  have hlim : Tendsto (fun T =>
      ((a.factorial : ℝ) * b.factorial * C / (R/4)^(a+b)) * errorEnvelope T)
      atTop (nhds 0) := by
    simpa using errorEnvelope_tendsto.const_mul
      ((a.factorial : ℝ) * b.factorial * C / (R/4)^(a+b))
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hy, hx, eventually_ge_atTop T0] with T hyT hxT hT
  calc
    _ ≤ (a.factorial : ℝ) * b.factorial * (C * errorEnvelope T) / (R/4)^(a+b) := by
      apply mixed_cauchy_bound _ (-(R:ℂ)) (R/4) _ a b hr hyT hxT
      intro x hxs y hys
      have hp : (x,y) ∈ witnessBidisc := by
        constructor
        · simpa only [dist_eq_norm, sub_neg_eq_add] using (Metric.mem_sphere.mp hxs).le
        · simpa only [dist_eq_norm, sub_neg_eq_add] using (Metric.mem_sphere.mp hys).le
      exact h T hT (x,y) (witnessBidisc_subset hp)
    _ = _ := by ring

#print axioms errorEnvelope_tendsto
#print axioms normalized_difference_bound
#print axioms normalized_difference_uniform
#print axioms radius_pos
#print axioms witnessBidisc_subset
#print axioms witnessBidisc_sum_ne_zero
#print axioms normalized_difference_on_bidisc
#print axioms moment_limit_of_gcd_limit
#print axioms moment_uniform_limit_of_gcd_limit
#print axioms mixed_cauchy_bound
#print axioms normalized_mixed_error_tendsto
end XiPrime8845.PRZZAsymptotic
