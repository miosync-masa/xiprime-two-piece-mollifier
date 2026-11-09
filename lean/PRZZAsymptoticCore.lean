import PRZZInterface
import KernelAlgebra

/-! Uniform normalized PRZZ error for the fixed witness.
This module does not evaluate the literal gcd sum by Euler poles or Mellin inversion.
This core contains definitions and elementary estimates only. -/
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


#print axioms errorEnvelope_tendsto
#print axioms radius_pos
#print axioms witnessBidisc_subset
#print axioms witnessBidisc_sum_ne_zero
#print axioms mixed_cauchy_bound
end XiPrime8845.PRZZAsymptotic
