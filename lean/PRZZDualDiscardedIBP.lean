import PRZZDualTimeIBP
import PRZZValuedSourceDiscarded

/-! The genuine dual Gamma-weighted discarded source row, including
the reflected coefficient and both cutoff VALUES. Source geometry is
supplied from the actual support selector. The remaining derivative
mass is computed from the true Gamma/sourceW product, not a hypothesis. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZDualDiscardedIBP
open PRZZDiscardedOuter PRZZMellinSeparation PRZZDualTimeIBP
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def coefficient (G H : ℝ → ℂ) (js : List ℕ) (Q V d : ℝ)
    (a b : ℂ) (u v : ℕ) (p : ℕ × ℕ) : ℂ :=
  PRZZActualLocalReplacement.coefficient
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (-b) (-a) 0 ((p.1+1,p.2+1),(u,v))*
      (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))

def integrand (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) (t : ℝ) : ℂ :=
  ∑ p ∈ s,
    (coefficient G H js Q V d a b u v p*
      sourceMask P (scaledCutoff G Q) K T M Q d eps u v p)*
      (exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))*
        weight F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) t)

def value (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) : ℂ :=
  ∫ t : ℝ, integrand F G H P js K u v T M Q V d eps a b s t

theorem value_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) :
    value F G H P js K u v T M Q V d eps a b s =
      ∫ t : ℝ, PRZZAFEDual.dualMultiplier a b t*
        row F T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (-b) (-a) (-(a+b)) u v s
          (fun p => (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))*
            sourceMask P (scaledCutoff G Q) K T M Q d eps u v p) t := by
  unfold value integrand row
  apply integral_congr_ae
  apply Filter.Eventually.of_forall; intro t
  dsimp only
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro p hp
  unfold coefficient weight
  ring

/-- The literal source row after arbitrary n integrations by parts.
No Geometry, Gamma derivative cap, or generic hB premise is supplied.
The explicit jetMass must still be bounded uniformly in height before
this can be called an optimized dual discarded-error theorem. -/
theorem source_ibp (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hm : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K u v n : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ))
    (hT : 1 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d) (he : eps ≤ 1)
    (hu : u ∈ Finset.Icc 1 N) (hv : v ∈ Finset.Icc 1 N)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    ‖value F G H P js K u v T M Q V d eps a b s‖ ≤
      ∑ p ∈ s, ‖coefficient G H js Q V d a b u v p*
        sourceMask P (scaledCutoff G Q) K T M Q d eps u v p‖*
        jetMass F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) n*
          (10*T^(1-eps))^n := by
  let w := sourceMask P (scaledCutoff G Q) K T M Q d eps u v
  let c := fun p => coefficient G H js Q V d a b u v p*w p
  let f := fun p : ℕ × ℕ => weight F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b))
  let x := fun p : ℕ × ℕ => ((p.1:ℝ)+1)*u
  let y := fun p : ℕ × ℕ => ((p.2:ℝ)+1)*v
  let s' := s.filter (fun p => w p ≠ 0)
  have hT0 : 0 < T := by linarith
  have hs' : -(a+b) ≠ 0 := neg_ne_zero.mpr hs
  have hg := source_geometry P (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    hT0 hM hQ hd (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) (fun _ _ => s)
  have hgeom (p : ℕ × ℕ) (hp : p ∈ s') :
      0 < |y p-x p| ∧ max (x p) (y p)/|y p-x p| ≤ 10*T^(1-eps) :=
    hg.2 u hu v hv p (mem_filter.mp hp).1 (mem_filter.mp hp).2
  have hxy (p : ℕ × ℕ) : 0 < x p ∧ 0 < y p := by
    have hu0 : (0:ℝ) < u := by exact_mod_cast (Finset.mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
    dsimp [x,y]; constructor <;> positivity
  have hsm (p : ℕ × ℕ) : ContDiff ℝ ∞ (f p) :=
    smooth F hF hsF T _ a b (-(a+b)) hT0 (by positivity) ha hb hs'
  have hcp (p : ℕ × ℕ) : HasCompactSupport (f p) := compact F hsF T _ a b (-(a+b)) hT0
  have heq : value F G H P js K u v T M Q V d eps a b s =
      ∫ t : ℝ, ∑ p ∈ s', c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*f p t) := by
    unfold value integrand
    apply integral_congr_ae
    apply Filter.Eventually.of_forall; intro t
    dsimp [s']
    rw [sum_filter]
    apply sum_congr rfl; intro p hp
    by_cases hw : w p = 0
    · simp [hw,w]
    · simp only [if_pos hw]
      rfl
  rw [heq]
  have hi := PRZZDeltaDecay.finite_discarded s' c f (fun p _ => hsm p) (fun p _ => hcp p) n
    x y (fun p => max (x p) (y p)) (fun p => |y p-x p|)
    (fun p _ => (hxy p).1) (fun p _ => (hxy p).2)
    (fun p _ => le_max_left _ _) (fun p _ => le_max_right _ _)
    (fun p hp => (hgeom p hp).1) (fun p _ => le_rfl)
  apply hi.trans
  calc
    _ ≤ ∑ p ∈ s', ‖c p‖*jetMass F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) n*
        (10*T^(1-eps))^n := by
      apply sum_le_sum; intro p hp
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (leibniz_mass F hF hsF T _ a b (-(a+b)) hT0 (by positivity) ha hb hs' n) (norm_nonneg _)
      · exact pow_le_pow_left₀ (by positivity) (hgeom p hp).2 n
      · positivity
      · unfold jetMass; positivity
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp hnot
      unfold jetMass
      positivity

theorem integrand_integrable (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (K u v : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ))
    (hT : 0 < T) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    Integrable (integrand F G H P js K u v T M Q V d eps a b s) := by
  unfold integrand
  apply integrable_finsetSum; intro p hp
  apply Continuous.integrable_of_hasCompactSupport
  · have hh := (smooth F hF hsF T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b))
      hT (by positivity) ha hb (neg_ne_zero.mpr hs)).continuous
    fun_prop
  · exact ((compact F hsF T _ a b (-(a+b)) hT).mul_left).mul_left

def outerValue (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (N K : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ)) : ℂ :=
  ∫ t : ℝ, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    integrand F G H P js K u v T M Q V d eps a b (s u v) t

theorem outer_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (N K : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (hT : 0 < T) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    outerValue F G H P js N K T M Q V d eps a b s =
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        value F G H P js K u v T M Q V d eps a b (s u v) := by
  unfold outerValue value
  rw [integral_finsetSum]
  · apply sum_congr rfl; intro u hu
    exact integral_finsetSum _ (fun v _ => integrand_integrable F G H P js hF hsF
      K u v T M Q V d eps a b (s u v) hT ha hb hs)
  · intro u hu
    exact integrable_finsetSum _ (fun v _ => integrand_integrable F G H P js hF hsF
      K u v T M Q V d eps a b (s u v) hT ha hb hs)

theorem source_outer_ibp (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hm : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K n : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (hT : 1 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d) (he : eps ≤ 1)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    ‖outerValue F G H P js N K T M Q V d eps a b s‖ ≤
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, ∑ p ∈ s u v,
        ‖coefficient G H js Q V d a b u v p*
          sourceMask P (scaledCutoff G Q) K T M Q d eps u v p‖*
          jetMass F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) n*
            (10*T^(1-eps))^n := by
  rw [outer_eq F G H P js hF hsF N K T M Q V d eps a b s (by linarith) ha hb hs]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  exact source_ibp F G H P js hF hsF hsG hm hlo hhi hleft hright N K u v n
    T M Q V d eps a b (s u v) hT hM hQ hd he hu hv ha hb hs

#print axioms integrand_integrable
#print axioms outer_eq
#print axioms source_outer_ibp
#print axioms value_eq
#print axioms source_ibp
end XiPrime8845.PRZZDualDiscardedIBP
