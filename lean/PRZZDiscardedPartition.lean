import PRZZPartitionMass
import PRZZDiscardedSuppliers

/-! Discarded spatial pieces are combined before the time estimate.
Zero combined coefficients are removed exactly. The partition cost is one,
not its number of pieces. This concerns the exact logarithmic phase with
sourceW; the Gamma replacement error is a separate term. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set MeasureTheory Complex
namespace XiPrime8845.PRZZDiscardedPartition
open PRZZAFEProgression
set_option maxHeartbeats 3000000

def mask (F : ℝ → ℝ) (M x : ℝ) (K : ℕ) (P : ℕ → Prop) : ℂ := by
  classical
  exact ∑ j ∈ range K, if P j then piece (fun x => (F x:ℂ)) (2^j*M) x else 0

theorem mask_norm (F : ℝ → ℝ) (hF : Antitone F)
    (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (M x : ℝ) (K : ℕ) (P : ℕ → Prop) (hM : 0 < M) (hx : 0 ≤ x) :
    ‖mask F M x K P‖ ≤ 1 := by
  classical
  unfold mask
  apply (norm_sum_le _ _).trans
  apply le_trans _ (PRZZPartitionMass.piece_mass F hF hlo hhi M x K hM hx)
  apply sum_le_sum
  intro j hj
  split_ifs <;> simp

theorem mask_witness (F : ℝ → ℝ) (M x : ℝ) (K : ℕ) (P : ℕ → Prop)
    (h : mask F M x K P ≠ 0) :
    ∃ j ∈ range K, P j ∧ piece (fun x => (F x:ℂ)) (2^j*M) x ≠ 0 := by
  classical
  by_contra hh
  push Not at hh
  apply h
  unfold mask
  apply sum_eq_zero
  intro j hj
  split_ifs with hp
  · exact hh j hj hp
  · rfl

/-- Exact finite regrouping, including zero terms, before integration. -/
theorem sum_mask {ι : Type*} (s : Finset ι) (F : ℝ → ℝ) (M : ℝ) (K : ℕ)
    (x : ι → ℝ) (P : ι → ℕ → Prop) [∀ i j, Decidable (P i j)] (f : ι → ℂ) :
    (∑ j ∈ range K, ∑ i ∈ s,
      (if P i j then piece (fun x => (F x:ℂ)) (2^j*M) (x i) else 0)*f i) =
      ∑ i ∈ s, mask F M (x i) K (P i)*f i := by
  classical
  rw [sum_comm]
  simp only [mask,sum_mul]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases h : P i j <;> simp [h]

/-- Exact substitution in the original disjoint gcd/gap/dyadic fibres,
under the time integral. Zero spatial coefficients disappear without a
support hypothesis on them. No interchange of infinite sums is used. -/
theorem grouped_time_identity (L N K : ℕ) (P : ℝ → ℝ) (M : ℝ)
    (keep : PRZZAFEIndices.Index → ℕ → Prop) [∀ i j, Decidable (keep i j)]
    (f : PRZZAFEIndices.Index → ℝ → ℂ) :
    (∫ t : ℝ, ∑ j ∈ range K, ∑ z ∈ PRZZAFEIndices.labels L N,
      ∑ i ∈ PRZZAFEIndices.fibre L N z,
        (if keep i j then piece (fun x => (P x:ℂ)) (2^j*M) i.1.1 else 0)*f i t) =
      ∫ t : ℝ, ∑ i ∈ (PRZZAFEIndices.indices L N).filter
        (fun i => mask P M i.1.1 K (keep i) ≠ 0),
          mask P M i.1.1 K (keep i)*f i t := by
  classical
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp_rw [← PRZZAFEIndices.grouped, sum_mask]
  rw [sum_filter]
  apply sum_congr rfl
  intro i hi
  by_cases h : mask P M i.1.1 K (keep i) = 0 <;> simp [h]

/-- The original support and a nonzero combined piece supply the entire
discarded-gap geometry, even when the other product is much larger. -/
theorem mask_geometry (F : ℝ → ℝ) (G : ℝ → ℂ)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (T M Q d m u y eps : ℝ) (K : ℕ)
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q)) (hg : G (d*u) ≠ 0)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hu : 0 < u) (hy : 0 < y) (hheight : 1 ≤ T^(1-eps))
    (hm : mask F M m K (fun j =>
      PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤ |y-m*u|) ≠ 0) :
    0 < |y-m*u| ∧ max (m*u) y/|y-m*u| ≤ 10*T^(1-eps) := by
  obtain ⟨j,hj,hgap,hpiece⟩ := mask_witness F M m K _ hm
  have hs := piece_support (fun x => (F x:ℂ)) (2^j*M) (by positivity)
    (by intro x hx; simp [hleft x hx]) (by intro x hx; simp [hright x hx])
  apply PRZZDiscardedSuppliers.cutoff_geometry _ G T (2^j*M) Q d m u y eps
    _ hG hpiece hg hT (by positivity) hQ hd hu hy hheight hgap
  intro x hx
  exact ⟨(hs hx).1, (hs hx).2.trans (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j])⟩

/-- Apply the integrated product estimate to precisely the nonzero
combined coefficients. No geometry is demanded of a zero row. -/
theorem masked_time_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ H : ℕ → ℝ, (∀ n, 0 ≤ H n) ∧
      ∀ (n : ℕ) (alpha beta : ℂ) (T C eps J : ℝ),
      r ≤ ‖alpha+beta‖ → 1 < T → 0 ≤ C → 0 ≤ J →
      ∀ (s : Finset (ℕ × ℕ)) (c w : ℕ × ℕ → ℂ) (x y : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ J) → (∀ p ∈ s, ‖w p‖ ≤ 1) →
      (∀ p ∈ s, c p*w p ≠ 0 → 0 < x p ∧ 0 < y p ∧
        0 < |y p-x p| ∧ max (x p) (y p)/|y p-x p| ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, (c p*w p)*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
          ((alpha+beta)/(Real.log T:ℂ)) t)‖ ≤
        J*H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps) := by
  classical
  obtain ⟨H,hH,hh⟩ := PRZZDiscardedSuppliers.scaled_summed F hF hsF hsupp r hr
  refine ⟨H,hH,?_⟩
  intro n alpha beta T C eps J hsep hT hC hJ s c w x y hc hw hg
  let active := s.filter (fun p => c p*w p ≠ 0)
  have he (t : ℝ) : (∑ p ∈ s, (c p*w p)*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
      PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
        ((alpha+beta)/(Real.log T:ℂ)) t)) =
      ∑ p ∈ active, (c p*w p)*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
      PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
        ((alpha+beta)/(Real.log T:ℂ)) t) := by
    simp only [active,sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases h : c p*w p = 0 <;> simp [h]
  simp_rw [he]
  apply hh n alpha beta T C eps J hsep hT hC hJ active (fun p => c p*w p)
    x y (fun p => max (x p) (y p)) (fun p => |y p-x p|)
  · intro p hp
    have hp' := (mem_filter.mp hp).1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hw p hp') (norm_nonneg _)).trans
      (by simpa using hc p hp')
  · intro p hp
    obtain ⟨hp',hn⟩ := mem_filter.mp hp
    obtain ⟨hx,hy,hd,hb⟩ := hg p hp' hn
    exact ⟨hx,hy,le_max_left _ _,le_max_right _ _,hd,le_rfl,hb⟩

/-- Substitution for every spatial piece and every finite product mask.
The original spatial and arithmetic supports supply the gap conditions;
the time cutoff is already inside the integral. H is independent of the
number of pieces, product truncation, shifts, and all spatial scales. -/
theorem partition_time_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ H : ℕ → ℝ, (∀ n, 0 ≤ H n) ∧
      ∀ (n K : ℕ) (alpha beta : ℂ) (T M Q d u v eps J : ℝ)
      (G : ℝ → ℂ) (P : ℝ → ℝ),
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      Function.support G ⊆ Icc (Q/2) (3*Q) → G (d*u) ≠ 0 →
      r ≤ ‖alpha+beta‖ → 1 < T → 0 < M → 0 < Q → 0 < d →
      0 < u → 0 < v → 1 ≤ T^(1-eps) → 0 ≤ J →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, ‖c p‖ ≤ J) →
      ‖∫ t : ℝ, ∑ j ∈ range K, ∑ p ∈ s,
        (if PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤
          |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u|
        then piece (fun x => (P x:ℂ)) (2^j*M) ((p.1:ℝ)+1) else 0)*
        (c p*(exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
          ((alpha+beta)/(Real.log T:ℂ)) t))‖ ≤
        J*H n*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps) := by
  classical
  obtain ⟨H,hH,hh⟩ := masked_time_bound F hF hsF hsupp r hr
  refine ⟨H,hH,?_⟩
  intro n K alpha beta T M Q d u v eps J G P hP hlo hhi hleft hright
    hG hg hsep hT hM hQ hd hu hv hheight hJ s c hc
  simp_rw [sum_mask]
  apply le_of_eq_of_le _ (hh n alpha beta T 10 eps J hsep hT (by norm_num) hJ s c
    (fun p => mask P M ((p.1:ℝ)+1) K (fun j =>
      PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤
        |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u|))
    (fun p => ((p.1:ℝ)+1)*u) (fun p => ((p.2:ℝ)+1)*v) hc ?_ ?_)
  · simp only [mul_assoc, mul_left_comm]
  · intro p hp
    exact mask_norm P hP hlo hhi M _ K _ hM (by positivity)
  · intro p hp hn
    have hm := (mul_ne_zero_iff.mp hn).2
    have hgeom := mask_geometry P G hleft hright T M Q d ((p.1:ℝ)+1) u
      (((p.2:ℝ)+1)*v) eps K hG hg (by linarith) hM hQ hd hu
      (by positivity) hheight hm
    exact ⟨by positivity,by positivity,hgeom⟩

#print axioms partition_time_bound
#print axioms grouped_time_identity
#print axioms mask_norm
#print axioms mask_witness
#print axioms sum_mask
#print axioms mask_geometry
#print axioms masked_time_bound
end XiPrime8845.PRZZDiscardedPartition
