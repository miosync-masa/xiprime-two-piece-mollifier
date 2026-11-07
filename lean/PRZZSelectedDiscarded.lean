import PRZZDualDiscardedBudget

/-! Source discarded IBP with an arbitrary spatial selector, including
strict small M. The selector is combined in the partition BEFORE norms.
Both actual cutoff values and the genuine dual Gamma jets are retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZSelectedDiscarded
open PRZZDiscardedOuter PRZZMellinSeparation PRZZDualTimeIBP PRZZDualDiscardedBudget
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

def sourceMask (P : ℝ → ℝ) (R : ℕ → Prop) (G : ℝ → ℂ) (K : ℕ)
    (T M Q d eps : ℝ) (u v : ℕ) (p : ℕ × ℕ) : ℂ :=
  if G (d*u) = 0 then 0 else
    PRZZDiscardedPartition.mask P M ((p.1:ℝ)+1) K (fun j =>
      R j ∧ PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤
        |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u|)

theorem mask_geometry (P : ℝ → ℝ) (R : ℕ → Prop) (G : ℝ → ℂ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T M Q d m u y eps : ℝ) (K : ℕ)
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q)) (hg : G (d*u) ≠ 0)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hu : 0 < u) (hy : 0 < y) (hheight : 1 ≤ T^(1-eps))
    (hm : PRZZDiscardedPartition.mask P M m K (fun j =>
      R j ∧ PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤ |y-m*u|) ≠ 0) :
    0 < |y-m*u| ∧ max (m*u) y/|y-m*u| ≤ 10*T^(1-eps) := by
  obtain ⟨j,hj,hsel,hpiece⟩ := PRZZDiscardedPartition.mask_witness P M m K _ hm
  have hs := PRZZAFEProgression.piece_support (fun x => (P x:ℂ)) (2^j*M) (by positivity)
    (by intro x hx; simp [hleft x hx]) (by intro x hx; simp [hright x hx])
  apply PRZZDiscardedSuppliers.cutoff_geometry _ G T (2^j*M) Q d m u y eps
    _ hG hpiece hg hT (by positivity) hQ hd hu hy hheight hsel.2
  intro x hx
  exact ⟨(hs hx).1,(hs hx).2.trans (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j])⟩

theorem source_geometry (P : ℝ → ℝ) (R : ℕ → Prop) (G : ℝ → ℂ)
    (hP : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K : ℕ) (T M Q d eps : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 < Q) (hd : 0 < d) (hheight : 1 ≤ T^(1-eps))
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q))
    (s : ℕ → ℕ → Finset (ℕ × ℕ)) :
    Geometry N T eps s (sourceMask P R G K T M Q d eps) := by
  constructor
  · intro u hu v hv p hp
    unfold sourceMask
    split_ifs
    · simp
    · exact PRZZDiscardedPartition.mask_norm P hP hlo hhi M _ K _ hM (by positivity)
  · intro u hu v hv p hp hn
    have hgu : G (d*u) ≠ 0 := by intro hz; exact hn (by simp [sourceMask,hz])
    have hm := hn
    simp only [sourceMask,if_neg hgu] at hm
    have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    exact mask_geometry P R G hleft hright T M Q d ((p.1:ℝ)+1) u
      (((p.2:ℝ)+1)*v) eps K hG hgu hT hM hQ hd hu0 (by positivity) hheight hm

def coefficient (G H : ℝ → ℂ) (js : List ℕ) (Q V d : ℝ)
    (a b : ℂ) (u v : ℕ) (p : ℕ × ℕ) : ℂ :=
  PRZZActualLocalReplacement.coefficient
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (-b) (-a) 0 ((p.1+1,p.2+1),(u,v))*
      (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))

def integrand (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) (t : ℝ) : ℂ :=
  ∑ p ∈ s,
    (coefficient G H js Q V d a b u v p*
      sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p)*
      (exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))*
        weight F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) t)

def value (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) : ℂ :=
  ∫ t : ℝ, integrand F G H P R js K u v T M Q V d eps a b s t

theorem value_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (K u v : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ)) :
    value F G H P R js K u v T M Q V d eps a b s =
      ∫ t : ℝ, PRZZAFEDual.dualMultiplier a b t*
        row F T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (-b) (-a) (-(a+b)) u v s
          (fun p => (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))*
            sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p) t := by
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
theorem source_ibp (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hm : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K u v n : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ))
    (hT : 1 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d) (he : eps ≤ 1)
    (hu : u ∈ Finset.Icc 1 N) (hv : v ∈ Finset.Icc 1 N)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    ‖value F G H P R js K u v T M Q V d eps a b s‖ ≤
      ∑ p ∈ s, ‖coefficient G H js Q V d a b u v p*
        sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p‖*
        jetMass F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) n*
          (10*T^(1-eps))^n := by
  let w := sourceMask P R (scaledCutoff G Q) K T M Q d eps u v
  let c := fun p => coefficient G H js Q V d a b u v p*w p
  let f := fun p : ℕ × ℕ => weight F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b))
  let x := fun p : ℕ × ℕ => ((p.1:ℝ)+1)*u
  let y := fun p : ℕ × ℕ => ((p.2:ℝ)+1)*v
  let s' := s.filter (fun p => w p ≠ 0)
  have hT0 : 0 < T := by linarith
  have hs' : -(a+b) ≠ 0 := neg_ne_zero.mpr hs
  have hg := source_geometry P R (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
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
  have heq : value F G H P R js K u v T M Q V d eps a b s =
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

theorem integrand_integrable (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (K u v : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : Finset (ℕ × ℕ))
    (hT : 0 < T) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    Integrable (integrand F G H P R js K u v T M Q V d eps a b s) := by
  unfold integrand
  apply integrable_finsetSum; intro p hp
  apply Continuous.integrable_of_hasCompactSupport
  · have hh := (smooth F hF hsF T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b))
      hT (by positivity) ha hb (neg_ne_zero.mpr hs)).continuous
    fun_prop
  · exact ((compact F hsF T _ a b (-(a+b)) hT).mul_left).mul_left

def outerValue (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (N K : ℕ)
    (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ)) : ℂ :=
  ∫ t : ℝ, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    integrand F G H P R js K u v T M Q V d eps a b (s u v) t

theorem outer_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (N K : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (hT : 0 < T) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    outerValue F G H P R js N K T M Q V d eps a b s =
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        value F G H P R js K u v T M Q V d eps a b (s u v) := by
  unfold outerValue value
  rw [integral_finsetSum]
  · apply sum_congr rfl; intro u hu
    exact integral_finsetSum _ (fun v _ => integrand_integrable F G H P R js hF hsF
      K u v T M Q V d eps a b (s u v) hT ha hb hs)
  · intro u hu
    exact integrable_finsetSum _ (fun v _ => integrand_integrable F G H P R js hF hsF
      K u v T M Q V d eps a b (s u v) hT ha hb hs)

theorem source_outer_ibp (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hm : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K n : ℕ) (T M Q V d eps : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (hT : 1 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d) (he : eps ≤ 1)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    ‖outerValue F G H P R js N K T M Q V d eps a b s‖ ≤
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, ∑ p ∈ s u v,
        ‖coefficient G H js Q V d a b u v p*
          sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p‖*
          jetMass F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) a b (-(a+b)) n*
            (10*T^(1-eps))^n := by
  rw [outer_eq F G H P R js hF hsF N K T M Q V d eps a b s (by linarith) ha hb hs]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  exact source_ibp F G H P R js hF hsF hsG hm hlo hhi hleft hright N K u v n
    T M Q V d eps a b (s u v) hT hM hQ hd he hu hv ha hb hs

theorem dual_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖outerValue F G H P R js N K T M Q V d eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) s‖ ≤ C*T^(-power) := by
  classical
  obtain ⟨U,hU,hcut⟩ := PRZZValuedCutoffs.cutoff_pair_uniform G H hG hH hcG hcH
  obtain ⟨J,hJ,hmass⟩ := shifted_mass F hF hcF hsF S r hS hr
  obtain ⟨n,D,hD,habs⟩ := outer_budget_absorbed js eps power r he hr
  let Z := ∑' p, PRZZSourceBoundaryDecay.majorant p
  have hz (p : ℕ × ℕ) : 0 ≤ PRZZSourceBoundaryDecay.majorant p := by
    unfold PRZZSourceBoundaryDecay.majorant; positivity
  have hZ : 0 ≤ Z := tsum_nonneg hz
  have hZsum (t : Finset (ℕ × ℕ)) : ∑ p ∈ t, PRZZSourceBoundaryDecay.majorant p ≤ Z :=
    PRZZSourceBoundaryDecay.majorant_summable.sum_le_tsum t (fun p _ =>
      hz p)
  refine ⟨(U*Z*J n)*10^n*D+1,by have := hJ n; positivity,?_⟩
  filter_upwards [hmass,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with T hmass hsmall hlarge
  have hT : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hlarge
  have hlog : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using hh
  intro N K M Q V d A B P R s hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  have ha : ‖a‖ ≤ 1/4 := hsmall.2 A hA
  have hb : ‖b‖ ≤ 1/4 := hsmall.2 B hB
  have hs : a+b ≠ 0 := by
    dsimp [a,b]; rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  have hg := source_geometry P R (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    (by linarith) hM hQ hd (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) s
  have hi := source_outer_ibp F G H P R js hF hsF hsG hm hlo hhi hleft hright
    N K n T M Q V d eps a b s hT hM hQ hd he1 ha hb hs
  let w := sourceMask P R (scaledCutoff G Q) K T M Q d eps
  let E := J n*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps)
  have hE : 0 ≤ E := by dsimp [E]; have := hJ n; positivity
  have hbnd : ‖outerValue F G H P R js N K T M Q V d eps a b s‖ ≤
      ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*(U*Z)*E := by
    apply hi.trans
    calc
      _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          (‖coefficient G H js Q V d a b u v p*w u v p‖*
            (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ))*E := by
        apply sum_le_sum; intro u hu
        apply sum_le_sum; intro v hv
        apply sum_le_sum; intro p hp
        have hh := hmass A B hA hB hsep n (((p.1:ℝ)+1)*((p.2:ℝ)+1)) eps (by positivity)
        rw [add_div] at hh
        have hh' := mul_le_mul_of_nonneg_left hh
          (norm_nonneg (coefficient G H js Q V d a b u v p*w u v p))
        convert hh' using 1 <;> dsimp only [a,b,w,E] <;> ring
      _ = (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          ‖coefficient G H js Q V d a b u v p*w u v p‖*
            (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ))*E := by simp only [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (finite_mass G H js U Z hU hZ hcut N Q V d a b s w hN ha hb hg.1 hZsum) hE
  have hh := habs N T (U*Z*J n) 10 hN hNT hlog (by have := hJ n; positivity) (by norm_num)
  apply hbnd.trans
  calc
    _ = ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*
        ((U*Z*J n)*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps)) := by dsimp [E]; ring
    _ ≤ _ := hh.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by linarith) _))


def directError (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (N K : ℕ)
    (T M Q V d eps : ℝ) (A B : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ)) : ℂ :=
  tailError F js N T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    ((A+B)/(Real.log T:ℂ)) s (fun u v p =>
      (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))*
        sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p)

theorem direct_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hr : 0 < r) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖directError F G H P R js N K T M Q V d eps A B s‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := PRZZValuedCutoffs.valued_negligible F G H hF hcF hsF
    hG hH hcG hcH js eps power r he hr
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with T hsmall hlarge
  have hT : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hlarge
  have hlog : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using hh
  intro N K M Q V d A B P R s hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  have ha := (Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA)
  have hb := (Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB)
  have hg := source_geometry P R (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    (by linarith) hM hQ hd
    (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) s
  exact h N A B _ _ T Q V d hN hNT hT hlog hsep
    (by linarith [(abs_le.mp ha).1]) (by linarith [(abs_le.mp hb).1]) s _ hg

#print axioms direct_negligible
#print axioms mask_geometry
#print axioms source_geometry
#print axioms value_eq
#print axioms source_ibp
#print axioms integrand_integrable
#print axioms outer_eq
#print axioms source_outer_ibp
#print axioms dual_negligible
end XiPrime8845.PRZZSelectedDiscarded

