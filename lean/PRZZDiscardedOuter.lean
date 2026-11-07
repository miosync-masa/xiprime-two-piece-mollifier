import PRZZDiscardedPartition
import PRZZIntegratedDefect

/-! Actual frozen AFE coefficients in the discarded exact-phase sum.
The finite outer mollifier pairs are summed after time integration, with
integrability proved here. Spatial masks retain explicit support geometry.
No identity between this term and the complete Poisson remainder is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZDiscardedOuter
set_option maxHeartbeats 4000000

def row (F : ℝ → ℂ) (T : ℝ) (a b : ℕ → ℂ) (alpha beta sigma : ℂ)
    (u v : ℕ) (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ s, (PRZZActualLocalReplacement.coefficient a b alpha beta 0
    ((p.1+1,p.2+1),(u,v))*w p)*
    (exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))*
      PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)

theorem row_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0 < T) (a b : ℕ → ℂ) (alpha beta sigma : ℂ)
    (hs : sigma ≠ 0) (u v : ℕ) (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) :
    Integrable (row F T a b alpha beta sigma u v s w) := by
  apply integrable_finsetSum
  intro p hp
  have hi := PRZZTimeAmplitude.jet_integrable F hF hsupp T
    (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma hT (by positivity) hs 0
  simp only [iteratedDeriv_zero] at hi
  have hc : Continuous (fun t : ℝ =>
      exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))) := by fun_prop
  have hb : ∀ t : ℝ, ‖exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))‖ ≤ 1 := by
    intro t; simp [Complex.norm_exp]
  exact (hi.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)).const_mul _

theorem outer_integral_eq (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0 < T) (a b : ℕ → ℂ) (alpha beta sigma : ℂ)
    (hs : sigma ≠ 0) (N : ℕ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) :
    (∫ t : ℝ, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      row F T a b alpha beta sigma u v (s u v) (w u v) t) =
    ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      ∫ t : ℝ, row F T a b alpha beta sigma u v (s u v) (w u v) t := by
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro u hu
    exact integral_finsetSum _ (fun v hv => row_integrable F hF hsupp T hT a b
      alpha beta sigma hs u v (s u v) (w u v))
  · intro u hu
    exact integrable_finsetSum _ (fun v hv => row_integrable F hF hsupp T hT a b
      alpha beta sigma hs u v (s u v) (w u v))

/-- Actual four-index coefficients, not a supplied coefficient-mass cap.
The only row conditions concern the nonzero spatial mask. -/
theorem actual_outer_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ H : ℕ → ℝ, (∀ n, 0 ≤ H n) ∧
      ∀ (n N : ℕ) (js : List ℕ) (A B alpha beta : ℂ) (T C eps : ℝ),
      1 ≤ N → r ≤ ‖A+B‖ → 1 < T → 0 ≤ C →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      (∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, ‖w u v p‖ ≤ 1) →
      (∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, w u v p ≠ 0 →
        0 < |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ∧
        max (((p.1:ℝ)+1)*u) (((p.2:ℝ)+1)*v)/
          |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        row F T (fun k => (PRZZGCoefficient.coefficient js k:ℂ))
          (fun k => (PRZZGCoefficient.coefficient js k:ℂ)) alpha beta
          ((A+B)/(Real.log T:ℂ)) u v (s u v) (w u v) t‖ ≤
        ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*
          (H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
  classical
  obtain ⟨H,hH,hh⟩ := PRZZDiscardedPartition.masked_time_bound F hF hsF hsupp r hr
  refine ⟨H,hH,?_⟩
  intro n N js A B alpha beta T C eps hN hsep hT hC ha hb s w hw hg
  have hHn := hH n
  let a := fun k => (PRZZGCoefficient.coefficient js k:ℂ)
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (Real.log_pos hT).ne')
  rw [outer_integral_eq F hF hsupp T (by linarith) _ _ _ _ _ hs]
  have hbnd (u : ℕ) (hu : u ∈ Icc 1 N) (v : ℕ) (hv : v ∈ Icc 1 N) :
      ‖∫ t : ℝ, row F T a a alpha beta ((A+B)/(Real.log T:ℂ)) u v (s u v) (w u v) t‖ ≤
        (‖a u‖*‖a v‖)*(H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
    have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    have hc := hh n A B T C eps (‖a u‖*‖a v‖) hsep hT hC (by positivity)
      (s u v) (fun p => PRZZActualLocalReplacement.coefficient a a alpha beta 0
        ((p.1+1,p.2+1),(u,v))) (w u v)
      (fun p => ((p.1:ℝ)+1)*u) (fun p => ((p.2:ℝ)+1)*v)
      (fun p hp => PRZZTimeDiscarded.actual_coefficient_cap a a alpha beta _
        (by dsimp; omega) (by dsimp; omega) (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 ha hb)
      (hw u hu v hv) (by
        intro p hp hn
        exact ⟨by positivity,by positivity,hg u hu v hv p hp (mul_ne_zero_iff.mp hn).2⟩)
    simpa only [row,mul_assoc] using hc
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        (‖a u‖*‖a v‖)*(H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
      apply sum_le_sum
      intro u hu
      exact (norm_sum_le _ _).trans (sum_le_sum (fun v hv => hbnd u hu v hv))
    _ = (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ‖a u‖*‖a v‖)*
        (H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by simp only [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (PRZZDiscardedSuppliers.outer_mass js N hN)
      (by positivity)

/-- Absorb the supplied outer arithmetic mass, not an assumed polynomial
cap. The order is chosen before N,T and every finite spatial truncation. -/
theorem outer_budget_absorbed (js : List ℕ) (eps A r : ℝ)
    (he : 0 < eps) (hr : 0 < r) :
    ∃ n : ℕ, ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ) (T K C : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ K → 0 ≤ C →
      ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*
        (K*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) ≤
          (K*C^n*H)*T^(-A) := by
  obtain ⟨D,hD,hlog⟩ := PRZZOptimalOuter.power_log_absorbed
    (2*PRZZGCoefficient.degree js) 0 1 (by norm_num)
  obtain ⟨n,E,hE,hpow⟩ := PRZZDiscardedSuppliers.loss_absorbed eps 3 A r he hr
  refine ⟨n,D*E,by positivity,?_⟩
  intro N T K C hN hNT hL hK hC
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hT : 1 ≤ T := hN1.trans hNT
  have hT0 : 0 < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogNT : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hm : (N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js) ≤ D*T^(3:ℝ) := by
    have hl := hlog T hT
    simp only [Real.rpow_zero,one_mul,Real.rpow_one] at hl
    calc
      _ ≤ T^2*(Real.log T)^(2*PRZZGCoefficient.degree js) := by gcongr
      _ ≤ T^2*(D*T) := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
      _ = _ := by norm_num [Real.rpow_natCast]; ring
  have hp := hpow T K C hT hL hK hC
  have hh := mul_le_mul_of_nonneg_left hp hD.le
  apply (mul_le_mul_of_nonneg_right hm (by positivity)).trans
  convert hh using 1 <;> ring

def Geometry (N : ℕ) (T eps : ℝ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) : Prop :=
  (∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, ‖w u v p‖ ≤ 1) ∧
  (∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, w u v p ≠ 0 →
    0 < |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ∧
    max (((p.1:ℝ)+1)*u) (((p.2:ℝ)+1)*v)/
      |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ≤ 10*T^(1-eps))

/-- The arithmetic cutoff is used here as a support selector. Its value
is not an additional amplitude factor in this definition. -/
def sourceMask (P : ℝ → ℝ) (G : ℝ → ℂ) (K : ℕ)
    (T M Q d eps : ℝ) (u v : ℕ) (p : ℕ × ℕ) : ℂ :=
  if G (d*u) = 0 then 0 else
    PRZZDiscardedPartition.mask P M ((p.1:ℝ)+1) K (fun j =>
      PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps/d ≤
        |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u|)

theorem source_geometry (P : ℝ → ℝ) (G : ℝ → ℂ)
    (hP : Antitone P) (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (N K : ℕ) (T M Q d eps : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 < Q) (hd : 0 < d) (hheight : 1 ≤ T^(1-eps))
    (hG : Function.support G ⊆ Set.Icc (Q/2) (3*Q))
    (s : ℕ → ℕ → Finset (ℕ × ℕ)) :
    Geometry N T eps s (sourceMask P G K T M Q d eps) := by
  constructor
  · intro u hu v hv p hp
    unfold sourceMask
    split_ifs
    · simp
    · exact PRZZDiscardedPartition.mask_norm P hP hlo hhi M _ K _ hM (by positivity)
  · intro u hu v hv p hp hn
    have hgu : G (d*u) ≠ 0 := by
      intro hz; exact hn (by simp [sourceMask,hz])
    have hm := hn
    simp only [sourceMask,if_neg hgu] at hm
    have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    exact PRZZDiscardedPartition.mask_geometry P G hleft hright T M Q d
      ((p.1:ℝ)+1) u (((p.2:ℝ)+1)*v) eps K hG hgu hT hM hQ hd hu0
      (by positivity) hheight hm

def tailError (F : ℝ → ℂ) (js : List ℕ) (N : ℕ) (T : ℝ)
    (alpha beta sigma : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) : ℂ :=
  ∫ t : ℝ, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    row F T (fun k => (PRZZGCoefficient.coefficient js k:ℂ))
      (fun k => (PRZZGCoefficient.coefficient js k:ℂ)) alpha beta sigma u v (s u v) (w u v) t

/-- A supplied coefficient cap and a supplied outer-mass cap are both
absent. Arbitrary finite product masks and spatial truncations are allowed. -/
theorem actual_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (N : ℕ) (A B alpha beta : ℂ) (T : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      Geometry N T eps s w →
      ‖tailError F js N T alpha beta ((A+B)/(Real.log T:ℂ)) s w‖ ≤ E*T^(-power) := by
  obtain ⟨H,hH,hh⟩ := actual_outer_bound F hF hsF hsupp r hr
  obtain ⟨n,D,hD,hd⟩ := outer_budget_absorbed js eps power r he hr
  refine ⟨H n*10^n*D+1,by have := hH n; positivity,?_⟩
  intro N A B alpha beta T hN hNT hT hL hsep ha hb s w hg
  have h1 := hh n N js A B alpha beta T 10 eps hN hsep hT (by norm_num) ha hb s w hg.1 hg.2
  have h2 := hd N T (H n) 10 hN hNT hL (hH n) (by norm_num)
  exact (h1.trans h2).trans (by gcongr; linarith)

/-- Fully substitute the source support selector: no nonzero-row or
Geometry premise remains. The actual cutoff values are not included. -/
theorem source_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (N K : ℕ) (A B alpha beta : ℂ) (T M Q d : ℝ)
      (P : ℝ → ℝ) (G : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      0 < M → 0 < Q → 0 < d → 1 ≤ T^(1-eps) →
      Function.support G ⊆ Set.Icc (Q/2) (3*Q) →
      ∀ s : ℕ → ℕ → Finset (ℕ × ℕ),
      ‖tailError F js N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (sourceMask P G K T M Q d eps)‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,hh⟩ := actual_negligible F hF hsF hsupp js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro N K A B alpha beta T M Q d P G hN hNT hT hL hsep ha hb
    hP hlo hhi hleft hright hM hQ hd hheight hG s
  exact hh N A B alpha beta T hN hNT hT hL hsep ha hb s _
    (source_geometry P G hP hlo hhi hleft hright N K T M Q d eps
      (by linarith) hM hQ hd hheight hG s)

/-- One estimate for the literal zeta-to-W defect plus the actual frozen
discarded sum. This is not an identity with the full post-Poisson error:
the retained central sum and phase-replacement error remain separate. -/
theorem replacement_and_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (js : List ℕ) (S r delta eps power : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) (he : 0 < eps) :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Set.Icc T (2*T), ‖phi t‖ ≤ P) →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      Geometry N T eps s w →
      ‖(∫ t in Set.Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun k => (PRZZGCoefficient.coefficient js k:ℂ))
        (fun k => (PRZZGCoefficient.coefficient js k:ℂ)) N t *
        PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) +
        tailError F js N T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          ((A+B)/(Real.log T:ℂ)) s w‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T+E*T^(-power) := by
  obtain ⟨C,hC,hc⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hd
  obtain ⟨E,hE,ht⟩ := actual_negligible F hF hsF hsupp js eps power r he hr
  refine ⟨C,E,hC,hE,?_⟩
  filter_upwards [hc, PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Filter.eventually_ge_atTop (Real.exp 1)] with T hc hsmall hlarge
  have hT : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hlarge
  have hL : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using hh
  intro A B hA hB hsep N hN hNT phi P hphi hP hp s w hg
  have ha := (Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA)
  have hb := (Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB)
  exact (norm_add_le _ _).trans (add_le_add
    (hc A B hA hB hsep N hN hNT phi P hphi hP hp)
    (ht N A B _ _ T hN hNT hT hL hsep
      (by linarith [(abs_le.mp ha).1]) (by linarith [(abs_le.mp hb).1]) s w hg))

#print axioms actual_negligible
#print axioms source_geometry
#print axioms source_negligible
#print axioms replacement_and_tail
#print axioms outer_budget_absorbed
#print axioms row_integrable
#print axioms outer_integral_eq
#print axioms actual_outer_bound
end XiPrime8845.PRZZDiscardedOuter
