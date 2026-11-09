import PRZZCappedDiscardedIBP

/-! Common-cap arithmetic mass and height-uniform genuine dual discarded
IBP. Constants precede the coefficients, selector and every finite cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Filter MeasureTheory Finset
namespace XiPrime8845.PRZZCappedDiscarded
open PRZZMellinSeparation PRZZDiscardedOuter PRZZDualDiscardedBudget
open PRZZCappedDiscardedIBP
open PRZZSelectedDiscarded (sourceMask source_geometry)
set_option maxHeartbeats 10000000

theorem pair_mass (c : ℕ → ℂ) (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (N : ℕ)
    (hc : ∀ n ∈ Icc 1 N, ‖c n‖ ≤ Hcap) :
    (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ‖c u‖*‖c v‖) ≤ (N:ℝ)^2*Hcap^2 := by
  calc
    _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, Hcap*Hcap := by
      apply sum_le_sum; intro u hu
      apply sum_le_sum; intro v hv
      exact mul_le_mul (hc u hu) (hc v hv) (norm_nonneg _) hHcap
    _ = _ := by simp [pow_two,mul_assoc]

theorem finite_mass (G H : ℝ → ℂ) (c : ℕ → ℂ) (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (U Z : ℝ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hcut : ∀ Q V x y, ‖scaledCutoff G Q x*scaledCutoff H V y‖ ≤ U)
    (N : ℕ) (Q V d : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) (hN : 1 ≤ N) (hcoef : ∀ n ∈ Icc 1 N, ‖c n‖ ≤ Hcap)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hw : ∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, ‖w u v p‖ ≤ 1)
    (hZsum : ∀ t : Finset (ℕ × ℕ), ∑ p ∈ t, PRZZSourceBoundaryDecay.majorant p ≤ Z) :
    (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
      ‖PRZZCappedDiscardedIBP.coefficient G H c Q V d a b u v p*w u v p‖ *
        (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ)) ≤
      ((N:ℝ)^2*Hcap^2)*(U*Z) := by
  have hc (u v : ℕ) (hu : u ∈ Icc 1 N) (hv : v ∈ Icc 1 N) (p : ℕ × ℕ) (hp : p ∈ s u v) :
      ‖PRZZCappedDiscardedIBP.coefficient G H c Q V d a b u v p*w u v p‖ ≤
        (‖c u‖*‖c v‖)*U := by
    rw [norm_mul,PRZZCappedDiscardedIBP.coefficient,norm_mul]
    have hh := PRZZTimeDiscarded.actual_coefficient_cap c c (-b) (-a)
      ((p.1+1,p.2+1),(u,v)) (by dsimp; omega) (by dsimp; omega)
      (mem_Icc.mp hu).1 (mem_Icc.mp hv).1
      (by simp only [neg_re]; have := (abs_le.mp ((abs_re_le_norm b).trans hb)).2; linarith)
      (by simp only [neg_re]; have := (abs_le.mp ((abs_re_le_norm a).trans ha)).2; linarith)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul hh (hcut Q V (d*u) (d*v)) (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans
      (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left (hw u hu v hv p hp)
        (show 0 ≤ (‖c u‖*‖c v‖)*U by positivity)))
  have hpw (p : ℕ × ℕ) : (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ) =
      PRZZSourceBoundaryDecay.majorant p := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rfl
  calc
    _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, (‖c u‖*‖c v‖)*(U*Z) := by
      apply sum_le_sum; intro u hu
      apply sum_le_sum; intro v hv
      calc
        _ ≤ ∑ p ∈ s u v, ((‖c u‖*‖c v‖)*U)*PRZZSourceBoundaryDecay.majorant p := by
          apply sum_le_sum; intro p hp
          rw [hpw]
          exact mul_le_mul_of_nonneg_right (hc u v hu hv p hp)
            (by unfold PRZZSourceBoundaryDecay.majorant; positivity)
        _ = ((‖c u‖*‖c v‖)*U)*(∑ p ∈ s u v, PRZZSourceBoundaryDecay.majorant p) := by rw [mul_sum]
        _ ≤ ((‖c u‖*‖c v‖)*U)*Z := mul_le_mul_of_nonneg_left (hZsum _) (by positivity)
        _ = _ := by ring
    _ = (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ‖c u‖*‖c v‖)*(U*Z) := by simp only [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pair_mass c Hcap hHcap N hcoef) (by positivity)


theorem outer_budget_absorbed (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps power r : ℝ)
    (he : 0 < eps) (hr : 0 < r) :
    ∃ n : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (T K C : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ K → 0 ≤ C →
      ((N:ℝ)^2*Hcap^2)*(K*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) ≤
        (K*C^n*D)*T^(-power) := by
  obtain ⟨n,D,hD,h⟩ := PRZZDiscardedSuppliers.loss_absorbed eps 2 power r he hr
  refine ⟨n,Hcap^2*D+1,by positivity,?_⟩
  intro N T K C hN hNT hlog hK hC
  have hT : 1 ≤ T := (by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT
  have hm : (N:ℝ)^2 ≤ T^2 := by gcongr
  have hp := h T K C hT hlog hK hC
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg Hcap)
  calc
    _ ≤ (T^2*Hcap^2)*(K*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
      gcongr
    _ = Hcap^2*(T^(2:ℝ)*K*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
      rw [Real.rpow_two]; ring
    _ ≤ Hcap^2*((K*C^n*D)*T^(-power)) := hh
    _ ≤ _ := by
      have hz : 0 ≤ K*C^n*T^(-power) := by positivity
      nlinarith only [hz]

theorem dual_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (coeffs : ℕ → ℂ) (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖coeffs n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖outerValue F G H P R coeffs N K T M Q V d eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) s‖ ≤ C*T^(-power) := by
  classical
  obtain ⟨U,hU,hcut⟩ := PRZZValuedCutoffs.cutoff_pair_uniform G H hG hH hcG hcH
  obtain ⟨J,hJ,hmass⟩ := shifted_mass F hF hcF hsF S r hS hr
  obtain ⟨n,D,hD,habs⟩ := outer_budget_absorbed Hcap hHcap eps power r he hr
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
  intro coeffs N K M Q V d A B P R s hcoef hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
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
  have hi := source_outer_ibp F G H P R coeffs hF hsF hsG hm hlo hhi hleft hright
    N K n T M Q V d eps a b s hT hM hQ hd he1 ha hb hs
  let w := sourceMask P R (scaledCutoff G Q) K T M Q d eps
  let E := J n*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps)
  have hE : 0 ≤ E := by dsimp [E]; have := hJ n; positivity
  have hbnd : ‖outerValue F G H P R coeffs N K T M Q V d eps a b s‖ ≤
      ((N:ℝ)^2*Hcap^2)*(U*Z)*E := by
    apply hi.trans
    calc
      _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          (‖coefficient G H coeffs Q V d a b u v p*w u v p‖*
            (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ))*E := by
        apply sum_le_sum; intro u hu
        apply sum_le_sum; intro v hv
        apply sum_le_sum; intro p hp
        have hh := hmass A B hA hB hsep n (((p.1:ℝ)+1)*((p.2:ℝ)+1)) eps (by positivity)
        rw [add_div] at hh
        have hh' := mul_le_mul_of_nonneg_left hh
          (norm_nonneg (coefficient G H coeffs Q V d a b u v p*w u v p))
        convert hh' using 1 <;> dsimp only [a,b,w,E] <;> ring
      _ = (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          ‖coefficient G H coeffs Q V d a b u v p*w u v p‖*
            (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ))*E := by simp only [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (finite_mass G H coeffs Hcap hHcap U Z hU hZ hcut N Q V d a b s w hN hcoef ha hb hg.1 hZsum) hE
  have hh := habs N T (U*Z*J n) 10 hN hNT hlog (by have := hJ n; positivity) (by norm_num)
  apply hbnd.trans
  calc
    _ = ((N:ℝ)^2*Hcap^2)*
        ((U*Z*J n)*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps)) := by dsimp [E]; ring
    _ ≤ _ := hh.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by linarith) _))


theorem actual_outer_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ H : ℕ → ℝ, (∀ n, 0 ≤ H n) ∧
      ∀ (n N : ℕ) (c : ℕ → ℂ) (Hcap : ℝ) (A B alpha beta : ℂ) (T C eps : ℝ),
      (∀ k ∈ Finset.Icc 1 N, ‖c k‖ ≤ Hcap) → 0 ≤ Hcap → 1 ≤ N → r ≤ ‖A+B‖ → 1 < T → 0 ≤ C →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      (∀ u ∈ Finset.Icc 1 N, ∀ v ∈ Finset.Icc 1 N, ∀ p ∈ s u v, ‖w u v p‖ ≤ 1) →
      (∀ u ∈ Finset.Icc 1 N, ∀ v ∈ Finset.Icc 1 N, ∀ p ∈ s u v, w u v p ≠ 0 →
        0 < |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ∧
        max (((p.1:ℝ)+1)*u) (((p.2:ℝ)+1)*v)/
          |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        row F T c
          c alpha beta
          ((A+B)/(Real.log T:ℂ)) u v (s u v) (w u v) t‖ ≤
        ((N:ℝ)^2*Hcap^2)*
          (H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
  classical
  obtain ⟨H,hH,hh⟩ := PRZZDiscardedPartition.masked_time_bound F hF hsF hsupp r hr
  refine ⟨H,hH,?_⟩
  intro n N c Hcap A B alpha beta T C eps hcoef hHcap hN hsep hT hC ha hb s w hw hg
  have hHn := hH n
  let a := c
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (Real.log_pos hT).ne')
  rw [outer_integral_eq F hF hsupp T (by linarith) _ _ _ _ _ hs]
  have hbnd (u : ℕ) (hu : u ∈ Finset.Icc 1 N) (v : ℕ) (hv : v ∈ Finset.Icc 1 N) :
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
    _ ≤ ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (‖a u‖*‖a v‖)*(H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by
      apply sum_le_sum
      intro u hu
      exact (norm_sum_le _ _).trans (sum_le_sum (fun v hv => hbnd u hu v hv))
    _ = (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, ‖a u‖*‖a v‖)*
        (H n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps)) := by simp only [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pair_mass c Hcap hHcap N hcoef)
      (by positivity)

theorem mixed_dual_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c dcoeff : ℕ → ℂ) (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖dcoeff n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖PRZZMixedPoisson.lift (fun coeffs => outerValue F G H P R coeffs N K T M Q V d eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) s) c dcoeff‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := dual_negligible F G H hF hcF hsF hG hH hcG hcH hsG
    (2*Hcap) (by positivity) S r eps power hS hr he he1
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c dcoeff N K M Q V d A B P R s hc hd hN hNT hM hQ hdpos hA hB hsep hm hlo hhi hleft hright
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact h _ N K M Q V d A B P R s
    (PRZZClassZeroCorrection.combine_cap N c dcoeff Hcap hHcap hc hd z hz)
    hN hNT hM hQ hdpos hA hB hsep hm hlo hhi hleft hright

def tailError (F : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ) (T : ℝ)
    (alpha beta sigma : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) : ℂ :=
  ∫ t : ℝ, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    row F T c c alpha beta sigma u v (s u v) (w u v) t

/-- The common coefficient cap supplies the outer mass. Arbitrary finite
product masks and spatial truncations are allowed. -/
theorem actual_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (c : ℕ → ℂ) (N : ℕ) (A B alpha beta : ℂ) (T : ℝ),
      (∀ k ∈ Finset.Icc 1 N, ‖c k‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      Geometry N T eps s w →
      ‖tailError F c N T alpha beta ((A+B)/(Real.log T:ℂ)) s w‖ ≤ E*T^(-power) := by
  obtain ⟨H,hH,hh⟩ := actual_outer_bound F hF hsF hsupp r hr
  obtain ⟨n,D,hD,hd⟩ := outer_budget_absorbed Hcap hHcap eps power r he hr
  refine ⟨H n*10^n*D+1,by have := hH n; positivity,?_⟩
  intro c N A B alpha beta T hcoef hN hNT hT hL hsep ha hb s w hg
  have h1 := hh n N c Hcap A B alpha beta T 10 eps hcoef hHcap hN hsep hT (by norm_num) ha hb s w hg.1 hg.2
  have h2 := hd N T (H n) 10 hN hNT hL (hH n) (by norm_num)
  exact (h1.trans h2).trans (by gcongr; linarith)

theorem tail_scale (F : ℝ → ℂ) (coeffs : ℕ → ℂ) (N : ℕ) (T : ℝ)
    (alpha beta sigma c : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) :
    tailError F coeffs N T alpha beta sigma s (fun u v p => c*w u v p) =
      c*tailError F coeffs N T alpha beta sigma s w := by
  unfold tailError row
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Arbitrary bounded outer multipliers may now contain the actual
cutoff values. The loss is linear in their common bound, not in the
number of arithmetic pairs. -/
theorem multiplier_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (coeffs : ℕ → ℂ) (N : ℕ) (A B alpha beta : ℂ) (T U : ℝ),
      (∀ k ∈ Finset.Icc 1 N, ‖coeffs k‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re → 0 ≤ U →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ)
        (g : ℕ → ℕ → ℂ),
      Geometry N T eps s w → (∀ u v, ‖g u v‖ ≤ U) →
      ‖tailError F coeffs N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (fun u v p => g u v*w u v p)‖ ≤ (U+1)*E*T^(-power) := by
  obtain ⟨E,hE,hh⟩ := actual_negligible F hF hsF hsupp Hcap hHcap eps power r he hr
  refine ⟨E,hE,?_⟩
  intro coeffs N A B alpha beta T U hcoef hN hNT hT hL hsep ha hb hU s w g hw hg
  have hU1 : 0 < U+1 := by linarith
  have hUc : ((U+1:ℝ):ℂ) ≠ 0 := by exact_mod_cast hU1.ne'
  let wn := fun u v p => (g u v/((U+1:ℝ):ℂ))*w u v p
  have hn : Geometry N T eps s wn := by
    constructor
    · intro u hu v hv p hp
      dsimp [wn]
      rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU1]
      have hg1 : ‖g u v‖/(U+1) ≤ 1 := (div_le_one hU1).mpr (by linarith [hg u v])
      exact (mul_le_mul hg1 (hw.1 u hu v hv p hp) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    · intro u hu v hv p hp hnon
      exact hw.2 u hu v hv p hp (mul_ne_zero_iff.mp hnon).2
  have hbound := hh coeffs N A B alpha beta T hcoef hN hNT hT hL hsep ha hb s wn hn
  have heq : (fun u v p => g u v*w u v p) =
      (fun u v p => ((U+1:ℝ):ℂ)*wn u v p) := by
    funext u v p
    dsimp [wn]
    field_simp
  rw [heq,tail_scale,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU1]
  exact (mul_le_mul_of_nonneg_left hbound hU1.le).trans_eq (by ring)

theorem valued_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H)
    (hsG : HasCompactSupport G) (hsH : HasCompactSupport H)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (coeffs : ℕ → ℂ) (N : ℕ) (A B alpha beta : ℂ) (T Q R d : ℝ),
      (∀ k ∈ Finset.Icc 1 N, ‖coeffs k‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      ∀ (s : ℕ → ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ → ℕ × ℕ → ℂ),
      Geometry N T eps s w →
      ‖tailError F coeffs N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (fun u v p => (PRZZMellinSeparation.scaledCutoff G Q (d*u)*
          PRZZMellinSeparation.scaledCutoff H R (d*v))*w u v p)‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,hh⟩ := multiplier_negligible F hF hsF hsupp Hcap hHcap eps power r he hr
  obtain ⟨U,hU,hg⟩ := PRZZValuedCutoffs.cutoff_pair_uniform G H hG hH hsG hsH
  refine ⟨(U+1)*E,by positivity,?_⟩
  intro coeffs N A B alpha beta T Q R d hcoef hN hNT hT hL hsep ha hb s w hw
  exact hh coeffs N A B alpha beta T U hcoef hN hNT hT hL hsep ha hb hU s w _ hw
    (fun u v => hg Q R (d*u) (d*v))

def directError (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (coeffs : ℕ → ℂ) (N K : ℕ)
    (T M Q V d eps : ℝ) (A B : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ)) : ℂ :=
  tailError F coeffs N T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    ((A+B)/(Real.log T:ℂ)) s (fun u v p =>
      (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))*
        sourceMask P R (scaledCutoff G Q) K T M Q d eps u v p)

theorem direct_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps power : ℝ) (hr : 0 < r) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (coeffs : ℕ → ℂ) (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      (∀ k ∈ Finset.Icc 1 N, ‖coeffs k‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖directError F G H P R coeffs N K T M Q V d eps A B s‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := valued_negligible F G H hF hcF hsF
    hG hH hcG hcH Hcap hHcap eps power r he hr
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with T hsmall hlarge
  have hT : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hlarge
  have hlog : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using hh
  intro coeffs N K M Q V d A B P R s hcoef hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  have ha := (Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA)
  have hb := (Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB)
  have hg := source_geometry P R (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    (by linarith) hM hQ hd
    (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) s
  exact h coeffs N A B _ _ T Q V d hcoef hN hNT hT hlog hsep
    (by linarith [(abs_le.mp ha).1]) (by linarith [(abs_le.mp hb).1]) s _ hg

#print axioms direct_negligible
#print axioms actual_negligible
#print axioms tail_scale
#print axioms multiplier_negligible
#print axioms valued_negligible
#print axioms mixed_dual_negligible
#print axioms actual_outer_bound
#print axioms outer_budget_absorbed
#print axioms dual_negligible
#print axioms pair_mass
#print axioms finite_mass
end XiPrime8845.PRZZCappedDiscarded
