import PRZZDualJetMass
import PRZZDualDiscardedIBP

/-! Arithmetic and logarithmic absorption for the genuine dual discarded
integral. Product indices are summed with a summable R^-2 majorant, not
their truncation cardinality. Constants precede every spatial cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Filter MeasureTheory Finset
namespace XiPrime8845.PRZZDualDiscardedBudget
open PRZZFullWeightJets PRZZMellinSeparation PRZZDiscardedOuter
set_option maxHeartbeats 8000000

theorem convolution_cap (A B D : ℕ → ℝ) (z : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hBD : ∀ i, B i ≤ D i*z) (n : ℕ) :
    convolution A B n ≤ convolution A D n*z := by
  unfold PRZZFullWeightJets.convolution
  rw [sum_mul]
  apply sum_le_sum; intro i hi
  exact (mul_le_mul_of_nonneg_left (hBD (n-i))
    (mul_nonneg (Nat.cast_nonneg _) (hA i))).trans_eq (by ring)

/-- All genuine Gamma derivative costs, with the source singularity
factored out before selecting the height. -/
theorem shifted_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ U : ℕ → ℝ, (∀ n, 0 ≤ U n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (n : ℕ) (R eps : ℝ), 0 < R →
      PRZZDualTimeIBP.jetMass F T (2*Real.pi*R)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) (-((A+B)/(Real.log T:ℂ))) n *
          (10*T^(1-eps))^n ≤
        U n*(1+(Real.log T)^2/r^2)*R^(-2:ℝ)*10^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨C,D,E,hpos,hm⟩ := PRZZDualJetMass.all_mass F hF hcF hsF S 2 hS (by norm_num)
  let V := fun (n : ℕ) (sigma : ℂ) => convolution PRZZDualJetTransfer.constant
    (fun j => convolution C (fun i => D i+E i/‖sigma‖^2) j) n
  let K := fun n => convolution PRZZDualJetTransfer.constant
    (fun j => convolution C (fun i => D i+E i) j) n
  have hK (n : ℕ) : 0 ≤ K n := by
    dsimp [K,PRZZFullWeightJets.convolution]
    exact sum_nonneg (fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (PRZZDualJetTransfer.constant_nonneg i))
      (sum_nonneg (fun j hj => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hpos j).1)
        (add_nonneg (hpos (n-i-j)).2.1 (hpos (n-i-j)).2.2))))
  have hV (n : ℕ) (sigma : ℂ) : V n sigma ≤ K n*(1+1/‖sigma‖^2) := by
    apply convolution_cap _ _ _ _ PRZZDualJetTransfer.constant_nonneg
    intro j
    exact convolution_cap C _ _ _ (fun i => (hpos i).1) (fun i => by
      have hD := (hpos i).2.1
      have hE := (hpos i).2.2
      have hh := mul_nonneg hD (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg ‖sigma‖))
      simp only [div_eq_mul_inv,one_mul] at hh ⊢
      nlinarith) j
  refine ⟨fun n => Real.exp (2*S+7)*K n/Real.pi^2,fun n => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (hK n)) (sq_nonneg _),?_⟩
  filter_upwards [hm,eventually_gt_atTop (1:ℝ)] with T hm hT
  intro A B hA hB hsep n R eps hR
  have hs : -((A+B)/(Real.log T:ℂ)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (Real.log_pos hT).ne'))
  have hh := hm A B hA hB n (2*Real.pi*R) _ (by positivity) hs
  have hv : V n (-((A+B)/(Real.log T:ℂ))) ≤ K n*(1+(Real.log T)^2/r^2) := by
    have hz := PRZZDiscardedSuppliers.log_shift_cap (V n) (K n) r (hK n) hr
      (hV n) (-A) (-B) (Real.log T) (Real.log_pos hT).ne' (by simpa only [← neg_add,norm_neg] using hsep)
    simpa only [← neg_add,neg_div] using hz
  change _ ≤ Real.exp (2*S+7)*V n (-((A+B)/(Real.log T:ℂ)))*
    (2*Real.pi*R/(2*T))^(-(2:ℝ))*T/T^n at hh
  have hcap : Real.exp (2*S+7)*V n (-((A+B)/(Real.log T:ℂ)))*
      (2*Real.pi*R/(2*T))^(-(2:ℝ))*T/T^n ≤
      Real.exp (2*S+7)*(K n*(1+(Real.log T)^2/r^2))*
      (2*Real.pi*R/(2*T))^(-(2:ℝ))*T/T^n := by
    gcongr
  have hh' := mul_le_mul_of_nonneg_right (hh.trans hcap)
    (show 0 ≤ (10*T^(1-eps))^n by positivity)
  apply hh'.trans_eq
  rw [mul_pow,← Real.rpow_natCast (T^(1-eps)) n,← Real.rpow_mul (by linarith : 0 ≤ T)]
  rw [show T^(3-(n:ℝ)*eps) = T^3/T^n*T^((1-eps)*(n:ℝ)) by
    rw [show 3-(n:ℝ)*eps = (3-(n:ℝ))+(1-eps)*(n:ℝ) by ring,
      Real.rpow_add (by linarith : 0 < T),Real.rpow_sub (by linarith : 0 < T),Real.rpow_natCast]
    norm_num [Real.rpow_natCast]]
  norm_num [Real.rpow_neg (by positivity : (0:ℝ) ≤ 2*Real.pi*R/(2*T)),
    Real.rpow_neg hR.le,Real.rpow_two]
  field_simp <;> ring

/-- Actual coefficient values and the entire finite product grid, with
no cost proportional to the size of that grid. -/
theorem finite_mass (G H : ℝ → ℂ) (js : List ℕ) (U Z : ℝ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hcut : ∀ Q V x y, ‖scaledCutoff G Q x*scaledCutoff H V y‖ ≤ U)
    (N : ℕ) (Q V d : ℝ) (a b : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ))
    (w : ℕ → ℕ → ℕ × ℕ → ℂ) (hN : 1 ≤ N)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hw : ∀ u ∈ Icc 1 N, ∀ v ∈ Icc 1 N, ∀ p ∈ s u v, ‖w u v p‖ ≤ 1)
    (hZsum : ∀ t : Finset (ℕ × ℕ), ∑ p ∈ t, PRZZSourceBoundaryDecay.majorant p ≤ Z) :
    (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
      ‖PRZZDualDiscardedIBP.coefficient G H js Q V d a b u v p*w u v p‖ *
        (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ)) ≤
      ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*(U*Z) := by
  let c := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  have hc (u v : ℕ) (hu : u ∈ Icc 1 N) (hv : v ∈ Icc 1 N) (p : ℕ × ℕ) (hp : p ∈ s u v) :
      ‖PRZZDualDiscardedIBP.coefficient G H js Q V d a b u v p*w u v p‖ ≤
        (‖c u‖*‖c v‖)*U := by
    rw [norm_mul,PRZZDualDiscardedIBP.coefficient,norm_mul]
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
    _ ≤ _ := mul_le_mul_of_nonneg_right (PRZZDiscardedSuppliers.outer_mass js N hN) (by positivity)

/-- Uniform in every finite product truncation and every spatial scale.
The order is selected before height, and genuine Gamma jets are estimated
inside IBP before summing the actual arithmetic coefficients. -/
theorem scaled_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖PRZZDualDiscardedIBP.outerValue F G H P js N K T M Q V d eps
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
  intro N K M Q V d A B P s hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  have ha : ‖a‖ ≤ 1/4 := hsmall.2 A hA
  have hb : ‖b‖ ≤ 1/4 := hsmall.2 B hB
  have hs : a+b ≠ 0 := by
    dsimp [a,b]; rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  have hg := source_geometry P (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    (by linarith) hM hQ hd (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) s
  have hi := PRZZDualDiscardedIBP.source_outer_ibp F G H P js hF hsF hsG hm hlo hhi hleft hright
    N K n T M Q V d eps a b s hT hM hQ hd he1 ha hb hs
  let w := sourceMask P (scaledCutoff G Q) K T M Q d eps
  let E := J n*(1+(Real.log T)^2/r^2)*10^n*T^(3-(n:ℝ)*eps)
  have hE : 0 ≤ E := by dsimp [E]; have := hJ n; positivity
  have hbnd : ‖PRZZDualDiscardedIBP.outerValue F G H P js N K T M Q V d eps a b s‖ ≤
      ((N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js))*(U*Z)*E := by
    apply hi.trans
    calc
      _ ≤ ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          (‖PRZZDualDiscardedIBP.coefficient G H js Q V d a b u v p*w u v p‖*
            (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ))*E := by
        apply sum_le_sum; intro u hu
        apply sum_le_sum; intro v hv
        apply sum_le_sum; intro p hp
        have hh := hmass A B hA hB hsep n (((p.1:ℝ)+1)*((p.2:ℝ)+1)) eps (by positivity)
        rw [add_div] at hh
        have hh' := mul_le_mul_of_nonneg_left hh
          (norm_nonneg (PRZZDualDiscardedIBP.coefficient G H js Q V d a b u v p*w u v p))
        convert hh' using 1 <;> dsimp only [a,b,w,E] <;> ring
      _ = (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ s u v,
          ‖PRZZDualDiscardedIBP.coefficient G H js Q V d a b u v p*w u v p‖*
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

#print axioms convolution_cap
#print axioms shifted_mass
#print axioms finite_mass
#print axioms scaled_negligible
end XiPrime8845.PRZZDualDiscardedBudget
