import PRZZTimeDiscarded
import PRZZOptimalOuter

/-! Suppliers for discarded-gap geometry and logarithmic shifts.
The positive source support supplies the one-sided product bound; no
comparability of the other product is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Complex
namespace XiPrime8845.PRZZDiscardedSuppliers
set_option maxHeartbeats 3000000

theorem all_gap_geometry (T M Q d C eps x y : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hC : 0 ≤ C) (hx : 0 < x) (hy : 0 < y)
    (hscale : x ≤ C*M*Q/d) (hheight : 1 ≤ T^(1-eps))
    (hgap : PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |y-x|) :
    0 < |y-x| ∧ max x y/|y-x| ≤ (C+1)*T^(1-eps) := by
  let D := PRZZSourceCutoffs.deltaCutoff T M Q eps/d
  have hD : 0 < D := by unfold D PRZZSourceCutoffs.deltaCutoff; positivity
  have hg : 0 < |y-x| := hD.trans_le hgap
  refine ⟨hg,?_⟩
  have hb : max x y ≤ x+|y-x| := by
    apply max_le
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · linarith [le_abs_self (y-x)]
  have hs : (C*M*Q/d)/D = C*T^(1-eps) :=
    PRZZDeltaDecay.source_scale T M Q d C eps hT hM hQ hd
  calc
    _ ≤ (x+|y-x|)/|y-x| := div_le_div_of_nonneg_right hb hg.le
    _ = x/|y-x|+1 := by rw [add_div,div_self hg.ne']
    _ ≤ (C*M*Q/d)/D+1 := by
      gcongr
    _ = C*T^(1-eps)+1 := by rw [hs]
    _ ≤ _ := by nlinarith

/-- One original spatial cutoff and one original arithmetic cutoff
supply geometry for every discarded signed gap, including distant y. -/
theorem cutoff_geometry (F G : ℝ → ℂ) (T M Q d m u y eps : ℝ)
    (hF : Function.support F ⊆ Icc (M/2) (3*M))
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q))
    (hf : F m ≠ 0) (hg : G (d*u) ≠ 0)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hu : 0 < u) (hy : 0 < y) (hheight : 1 ≤ T^(1-eps))
    (hgap : PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |y-m*u|) :
    0 < |y-m*u| ∧ max (m*u) y/|y-m*u| ≤ 10*T^(1-eps) := by
  have hm := hF hf
  have hdu := hG hg
  have hm0 : 0 < m := (by positivity : 0 < M/2).trans_le hm.1
  have hs : m*u ≤ 9*M*Q/d := by
    apply (le_div_iff₀ hd).mpr
    have hh := mul_le_mul hm.2 hdu.2 (by positivity : 0 ≤ d*u) (by positivity : 0 ≤ 3*M)
    nlinarith only [hh]
  simpa only [show (9:ℝ)+1=10 by norm_num] using all_gap_geometry T M Q d 9 eps (m*u) y hT hM hQ hd
    (by norm_num) (mul_pos hm0 hu) hy hs hheight hgap

theorem log_shift_cap (U : ℂ → ℝ) (K r : ℝ) (hK : 0 ≤ K) (hr : 0 < r)
    (hU : ∀ sigma, U sigma ≤ K*(1+1/‖sigma‖^2))
    (A B : ℂ) (L : ℝ) (hL : L ≠ 0) (hsep : r ≤ ‖A+B‖) :
    U ((A+B)/(L:ℂ)) ≤ K*(1+L^2/r^2) := by
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have he : 1/‖(A+B)/(L:ℂ)‖^2 = L^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  have hh := hU ((A+B)/(L:ℂ))
  rw [he] at hh
  apply hh.trans
  gcongr

/-- The outer coefficient mass is supplied for the literal convolution
coefficients. This coarse polynomial loss is usable with arbitrary IBP
order; it is not the mollifier mean-square estimate. -/
theorem outer_mass (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      ‖(PRZZGCoefficient.coefficient js u:ℂ)‖*
        ‖(PRZZGCoefficient.coefficient js v:ℂ)‖) ≤
      (N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js) := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (Real.log N)^(2*PRZZGCoefficient.degree js) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hh := PRZZArithmeticMass.pair_bound js N u v hN
        (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2
        (Finset.mem_Icc.mp hv).1 (Finset.mem_Icc.mp hv).2
      simpa only [norm_mul,norm_star] using hh
    _ = _ := by simp [pow_two,mul_assoc]

/-- The logarithmically varying shift is substituted into the whole
finite discarded-product integral, with constants before all shifts and T. -/
theorem scaled_summed (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ (n : ℕ) (alpha beta : ℂ) (T C eps J : ℝ),
      r ≤ ‖alpha+beta‖ → 1 < T → 0 ≤ C → 0 ≤ J →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (x y B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ J) →
      (∀ p ∈ s, 0 < x p ∧ 0 < y p ∧ x p ≤ B p ∧ y p ≤ B p ∧
        0 < D p ∧ D p ≤ |y p-x p| ∧ B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
          ((alpha+beta)/(Real.log T:ℂ)) t)‖ ≤
        J*K n*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨U,hU,hcap,h⟩ := PRZZTimeDiscarded.summed_controlled F hF hsF hsupp
  choose K hK hk using hcap
  refine ⟨K,hK,?_⟩
  intro n alpha beta T C eps J hsep hT hC hJ s c x y B D hc hg
  have hT0 : 0 < T := by linarith
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hab : alpha+beta ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL
  have hh := h n ((alpha+beta)/(Real.log T:ℂ)) T C eps J
    (div_ne_zero hab hLc) hT0 hC hJ s c x y B D hc hg
  have hu := log_shift_cap (U n) (K n) r (hK n) hr (hk n) alpha beta (Real.log T) hL hsep
  apply hh.trans
  calc
    _ ≤ J*(K n*(1+(Real.log T)^2/r^2))*C^n*T^(3-(n:ℝ)*eps) := by gcongr
    _ = _ := by ring

/-- Both the outer arithmetic polynomial and the shift log-square are
absorbed by the IBP order. The fixed K and C costs remain explicit. -/
theorem loss_absorbed (eps b A r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ n : ℕ, ∃ H : ℝ, 0 < H ∧ ∀ T K C : ℝ,
      1 ≤ T → 1 ≤ Real.log T → 0 ≤ K → 0 ≤ C →
      T^b*K*(1+(Real.log T)^2/r^2)*C^n*T^(3-(n:ℝ)*eps) ≤
        (K*C^n*H)*T^(-A) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((b+3+A)/eps)
  have hm : b+3-(n:ℝ)*eps < -A := by
    have hh := (div_lt_iff₀ he).mp hn
    nlinarith
  obtain ⟨H,hH,hh⟩ := PRZZOptimalOuter.power_log_absorbed 2 (b+3-(n:ℝ)*eps) (-A) hm
  refine ⟨n,(1+1/r^2)*H,by positivity,?_⟩
  intro T K C hT hlog hK hC
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog2 : 1 ≤ (Real.log T)^2 := by nlinarith
  have hl : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*(Real.log T)^2 := by
    simp only [div_eq_mul_inv,one_mul]
    nlinarith
  calc
    _ ≤ T^b*K*((1+1/r^2)*(Real.log T)^2)*C^n*T^(3-(n:ℝ)*eps) := by gcongr
    _ = (K*C^n*(1+1/r^2))*(T^(b+3-(n:ℝ)*eps)*(Real.log T)^2) := by
      rw [show b+3-(n:ℝ)*eps = b+(3-(n:ℝ)*eps) by ring,Real.rpow_add hT0]
      ring
    _ ≤ (K*C^n*(1+1/r^2))*(H*T^(-A)) := by
      exact mul_le_mul_of_nonneg_left (hh T hT) (by positivity)
    _ = _ := by ring

/-- Uniform negative powers for the actual logarithmic shift family.
The finite set can grow with height or the AFE truncation. -/
theorem scaled_negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (r C eps b A : ℝ) (hr : 0 < r) (hC : 0 ≤ C) (he : 0 < eps) :
    ∃ H : ℝ, 0 < H ∧ ∀ (alpha beta : ℂ) (T : ℝ),
      r ≤ ‖alpha+beta‖ → 1 < T → 1 ≤ Real.log T →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (x y B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ T^b) →
      (∀ p ∈ s, 0 < x p ∧ 0 < y p ∧ x p ≤ B p ∧ y p ≤ B p ∧
        0 < D p ∧ D p ≤ |y p-x p| ∧ B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
          ((alpha+beta)/(Real.log T:ℂ)) t)‖ ≤ H*T^(-A) := by
  obtain ⟨K,hK,h⟩ := scaled_summed F hF hsF hsupp r hr
  obtain ⟨n,H,hH,habs⟩ := loss_absorbed eps b A r he hr
  have hKn := hK n
  refine ⟨K n*C^n*H+1,by positivity,?_⟩
  intro alpha beta T hsep hT hlog s c x y B D hc hg
  have hT0 : 0 < T := by linarith
  have hh := h n alpha beta T C eps (T^b) hsep hT hC (by positivity) s c x y B D hc hg
  apply hh.trans
  apply (habs T (K n) C hT.le hlog hKn hC).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hT0.le _)

#print axioms scaled_negligible
#print axioms scaled_summed
#print axioms loss_absorbed
#print axioms all_gap_geometry
#print axioms cutoff_geometry
#print axioms log_shift_cap
#print axioms outer_mass
end XiPrime8845.PRZZDiscardedSuppliers
