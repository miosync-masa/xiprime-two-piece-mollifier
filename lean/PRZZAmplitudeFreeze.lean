import PRZZWeightedSourcePoisson
import PRZZPowerJets
import PRZZDiscardedSuppliers
import Mathlib.Analysis.Calculus.MeanValue

/-! Joint freezing of the positive product argument and complex power.
All constants precede the product scale X and sigma. The local X^-2
decay is retained; no summation over small products is inferred here. -/
noncomputable section
open scoped ContDiff BigOperators
open Set Complex MeasureTheory
namespace XiPrime8845.PRZZAmplitudeFreeze
open PRZZDyadicEnvelope PRZZPowerJets PRZZSourceWDerivatives
set_option maxHeartbeats 4000000

theorem power_bounds (Z : ℝ) :
    ∃ P Q : ℝ, 0 ≤ P ∧ 0 ≤ Q ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ∀ r : ℝ,
      r ∈ Icc (1/2:ℝ) (3/2) → ‖power z r‖ ≤ P ∧ ‖PRZZPowerJets.jet z 1 r‖ ≤ Q := by
  let S := Metric.closedBall (0:ℂ) Z ×ˢ Icc (1/2:ℝ) (3/2)
  have hc : IsCompact S := (isCompact_closedBall (0:ℂ) Z).prod isCompact_Icc
  have hr : ∀ p ∈ S, 0 < p.2 := by intro p hp; linarith [hp.2.1]
  have hl : ContinuousOn (fun p : ℂ × ℝ => Real.log p.2) S :=
    Real.continuousOn_log.comp continuous_snd.continuousOn (fun p hp => (hr p hp).ne')
  have hp : ContinuousOn (fun p : ℂ × ℝ => power p.1 p.2) S := by
    exact (continuous_fst.continuousOn.neg.mul
      (Complex.continuous_ofReal.comp_continuousOn hl)).cexp
  have hq : ContinuousOn (fun p : ℂ × ℝ => PRZZPowerJets.jet p.1 1 p.2) S := by
    have hh := (continuous_fst.continuousOn.neg.mul hp).div
      (Complex.continuous_ofReal.comp_continuousOn continuous_snd.continuousOn)
      (fun p hp => by change (p.2:ℂ) ≠ 0; exact_mod_cast (hr p hp).ne')
    change ContinuousOn (fun p : ℂ × ℝ => (-p.1*power p.1 p.2)/(p.2:ℂ)) S at hh
    simpa [PRZZPowerJets.jet,coeff] using hh
  obtain ⟨P,hP⟩ := hc.exists_bound_of_continuousOn hp
  obtain ⟨Q,hQ⟩ := hc.exists_bound_of_continuousOn hq
  refine ⟨max P 0,max Q 0,le_max_right _ _,le_max_right _ _,?_⟩
  intro z hz r hrr
  have hs : (z,r) ∈ S := ⟨by simpa using hz,hrr⟩
  exact ⟨(hP _ hs).trans (le_max_left _ _),(hQ _ hs).trans (le_max_left _ _)⟩

def profile (z sigma : ℂ) (X r : ℝ) : ℂ := power z r*sourceW sigma (X*r)

theorem profile_deriv (z sigma : ℂ) (X r : ℝ)
    (hs : sigma ≠ 0) (hX : 0 < X) (hr : 0 < r) :
    HasDerivAt (profile z sigma X)
      (PRZZPowerJets.jet z 1 r*sourceW sigma (X*r)+power z r*(PRZZSourceWDerivatives.jet sigma 0 (X*r)*(X:ℂ))) r := by
  have hp : HasDerivAt (power z) (PRZZPowerJets.jet z 1 r) r := by
    have hh := jet_deriv z 0 r hr
    have he : PRZZPowerJets.jet z 0 = power z := by funext x; simp [PRZZPowerJets.jet,coeff]
    rw [he] at hh
    exact hh
  have hw := (source_hasDerivAt sigma hs (X*r) (mul_pos hX hr)).scomp r
    (hasDerivAt_id r |>.const_mul X)
  convert hp.mul hw using 1 <;> (try rfl) <;>
    (try simp only [Function.comp_apply,mul_one,Complex.real_smul]) <;> ring

/-- The entire power-times-W profile, on the actual retained ratio
interval, has a scale-uniform derivative envelope. -/
theorem profile_derivative_bound (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z sigma : ℂ, ‖z‖ ≤ Z → sigma ≠ 0 →
      ∀ X r : ℝ, 0 < X → r ∈ Icc (1/2:ℝ) (3/2) →
      ‖PRZZPowerJets.jet z 1 r*sourceW sigma (X*r)+power z r*(PRZZSourceWDerivatives.jet sigma 0 (X*r)*(X:ℂ))‖ ≤
        (C+D/‖sigma‖^2)*X^(-2:ℝ) := by
  obtain ⟨P,Q,hP,hQ,hpq⟩ := power_bounds Z
  obtain ⟨C0,D0,hC0,hD0,hw0⟩ := source_all_decay 0 2 (by norm_num)
  obtain ⟨C1,D1,hC1,hD1,hw1⟩ := source_derivative_decay 0 2
  refine ⟨4*Q*C0+8*P*C1,4*Q*D0+8*P*D1,by positivity,by positivity,?_⟩
  intro z sigma hz hs X r hX hrr
  have hr : 0 < r := by linarith [hrr.1]
  have hhalf : X/2 ≤ X*r := by nlinarith [hrr.1]
  have hw := hw0 sigma hs (X*r) (by positivity)
  simp only [iteratedDeriv_zero,pow_zero,div_one] at hw
  have hd := hw1 sigma hs (X*r) (by positivity)
  rw [source_iterated sigma hs 0 (X*r) (by positivity)] at hd
  simp only [zero_add,pow_one] at hd
  have hb0 : ‖sourceW sigma (X*r)‖ ≤ 4*(C0+D0/‖sigma‖^2)*X^(-2:ℝ) := by
    apply hw.trans
    rw [Real.rpow_neg (by positivity : 0 ≤ X*r),Real.rpow_two,
      Real.rpow_neg hX.le,Real.rpow_two]
    calc
      _ ≤ (C0+D0/‖sigma‖^2)*((X/2)^2)⁻¹ := by gcongr
      _ = _ := by field_simp; ring
  have hb1 : ‖PRZZSourceWDerivatives.jet sigma 0 (X*r)‖*X ≤
      8*(C1+D1/‖sigma‖^2)*X^(-2:ℝ) := by
    apply (mul_le_mul_of_nonneg_right hd hX.le).trans
    rw [Real.rpow_neg (by positivity : 0 ≤ X*r),Real.rpow_two,
      Real.rpow_neg hX.le,Real.rpow_two]
    calc
      _ ≤ ((C1+D1/‖sigma‖^2)*((X/2)^2)⁻¹/(X/2))*X := by gcongr
      _ = _ := by field_simp; ring
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hh := add_le_add
    (mul_le_mul (hpq z hz r hrr).2 hb0 (norm_nonneg _) hQ)
    (mul_le_mul (hpq z hz r hrr).1 hb1 (by positivity) hP)
  exact hh.trans_eq (by ring)

/-- Joint W-argument and power freezing error. The estimate is linear
in the actual relative gap and keeps the original product scale. -/
theorem freeze_bound (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z sigma : ℂ, ‖z‖ ≤ Z → sigma ≠ 0 →
      ∀ X r : ℝ, 0 < X → r ∈ Icc (1/2:ℝ) (3/2) →
      ‖power z r*sourceW sigma (X*r)-sourceW sigma X‖ ≤
        (C+D/‖sigma‖^2)*X^(-2:ℝ)*|r-1| := by
  obtain ⟨C,D,hC,hD,hh⟩ := profile_derivative_bound Z
  refine ⟨C,D,hC,hD,?_⟩
  intro z sigma hz hs X r hX hrr
  have hd := fun r (hr : r ∈ Icc (1/2:ℝ) (3/2)) =>
    (profile_deriv z sigma X r hs hX (by linarith [hr.1])).hasDerivWithinAt
      (s := Icc (1/2:ℝ) (3/2))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun r hr => hh z sigma hz hs X r hX hr) (convex_Icc (1/2:ℝ) (3/2))
    (show (1:ℝ) ∈ Icc (1/2:ℝ) (3/2) by norm_num) hrr
  simpa [profile,power,Real.norm_eq_abs] using hm

def error (z sigma : ℂ) (X t u : ℝ) : ℂ :=
  power z (1+u)*sourceW sigma (X*(1+u))*exp (I*((t*Real.log (1+u):ℝ):ℂ))-
    sourceW sigma X*exp (I*((t*u:ℝ):ℂ))

/-- The amplitude and phase errors share one analytic mass. -/
theorem full_bound (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z sigma : ℂ, ‖z‖ ≤ Z → sigma ≠ 0 →
      ∀ X t u : ℝ, 0 < X → |u| ≤ 1/2 →
      ‖error z sigma X t u‖ ≤
        (C+D/‖sigma‖^2)*X^(-2:ℝ)*(|u|+|t| *u^2) := by
  obtain ⟨C,D,hC,hD,hf⟩ := freeze_bound Z
  obtain ⟨C0,D0,hC0,hD0,hw⟩ := source_all_decay 0 2 (by norm_num)
  refine ⟨C+2*C0,D+2*D0,by positivity,by positivity,?_⟩
  intro z sigma hz hs X t u hX hu
  have hrr : 1+u ∈ Icc (1/2:ℝ) (3/2) := by
    have hh := abs_le.mp hu
    constructor <;> linarith [hh.1,hh.2]
  have hf' := hf z sigma hz hs X (1+u) hX hrr
  simp only [add_sub_cancel_left] at hf'
  have hw' := hw sigma hs X hX
  simp only [iteratedDeriv_zero,pow_zero,div_one] at hw'
  have hp := PRZZPhaseError.phase_error t u hu
  have hzero : 0 ≤ C+D/‖sigma‖^2 := by positivity
  have hzero0 : 0 ≤ C0+D0/‖sigma‖^2 := by positivity
  have he : error z sigma X t u =
      (power z (1+u)*sourceW sigma (X*(1+u))-sourceW sigma X)*
        exp (I*((t*Real.log (1+u):ℝ):ℂ))+
      sourceW sigma X*(exp (I*((t*Real.log (1+u):ℝ):ℂ))-exp (I*((t*u:ℝ):ℂ))) := by
    unfold error; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_exp]
  simp only [mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,
    Real.exp_zero,mul_one]
  apply (add_le_add hf' (mul_le_mul hw' hp (norm_nonneg _) (by positivity))).trans
  calc
    _ ≤ ((C+D/‖sigma‖^2)+2*(C0+D0/‖sigma‖^2))*X^(-2:ℝ)*|u|+
        ((C+D/‖sigma‖^2)+2*(C0+D0/‖sigma‖^2))*X^(-2:ℝ)*(|t| *u^2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show C+D/‖sigma‖^2 ≤
            (C+D/‖sigma‖^2)+2*(C0+D0/‖sigma‖^2) by linarith) (by positivity)) (abs_nonneg u)
      · calc
          _ = (2*(C0+D0/‖sigma‖^2))*X^(-2:ℝ)*(|t| *u^2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (show 2*(C0+D0/‖sigma‖^2) ≤
              (C+D/‖sigma‖^2)+2*(C0+D0/‖sigma‖^2) by linarith) (by positivity)) (by positivity)
    _ = _ := by ring

theorem ratio_identity (m k u v delta : ℝ) (hmu : m*u ≠ 0)
    (hgap : m*u-k*v = -delta) : 1+delta/(m*u) = k*v/(m*u) := by
  calc
    _ = (m*u+delta)/(m*u) := by rw [add_div,div_self hmu]
    _ = _ := by congr 1; linarith

theorem product_identity (m k u v delta t : ℝ) (hm : 0 < m) (hu : 0 < u)
    (hv : 0 < v) (ht : 0 < t) (hgap : m*u-k*v = -delta) :
    (2*Real.pi*m^2*u/(t*v))*(1+delta/(m*u)) = 2*Real.pi*m*k/t := by
  rw [ratio_identity m k u v delta (mul_pos hm hu).ne' hgap]
  field_simp
  <;> ring

theorem power_product (z : ℂ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    power z (x*y) = power z x*power z y := by
  rw [power,Real.log_mul hx.ne' hy.ne',Complex.ofReal_add,mul_add,Complex.exp_add]
  rfl

/-- Exact identification with the two positive monomials occurring in
the W form of the AFE. Substituting a=1/2+alpha, b=1/2+beta retains both
original denominator powers. -/
theorem monomial_identity (a b sigma : ℂ) (m k u v delta t : ℝ)
    (hm : 0 < m) (hu : 0 < u) (hv : 0 < v) (ht : 0 < t)
    (hgap : m*u-k*v = -delta) (hsmall : |delta/(m*u)| ≤ 1/2) :
    power a m*power b k*sourceW sigma (2*Real.pi*m*k/t)*
        exp (I*((t*Real.log (k*v/(m*u)):ℝ):ℂ))-
      power a m*power b (m*u/v)*sourceW sigma (2*Real.pi*m^2*u/(t*v))*
        exp (I*((t*(delta/(m*u)):ℝ):ℂ)) =
      (power a m*power b (m*u/v))*
        error b sigma (2*Real.pi*m^2*u/(t*v)) t (delta/(m*u)) := by
  have hk0 : 0 < m*u/v := by positivity
  have hr : 0 < 1+delta/(m*u) := by linarith [(abs_le.mp hsmall).1]
  have hratio := ratio_identity m k u v delta (mul_pos hm hu).ne' hgap
  have hkr : (m*u/v)*(1+delta/(m*u)) = k := by
    rw [hratio]
    field_simp
  have hp : power b k = power b (m*u/v)*power b (1+delta/(m*u)) := by
    rw [← hkr,power_product b (m*u/v) (1+delta/(m*u)) hk0 hr]
  have hprod := product_identity m k u v delta t hm hu hv ht hgap
  rw [hp,← hprod,← hratio]
  unfold error
  ring

/-- Finite arithmetic masks retain one common product-weighted mass;
no extra cardinality of the index set is introduced. -/
theorem finite_bound {ι : Type*} (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z sigma : ℂ, ‖z‖ ≤ Z → sigma ≠ 0 →
      ∀ (s : Finset ι) (c : ι → ℂ) (X u : ι → ℝ) (t : ℝ),
      (∀ i ∈ s, 0 < X i) → (∀ i ∈ s, |u i| ≤ 1/2) →
      ‖∑ i ∈ s, c i*error z sigma (X i) t (u i)‖ ≤
        (C+D/‖sigma‖^2)*
          ∑ i ∈ s, ‖c i‖*(X i)^(-2:ℝ)*(|u i|+|t| *(u i)^2) := by
  obtain ⟨C,D,hC,hD,h⟩ := full_bound Z
  refine ⟨C,D,hC,hD,?_⟩
  intro z sigma hz hs s c X u t hX hu
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (h z sigma hz hs (X i) t (u i) (hX i hi) (hu i hi))
    (norm_nonneg _)).trans_eq (by ring)

/-- The ratio used by the freezing estimate is supplied by the original
cutoffs and gap, including its sign. -/
theorem actual_ratio (T M Q d eps delta m k u v : ℝ) (FM F1 : ℝ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hfm : FM m ≠ 0) (hf1 : F1 (d*u) ≠ 0)
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) (hgap : m*u-k*v = -delta) :
    |k*v/(m*u)-1| ≤ 4/T^(1-eps) ∧ |k*v/(m*u)-1| ≤ 1/2 := by
  have hm : 0 < m := (by positivity : 0 < M/2).trans_le (hsM hfm).1
  have hu : 0 < u := by nlinarith [(hs1 hf1).1]
  rw [← ratio_identity m k u v delta (mul_pos hm hu).ne' hgap,add_sub_cancel_left]
  exact ⟨PRZZCutoffPhase.support_ratio T M Q d eps delta m u FM F1
      hT hM hQ hd hsM hs1 hfm hf1 hdelta,
    PRZZCutoffPhase.support_small T M Q d eps delta m u FM F1
      hT hM hQ hd hsM hs1 hfm hf1 hdelta hheight⟩

/-- Integrate the combined freezing error with one common analytic
mass. R is the time-independent local product numerator, X=R/t.
The coefficient norms and reciprocal product squares are aggregated
before the time integral, without an index-cardinality factor. -/
theorem time_bound {ι : Type*} (Z : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z sigma : ℂ, ‖z‖ ≤ Z → sigma ≠ 0 →
      ∀ (s : Finset ι) (c : ι → ℂ) (R u : ι → ℝ) (T kappa : ℝ)
        (phi : ℝ → ℂ),
      0 < T → 0 ≤ kappa → Continuous phi →
      (∀ i ∈ s, 0 < R i) → (∀ i ∈ s, |u i| ≤ 1/2) →
      (∀ i ∈ s, |u i| ≤ kappa) →
      ‖∫ t in Icc T (2*T), phi t*∑ i ∈ s, c i*error z sigma (R i/t) t (u i)‖ ≤
        (C+D/‖sigma‖^2)*(kappa+2*T*kappa^2)*(2*T)^2*
          (∑ i ∈ s, ‖c i‖/(R i)^2)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,D,hC,hD,hh⟩ := finite_bound (ι := ι) Z
  refine ⟨C,D,hC,hD,?_⟩
  intro z sigma hz hs s c R u T kappa phi hT hk hphi hR hu huk
  let B := (C+D/‖sigma‖^2)*(kappa+2*T*kappa^2)*(2*T)^2*
    (∑ i ∈ s, ‖c i‖/(R i)^2)
  have hi : IntegrableOn (fun t => B*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  have hb : (∫ t in Icc T (2*T), ‖phi t*∑ i ∈ s, c i*error z sigma (R i/t) t (u i)‖) ≤
      ∫ t in Icc T (2*T), B*‖phi t‖ := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : 0 < t := hT.trans_le ht.1
    have hb := hh z sigma hz hs s c (fun i => R i/t) u t
      (fun i hi => div_pos (hR i hi) ht0) hu
    have hm : (∑ i ∈ s, ‖c i‖*(R i/t)^(-2:ℝ)*(|u i|+|t| *(u i)^2)) ≤
        ((kappa+2*T*kappa^2)*(2*T)^2)*(∑ i ∈ s, ‖c i‖/(R i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hRi := hR i hi
      have hui : (u i)^2 ≤ kappa^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg (u i)) hk).mpr (huk i hi)
        simpa only [sq_abs] using hh
      have he : (R i/t)^(-2:ℝ) = t^2/(R i)^2 := by
        rw [Real.rpow_neg (by positivity : 0 ≤ R i/t),Real.rpow_two]
        field_simp
      rw [he,abs_of_pos ht0]
      calc
        _ ≤ ‖c i‖*((2*T)^2/(R i)^2)*(kappa+2*T*kappa^2) := by
          gcongr <;> first | exact huk i hi | exact ht.2 | exact hui
        _ = _ := by ring
    rw [norm_mul,mul_comm B]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact hb.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by dsimp [B]; ring))
  exact hb.trans_eq (by rw [integral_const_mul])

/-- Uniformity for the actual logarithmically scaled shifts. Both the
complex-power shift and the source annihilator are substituted here. -/
theorem scaled_bound (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B : ℂ) (T X t u : ℝ),
      ‖B‖ ≤ S → r ≤ ‖A+B‖ → 1 ≤ Real.log T → 0 < X → |u| ≤ 1/2 →
      ‖error ((1/2:ℂ)+B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) X t u‖ ≤
        E*(1+(Real.log T)^2/r^2)*X^(-2:ℝ)*(|u|+|t| *u^2) := by
  obtain ⟨C,D,hC,hD,hh⟩ := full_bound (1/2+S)
  let E := C+D+1
  have hE : 0 < E := by dsimp [E]; linarith
  refine ⟨E,hE,?_⟩
  intro A B T X t u hB hsep hL hX hu
  have hL0 : 0 < Real.log T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hz : ‖(1/2:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/2+S := by
    apply (norm_add_le _ _).trans
    norm_num only [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hL0,norm_div,norm_one,Complex.norm_ofNat]
    have hb : ‖B‖/Real.log T ≤ S :=
      (div_le_self (norm_nonneg B) hL).trans hB
    linarith
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 :=
    div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have hc : ∀ sigma : ℂ, C+D/‖sigma‖^2 ≤ E*(1+1/‖sigma‖^2) := by
    intro sigma
    calc
      _ ≤ E+E/‖sigma‖^2 := add_le_add (by dsimp [E]; linarith)
        (div_le_div_of_nonneg_right (by dsimp [E]; linarith) (sq_nonneg _))
      _ = _ := by ring
  have hb := PRZZDiscardedSuppliers.log_shift_cap (fun sigma => C+D/‖sigma‖^2)
    E r hE.le hr hc A B (Real.log T) hL0.ne' hsep
  exact (hh _ _ hz hs X t u hX hu).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity))

#print axioms scaled_bound
#print axioms actual_ratio
#print axioms monomial_identity
#print axioms time_bound
#print axioms full_bound
#print axioms ratio_identity
#print axioms product_identity
#print axioms power_product
#print axioms finite_bound
#print axioms power_bounds
#print axioms profile_deriv
#print axioms profile_derivative_bound
#print axioms freeze_bound
end XiPrime8845.PRZZAmplitudeFreeze
