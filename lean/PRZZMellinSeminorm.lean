import PRZZMellinMoment
import PRZZWeightFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A quantitative Mellin L1 estimate from finitely many ordinary jets
on the fixed positive support [1,2]. No cutoff-dependent Schwartz constant
is selected: the explicit logarithmic third derivative supplies decay. -/
noncomputable section
open scoped ContDiff FourierTransform Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZMellinSeminorm
open PRZZSmoothMellin PRZZMellinSeparation
set_option maxHeartbeats 8000000

def xlog (u : ℝ) : ℝ := Real.exp (-u)

theorem xlog_deriv (u : ℝ) : HasDerivAt (fun v => (xlog v:ℂ)) (-(xlog u:ℂ)) u := by
  simpa [xlog] using (((hasDerivAt_id u).neg.exp).ofReal_comp)

theorem pull_jet_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v => iteratedDeriv n f (xlog v))
      (-(xlog u:ℂ)*iteratedDeriv (n+1) f (xlog u)) u := by
  have hd : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f (xlog u)) (xlog u) := by
    rw [iteratedDeriv_succ]
    exact ((hf.of_le (by exact_mod_cast (le_top : ((n+1):ℕ∞) ≤ ⊤))).differentiable_iteratedDeriv' n).differentiableAt.hasDerivAt
  have hx : HasDerivAt xlog (-xlog u) u := by
    change HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) u
    simpa using (hasDerivAt_id u).neg.exp
  simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_neg] using hd.scomp u hx

theorem piece_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n k : ℕ) (u : ℝ) :
    HasDerivAt (fun v => (xlog v:ℂ)^(k+1)*iteratedDeriv n f (xlog v))
      (-((k+1:ℕ):ℂ)*(xlog u:ℂ)^(k+1)*iteratedDeriv n f (xlog u)-
        (xlog u:ℂ)^(k+2)*iteratedDeriv (n+1) f (xlog u)) u := by
  have h := ((xlog_deriv u).pow (k+1)).mul (pull_jet_deriv f hf n u)
  convert h using 1 <;> (try simp only [Pi.mul_apply,Pi.pow_apply,Nat.add_sub_cancel,pow_succ]) <;> first | rfl | ring

theorem log_first (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv 1 (logPull f) = fun u => -(xlog u:ℂ)*iteratedDeriv 1 f (xlog u) := by
  funext u
  rw [iteratedDeriv_one]
  change deriv (fun v => f (xlog v)) u = _
  simpa only [iteratedDeriv_zero,zero_add] using (pull_jet_deriv f hf 0 u).deriv

theorem log_second (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv 2 (logPull f) = fun u =>
      (xlog u:ℂ)*iteratedDeriv 1 f (xlog u)+(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u) := by
  rw [show 2 = 1+1 by norm_num,iteratedDeriv_succ,log_first f hf]
  funext u
  have h := (piece_deriv f hf 1 0 u).neg
  have he : HasDerivAt (fun v => -(xlog v:ℂ)*iteratedDeriv 1 f (xlog v))
      ((xlog u:ℂ)*iteratedDeriv 1 f (xlog u)+(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)) u := by
    convert h using 1 <;> (try simp only [Pi.neg_apply,pow_one,Nat.cast_one,one_mul]) <;>
      first | rfl | (funext v; dsimp; ring) | ring
  exact he.deriv

theorem log_third (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv 3 (logPull f) = fun u =>
      -(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)-
        3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)-
        (xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u) := by
  rw [show 3 = 2+1 by norm_num,iteratedDeriv_succ,log_second f hf]
  funext u
  have h := (piece_deriv f hf 1 0 u).add (piece_deriv f hf 2 1 u)
  have he : HasDerivAt (fun v => (xlog v:ℂ)*iteratedDeriv 1 f (xlog v)+
      (xlog v:ℂ)^2*iteratedDeriv 2 f (xlog v))
      (-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)-
        3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)-
        (xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u)) u := by
    convert h using 1 <;> (try simp only [Pi.add_apply,pow_one,Nat.cast_one,Nat.cast_ofNat,one_mul]) <;>
      first | rfl | (funext v; dsimp; ring) | ring
  exact he.deriv

def mass (f : ℝ → ℂ) (n : ℕ) : ℝ := ∫ u, ‖iteratedDeriv n (logPull f) u‖

theorem frequency_power (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (n : ℕ) (t : ℝ) :
    |t|^n*‖mellin f (t*I)‖ ≤ mass f n := by
  have hg : ContDiff ℝ ∞ (logPull f) := hf.comp (by fun_prop)
  have hc := logPull_compact f 1 2 (by norm_num) hs
  have hi (i : ℕ) : Integrable (iteratedDeriv i (logPull f)) :=
    (hg.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ hc i)
  have he := congrFun (Real.fourier_iteratedDeriv (N := ⊤) hg (fun i _ => hi i)
    (by simp : (n:ℕ∞) ≤ ⊤)) (t/(2*Real.pi))
  have hb := PRZZWeightFourier.norm_fourier_le (iteratedDeriv n (logPull f)) (t/(2*Real.pi))
  rw [he] at hb
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos Real.pi_pos,mul_one] at hb
  rw [mellin_fourier]
  have hp : 2*Real.pi*(|t|/|2*Real.pi|) = |t| := by
    rw [abs_of_pos (by positivity : 0 < 2*Real.pi)]
    field_simp
  rw [hp] at hb
  exact hb

theorem linear_pointwise (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (B : ℝ) (hB : 0 ≤ B)
    (h0 : mass f 0 ≤ B) (h3 : mass f 3 ≤ B) (t : ℝ) :
    (1+|t|)*‖mellin f (t*I)‖ ≤ 4*B*(1+t^2)⁻¹ := by
  have hzero : ‖mellin f (t*I)‖ ≤ B := by simpa using (frequency_power f hf hs 0 t).trans h0
  have hcube := (frequency_power f hf hs 3 t).trans h3
  have ht : 0 ≤ |t| := abs_nonneg t
  have hsq : t^2 = |t|^2 := (sq_abs t).symm
  rw [hsq]
  by_cases hh : |t| ≤ 1
  · apply (show (1+|t|)*‖mellin f (t*I)‖ ≤ 2*B by nlinarith [norm_nonneg (mellin f (t*I))]).trans
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1+|t|^2)).mpr
    nlinarith [mul_nonneg hB (show 0 ≤ 1-|t|^2 by nlinarith)]
  · have ht1 : 1 ≤ |t| := le_of_lt (lt_of_not_ge hh)
    have ht0 : 0 < |t| := by linarith
    have hp : |t| * ‖mellin f (t*I)‖ ≤ B/|t|^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ht0)).mpr
      nlinarith only [hcube]
    calc
      _ ≤ 2*(|t| * ‖mellin f (t*I)‖) := by nlinarith [norm_nonneg (mellin f (t*I))]
      _ ≤ 2*(B/|t|^2) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ (by positivity : 0 < 1+|t|^2)).mpr
        have hd : (B/|t|^2) * |t|^2 = B := by field_simp
        have hd' : B/|t|^2 ≤ B := div_le_self hB (by nlinarith)
        nlinarith

theorem linear_mass_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (B : ℝ) (hB : 0 ≤ B)
    (h0 : mass f 0 ≤ B) (h3 : mass f 3 ≤ B) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤
      4*B*(∫ t : ℝ, (1+t^2)⁻¹) := by
  have hi := integrable_inv_one_add_sq.const_mul (4*B)
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) hi
    (Filter.Eventually.of_forall (linear_pointwise f hf hs B hB h0 h3))).trans_eq
  exact integral_const_mul _ _

theorem log_jet_support (f : ℝ → ℂ) (hs : Function.support f ⊆ Icc (1:ℝ) 2) (n : ℕ) :
    tsupport (iteratedDeriv n (logPull f)) ⊆ Icc (-Real.log 2) 0 := by
  induction n with
  | zero =>
    apply closure_minimal _ isClosed_Icc
    simpa only [iteratedDeriv_zero,Real.log_one,neg_zero] using logPull_support f 1 2 (by norm_num) hs
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem mass_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (n : ℕ) (B : ℝ)
    (hb : ∀ u ∈ Icc (-Real.log 2) 0, ‖iteratedDeriv n (logPull f) u‖ ≤ B) :
    mass f n ≤ Real.log 2*B := by
  have hg : ContDiff ℝ ∞ (logPull f) := hf.comp (by fun_prop)
  have hi : Integrable (iteratedDeriv n (logPull f)) :=
    (hg.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ (logPull_compact f 1 2 (by norm_num) hs) n)
  have he : mass f n = ∫ u in Icc (-Real.log 2) 0, ‖iteratedDeriv n (logPull f) u‖ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : iteratedDeriv n (logPull f) u = 0 := by
      by_contra hh
      exact hu (log_jet_support f hs n (subset_closure hh))
    rw [hz,norm_zero]
  rw [he]
  have hh := setIntegral_mono_on hi.norm.integrableOn
    (show IntegrableOn (fun _ : ℝ => B) (Icc (-Real.log 2) 0) from continuous_const.integrableOn_Icc)
    measurableSet_Icc hb
  apply hh.trans_eq
  simp [setIntegral_const,Measure.real,Real.volume_Icc,smul_eq_mul,
    Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

theorem mass_from_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (U : ℕ → ℝ) (hU : ∀ n, 0 ≤ U n)
    (hu : ∀ n x, ‖iteratedDeriv n f x‖ ≤ U n) :
    mass f 0 ≤ Real.log 2*U 0 ∧
      mass f 3 ≤ Real.log 2*(2*U 1+12*U 2+8*U 3) := by
  have h1 := hU 1
  have h2 := hU 2
  have h3 := hU 3
  refine ⟨mass_le f hf hs 0 (U 0) (by intro u huu; exact hu 0 (xlog u)),?_⟩
  apply mass_le f hf hs 3
  intro u huu
  have hx : 0 < xlog u := Real.exp_pos _
  have hx2 : xlog u ≤ 2 := by
    have hh := Real.exp_le_exp.mpr (show -u ≤ Real.log 2 by linarith [huu.1])
    exact hh.trans_eq (Real.exp_log (by norm_num : (0:ℝ) < 2))
  rw [log_third f hf]
  dsimp only
  have hb : ‖-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)-
      3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)-(xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u)‖ ≤
      ‖-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)‖+
        ‖3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)‖+
        ‖(xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u)‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  apply hb.trans
  simp only [norm_mul,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx,Complex.norm_ofNat]
  calc
    _ ≤ xlog u*U 1+3*(xlog u)^2*U 2+(xlog u)^3*U 3 := by
      gcongr <;> apply hu
    _ ≤ 2*U 1+12*U 2+8*U 3 := by
      calc
        _ ≤ 2*U 1+3*2^2*U 2+2^3*U 3 := by gcongr
        _ = _ := by ring

/-- Quantitative fixed-support Sobolev-to-Mellin bound. -/
theorem uniform_mass_from_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1:ℝ) 2) (U : ℕ → ℝ) (hU : ∀ n, 0 ≤ U n)
    (hu : ∀ n x, ‖iteratedDeriv n f x‖ ≤ U n) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤
      4*(Real.log 2*(U 0+2*U 1+12*U 2+8*U 3))*(∫ t : ℝ, (1+t^2)⁻¹) := by
  have hm := mass_from_jets f hf hs U hU hu
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h0 := hU 0
  have h1 := hU 1
  have h2 := hU 2
  have h3 := hU 3
  apply linear_mass_bound f hf hs _ (by positivity)
  · nlinarith [hU 0,hU 1,hU 2,hU 3]
  · nlinarith [hU 0]

#print axioms xlog_deriv
#print axioms pull_jet_deriv
#print axioms piece_deriv
#print axioms log_first
#print axioms log_second
#print axioms log_third
#print axioms frequency_power
#print axioms linear_pointwise
#print axioms linear_mass_bound
#print axioms log_jet_support
#print axioms mass_le
#print axioms mass_from_jets
#print axioms uniform_mass_from_jets
end XiPrime8845.PRZZMellinSeminorm
