import PRZZAStarIntegralBound

/-! Uniform outer common-window mass for a fixed continuous W.
N <= T and logarithmically small real shifts give a constant chosen before
N,d,T,alpha,beta. The resulting O(T/d) budget is explicit, not an optimal
PRZZ error estimate and not a bound for an unspecified T-dependent W. -/
noncomputable section
open scoped ContDiff
open Set MeasureTheory Complex
namespace XiPrime8845.PRZZOuterMass
open PRZZAStarWindow PRZZAStarIntegralBound
set_option maxHeartbeats 2000000

theorem ratio_mem (N : ℕ) (T A B : ℝ) (hN : 0 < N) (hT : 0 < T)
    (hA : 0 < A) (hB : 0 < B) (hNT : (N:ℝ) ≤ T) (p : ℝ × ℝ)
    (hp : p ∈ window N T A B) : 2*Real.pi*p.1/p.2 ∈ Icc 0 (2*Real.pi*B^2) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < p.1 := (div_pos hA hn).trans_le hp.1.1
  have hy : 0 < p.2 := (div_pos hT (mul_pos hB hn)).trans_le hp.2.1
  have hlow := (div_le_iff₀ (mul_pos hB hn)).mp hp.2.1
  have hby : 1 ≤ B*p.2 := by nlinarith
  refine ⟨by positivity, (div_le_iff₀ hy).mpr ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hp.1.2 (by positivity : 0 ≤ 2*Real.pi)
  have h2 := mul_le_mul_of_nonneg_left hby (by positivity : 0 ≤ 2*Real.pi*B)
  nlinarith

theorem log_bound (N : ℕ) (T A B x : ℝ) (hN : 0 < N) (_hT : 0 < T)
    (hA : 0 < A) (_hB : 0 < B) (hNT : (N:ℝ) ≤ T) (hx : x ∈ Icc (A/N) B) :
    |Real.log x| ≤ Real.log T+|Real.log A|+|Real.log B| := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := (div_pos hA hn).trans_le hx.1
  have hlo := Real.log_le_log (div_pos hA hn) hx.1
  rw [Real.log_div hA.ne' hn.ne'] at hlo
  have hhi := Real.log_le_log hx0 hx.2
  have hnt := Real.log_le_log hn hNT
  have hlt := Real.log_nonneg (hn1.trans hNT)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log A),abs_nonneg (Real.log B)],
    by linarith [le_abs_self (Real.log B),abs_nonneg (Real.log A)]⟩

theorem inv_power_bound (N : ℕ) (T A B S x : ℝ) (z : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hL : 1 ≤ Real.log T)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) (hNT : (N:ℝ) ≤ T)
    (hx : x ∈ Icc (A/N) B) (hz : |z.re| ≤ S/Real.log T) :
    ‖((x:ℂ)^z)⁻¹‖ ≤ Real.exp (S*(1+|Real.log A|+|Real.log B|)) := by
  have hx0 : 0 < x := (div_pos hA (by exact_mod_cast hN)).trans_le hx.1
  have hl := log_bound N T A B x hN hT hA hB hNT hx
  have hL0 : 0 < Real.log T := by linarith
  have hmul := mul_le_mul hz hl (abs_nonneg _) (div_nonneg hS hL0.le)
  have he : S/Real.log T*(Real.log T+|Real.log A|+|Real.log B|) ≤
      S*(1+|Real.log A|+|Real.log B|) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL0).mpr
    have hh := mul_le_mul_of_nonneg_left hL
      (mul_nonneg hS (add_nonneg (abs_nonneg (Real.log A)) (abs_nonneg (Real.log B))))
    nlinarith
  have hneg : -(Real.log x*z.re) ≤ S*(1+|Real.log A|+|Real.log B|) := by
    have hh := neg_le_abs (Real.log x*z.re)
    rw [abs_mul] at hh
    nlinarith [hmul.trans he]
  rw [norm_inv,Complex.norm_cpow_eq_rpow_re_of_pos hx0,Real.rpow_def_of_pos hx0,← Real.exp_neg]
  exact Real.exp_le_exp.mpr hneg

theorem window_volume_bound (N : ℕ) (T A B : ℝ) (hN : 0 < N)
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    volume.real (window N T A B) ≤ B*(2*T/A) := by
  rw [window,Measure.volume_eq_prod,measureReal_prod_prod,Real.volume_real_Icc,Real.volume_real_Icc]
  apply mul_le_mul
  · exact max_le (sub_le_self _ (by positivity)) hB.le
  · exact max_le (sub_le_self _ (by positivity)) (by positivity)
  · exact le_max_right _ _
  · exact hB.le

/-- All constants precede the arithmetic sizes and height. -/
theorem common_mass_uniform (W : ℝ → ℂ) (hW : Continuous W) (A B S : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ α β : ℂ,
      |(α+β).re| ≤ S/Real.log T →
      (∫ p, ‖common N d T A B W α β p‖) ≤ C*T/d := by
  obtain ⟨C0,hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW.continuousOn : ContinuousOn W (Icc 0 (2*Real.pi*B^2)))
  let C := max C0 0*Real.exp (S*(1+|Real.log A|+|Real.log B|))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C*B*2/A,by positivity,?_⟩
  intro N d hN hd T hT hL hNT α β hz
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hs : MeasurableSet (window N T A B) := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hc := common_integrable N d T A B W α β hW hN hd hT hA hB
  have hi : Integrable ((window N T A B).indicator (fun _ : ℝ × ℝ => C/d)) :=
    (integrable_indicator_iff hs).mpr (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
  have hb : ∀ p, ‖common N d T A B W α β p‖ ≤
      (window N T A B).indicator (fun _ => C/d) p := by
    intro p
    by_cases hp : p ∈ window N T A B
    · simp only [common,indicator_of_mem hp,div_eq_mul_inv,mul_inv,norm_mul,norm_inv,
        Complex.norm_natCast]
      have hw := (hC0 _ (ratio_mem N T A B hN hT hA hB hNT p hp)).trans (le_max_left C0 0)
      have hz' := inv_power_bound N T A B S p.1 (α+β) hN hT hL hA hB hS hNT hp.1 hz
      have hh := mul_le_mul hw hz' (norm_nonneg _) (le_max_right C0 0)
      simpa [C,norm_inv,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hd0.le)
    · simp [common,hp]
  calc
    _ ≤ ∫ p, (window N T A B).indicator (fun _ : ℝ × ℝ => C/d) p := integral_mono hc.norm hi hb
    _ = volume.real (window N T A B)*(C/d) := by rw [integral_indicator hs,setIntegral_const]; rfl
    _ ≤ (B*(2*T/A))*(C/d) := mul_le_mul_of_nonneg_right
      (window_volume_bound N T A B hN hT hA hB) (div_nonneg hC hd0.le)
    _ = _ := by ring

#print axioms ratio_mem
#print axioms log_bound
#print axioms inv_power_bound
#print axioms window_volume_bound
#print axioms common_mass_uniform

/-- The former unevaluated outer L1 cost is now supplied uniformly.
M is still the signed arithmetic-sum budget, not an assumed DI conclusion. -/
theorem literal_uniform (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ D H M : ℝ, 0 ≤ M →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (α β : ℂ),
      Continuous FM → Function.support FM ⊆ Icc A B → |(α+β).re| ≤ S/Real.log T →
      (∀ p ∈ window N T A B, ∀ t : ℝ,
        ‖PRZZAStarNu.signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ M) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi α β‖ ≤ C*(T/d)*M := by
  obtain ⟨C,hC,hmass⟩ := common_mass_uniform W hW A B S hA hB hS
  let L := ∫ t : ℝ, ‖mellin Phi (t*I)‖
  have hL : 0 ≤ L := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(1/(2*Real.pi))*C*L,by positivity,?_⟩
  intro N d hN hd T hT hlog hNT D H M hM a F1 F2 FM α β hFM hsM hz hb
  have hh := literal_bound N d D H T A B M a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hd hT hA hB hM hb
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmass N d hN hd T hT hlog hNT α β hz)
        (by positivity : 0 ≤ 1/(2*Real.pi))) hM) hL
  exact hh'.trans_eq (by dsimp [L]; ring)

#print axioms literal_uniform
end XiPrime8845.PRZZOuterMass
