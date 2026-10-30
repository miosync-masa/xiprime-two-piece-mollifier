import WuAuxiliary
import Zeta23.GammaFacts.StirlingVert
import Mathlib.Analysis.Complex.Liouville

/-! Actual gamma factor and finite Stirling transfer for Wu's auxiliary.
All derivatives are in s with T held fixed. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.WuStirling
open WuAuxiliary Zeta23.XiPrime
set_option maxHeartbeats 2000000

def H (s : ℂ) : ℂ := s*(s-1)/2*Complex.Gammaℝ s
def V (T : ℝ) (s : ℂ) : ℂ := eta (Real.log T) s/H s
def jet (n : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  iteratedDeriv n H s/(H s*(Real.log T:ℂ)^n)

theorem H_ne_zero (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) : H s ≠ 0 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (by norm_num))
    (Complex.Gammaℝ_ne_zero_of_re_pos hs)

theorem H_analytic (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ H s := by
  exact (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const
    (by norm_num)).mul (Zeta23.RvM.Gammaℝ_analyticOnNhd s hs))

theorem H_deriv (s : ℂ) (hs : 0 < s.re) :
    deriv H s = (2*s-1)/2*Complex.Gammaℝ s+s*(s-1)/2*deriv Complex.Gammaℝ s := by
  have hp : HasDerivAt (fun z : ℂ => z*(z-1)/2) ((2*s-1)/2) s := by
    have hh := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    exact hh.congr_deriv (by simp only [id_eq]; ring)
  exact (hp.mul (Zeta23.WeilEF.differentiableAt_Gammaℝ hs).hasDerivAt).deriv

theorem H_logDeriv (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    deriv H s/H s = Lfn s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [H_deriv s hs]
  simp only [H,Lfn,logDeriv_apply]
  field_simp
  ring

theorem xi_eq (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    xi s = H s*riemannZeta s := by
  rw [xi_eq_Gammaℝ_mul_zeta hs h1]
  unfold H
  ring

theorem xi_leibniz (n : ℕ) (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    iteratedDeriv n xi s =
      ∑ j ∈ range (n+1), (n.choose j:ℂ)*iteratedDeriv j H s*
        iteratedDeriv (n-j) riemannZeta s := by
  have he : xi =ᶠ[𝓝 s] H*riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
      isOpen_compl_singleton.mem_nhds h1] with z hz hz1
    exact xi_eq z hz hz1
  rw [he.iteratedDeriv_eq n]
  exact iteratedDeriv_mul (H_analytic s hs).contDiffAt
    (analyticOn_riemannZeta s h1).contDiffAt

/-- The actual finite Leibniz expansion, before applying any asymptotic. -/
theorem V_expansion (T : ℝ) (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1)
    (hL : Real.log T ≠ 0) :
    V T s = ∑ n ∈ range 7, ∑ j ∈ range (n+1),
      (rCoeff n:ℂ)*(n.choose j:ℂ)*jet j T s*
        ZetaMomentIntegral.scaledZeta (n-j) T s := by
  have hH := H_ne_zero s hs h1
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL
  unfold V eta
  rw [sum_div]
  apply sum_congr rfl
  intro n hn
  rw [xi_leibniz n s hs h1,mul_sum,sum_div]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  have he : (Real.log T:ℂ)^n = (Real.log T:ℂ)^j*(Real.log T:ℂ)^(n-j) := by
    rw [← pow_add,Nat.add_sub_of_le hjn]
  unfold jet ZetaMomentIntegral.scaledZeta
  rw [he]
  field_simp

/-- Uniform complex, not merely real-part, digamma remainder. -/
theorem digamma_sub_log (w : ℂ) (hw : 0 < w.re) (hi : 1 ≤ |w.im|) :
    ‖Complex.digamma w-Complex.log w‖ ≤ 4 := by
  have hh := Zeta23.StirlingVert.digamma_stirling hw (by linarith)
  have hn : 1 ≤ ‖w‖ := hi.trans (Complex.abs_im_le_norm w)
  have hsq : 1 ≤ w.im^2 := by nlinarith [sq_abs w.im]
  have hrem : 3/w.im^2 ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hinv : ‖(1/2:ℂ)/w‖ ≤ 1/2 := by
    rw [norm_div]
    norm_num
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have he : Complex.digamma w-Complex.log w =
      (Complex.digamma w-Complex.log w+(1/2:ℂ)/w)-(1/2:ℂ)/w := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

/-- A dyadic logarithm comparison on a slightly enlarged strip, suitable
for later Cauchy circles. -/
theorem log_half_bound (T : ℝ) (s : ℂ) (hT : 4 ≤ T)
    (hr : 0 < s.re) (hr4 : s.re ≤ 4) (hi : T/2 ≤ s.im) (hi3 : s.im ≤ 3*T) :
    ‖Complex.log (s/2)-(Real.log T:ℂ)‖ ≤ Real.log 4+Real.pi := by
  have ht : 0 < T := by linarith
  have hsn : T/2 ≤ ‖s‖ := hi.trans ((le_abs_self _).trans (Complex.abs_im_le_norm s))
  have hsu : ‖s‖ ≤ 4*T := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hr,abs_of_nonneg (by linarith : 0 ≤ s.im)] at h
    linarith
  have hnorm : ‖s/2‖ = ‖s‖/2 := by simp
  have hlow : Real.log T-Real.log 4 ≤ Real.log ‖s/2‖ := by
    rw [← Real.log_div ht.ne' (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [hnorm]; linarith
  have hupp : Real.log ‖s/2‖ ≤ Real.log T+Real.log 4 := by
    rw [← Real.log_mul ht.ne' (by norm_num)]
    apply Real.log_le_log (by rw [hnorm]; linarith)
    rw [hnorm]; linarith
  have hre : |(Complex.log (s/2)-(Real.log T:ℂ)).re| ≤ Real.log 4 := by
    simp only [Complex.sub_re,Complex.log_re,Complex.ofReal_re]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have him : |(Complex.log (s/2)-(Real.log T:ℂ)).im| ≤ Real.pi := by
    simpa only [Complex.sub_im,Complex.log_im,Complex.ofReal_im,sub_zero] using
      Complex.abs_arg_le_pi (s/2)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

def firstConstant : ℝ := |Real.log Real.pi|/2+(4+Real.log 4+Real.pi)/2+2

theorem firstConstant_pos : 0 < firstConstant := by
  unfold firstConstant
  have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have := Real.pi_pos
  positivity

theorem Lfn_stirling_bound (T : ℝ) (s : ℂ) (hT : 4 ≤ T)
    (hr : 0 < s.re) (hr4 : s.re ≤ 4) (hi : T/2 ≤ s.im) (hi3 : s.im ≤ 3*T) :
    ‖Lfn s-(Real.log T:ℂ)/2‖ ≤ firstConstant := by
  have hsn : 1 ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    have := le_abs_self s.im
    linarith
  have hsm : 1 ≤ ‖s-1‖ := by
    have := Complex.abs_im_le_norm (s-1)
    have := le_abs_self s.im
    simp only [Complex.sub_im,Complex.one_im,sub_zero] at *
    linarith
  have hd := digamma_sub_log (s/2) (by simpa using half_pos hr)
    (by simp only [Complex.div_ofNat_im]; rw [abs_of_nonneg (by linarith)]; linarith)
  have hl := log_half_bound T s hT hr hr4 hi hi3
  have hp : ‖Complex.digamma (s/2)-(Real.log T:ℂ)‖ ≤ 4+Real.log 4+Real.pi :=
    (norm_sub_le_norm_sub_add_norm_sub _ (Complex.log (s/2)) _).trans (by linarith)
  have hi1 : ‖(1:ℂ)/s‖ ≤ 1 := by simpa only [norm_div,norm_one] using
    (div_le_one (by linarith : 0 < ‖s‖)).mpr hsn
  have hi2 : ‖(1:ℂ)/(s-1)‖ ≤ 1 := by simpa only [norm_div,norm_one] using
    (div_le_one (by linarith : 0 < ‖s-1‖)).mpr hsm
  rw [Lfn_eq_digamma hr]
  have he : -(Real.log Real.pi:ℂ)/2+(1/2:ℂ)*Complex.digamma (s/2)+1/s+1/(s-1)-
      (Real.log T:ℂ)/2 =
      -(Real.log Real.pi:ℂ)/2+(Complex.digamma (s/2)-(Real.log T:ℂ))/2+1/s+1/(s-1) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
  simp only [norm_div,norm_neg,norm_one,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat] at hi1 hi2 ⊢
  dsimp [firstConstant]
  linarith

theorem jet_one_bound (T : ℝ) (s : ℂ) (hT : 4 ≤ T)
    (hr : 0 < s.re) (hr4 : s.re ≤ 4) (hi : T/2 ≤ s.im) (hi3 : s.im ≤ 3*T) :
    ‖jet 1 T s-(1/2:ℂ)‖ ≤ firstConstant/Real.log T := by
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have h1 : s ≠ 1 := by intro h; simp [h] at hi; linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have he : jet 1 T s-(1/2:ℂ) = (Lfn s-(Real.log T:ℂ)/2)/(Real.log T:ℂ) := by
    simp only [jet,iteratedDeriv_one,pow_one,← div_div,H_logDeriv s hr h1]
    field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  exact div_le_div_of_nonneg_right (Lfn_stirling_bound T s hT hr hr4 hi hi3) hL.le

#print axioms H_ne_zero
#print axioms H_analytic
#print axioms H_deriv
#print axioms H_logDeriv
#print axioms xi_eq
#print axioms xi_leibniz
#print axioms V_expansion
#print axioms digamma_sub_log
#print axioms log_half_bound
#print axioms firstConstant_pos
#print axioms Lfn_stirling_bound
#print axioms jet_one_bound
end XiPrime8845.WuStirling

