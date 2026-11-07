import PRZZSourceWDerivatives
import Zeta23.GammaFacts.StirlingVert

/-! Literal Gamma-ratio kernel of Pratt--Robles, arXiv:1706.04593v3,
(2.1)--(2.2). The uniform digamma estimate below is a supplied analytic
ingredient, not yet a bound on the integrated ratio or on V-sourceW.
Bochner integral definitions alone do not assert their integrability. -/
noncomputable section
open Complex MeasureTheory
namespace XiPrime8845.PRZZAFEGamma
open PRZZDyadicEnvelope

def gammaRatio (alpha beta s : ℂ) (t : ℝ) : ℂ :=
  (Real.pi:ℂ)^(-s) *
    (Complex.Gamma ((1/2+alpha+s+(t:ℂ)*I)/2) *
      Complex.Gamma ((1/2+beta+s-(t:ℂ)*I)/2)) /
    (Complex.Gamma ((1/2+alpha+(t:ℂ)*I)/2) *
      Complex.Gamma ((1/2+beta-(t:ℂ)*I)/2))

def kernel (alpha beta : ℂ) (x t : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v : ℝ,
    (x:ℂ)^(-(2+(v:ℂ)*I))*Complex.exp ((2+(v:ℂ)*I)^2)*
      annihilator (alpha+beta) (2+(v:ℂ)*I)/(2+(v:ℂ)*I)*
      gammaRatio alpha beta (2+(v:ℂ)*I) t

/-- Retain the decay discarded by the coarse Wu digamma envelope. -/
theorem digamma_error (T : ℝ) (w : ℂ) (hT : 2 ≤ T)
    (hw : 0 < w.re) (hi : T/4 ≤ |w.im|) :
    ‖Complex.digamma w-Complex.log w‖ ≤ 50/T := by
  have hT0 : 0 < T := by linarith
  have hh := Zeta23.StirlingVert.digamma_stirling hw (by linarith : 1/2 ≤ |w.im|)
  have hn : T/4 ≤ ‖w‖ := hi.trans (Complex.abs_im_le_norm w)
  have hnorm : 0 < ‖w‖ := by linarith
  have hsq : T^2/16 ≤ w.im^2 := by nlinarith [sq_abs w.im]
  have hs0 : 0 < w.im^2 := by nlinarith
  have h1 : ‖(1/2:ℂ)/w‖ ≤ 2/T := by
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    apply (div_le_iff₀ hnorm).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hT0).mpr
    nlinarith
  have h2 : 3/w.im^2 ≤ 48/T^2 := by
    apply (div_le_div_iff₀ hs0 (sq_pos_of_pos hT0)).mpr
    nlinarith
  have he : Complex.digamma w-Complex.log w =
      (Complex.digamma w-Complex.log w+(1/2:ℂ)/w)-(1/2:ℂ)/w := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hb := add_le_add (hh.trans h2) h1
  apply hb.trans
  apply (le_div_iff₀ hT0).mpr
  field_simp
  nlinarith

/-- Both signs of the height are covered. The central Mellin region is
explicit, as is the right-half-plane condition needed by Stirling. -/
theorem gamma_argument_error (T t : ℝ) (alpha s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ |t|) (ha : |alpha.im| ≤ T/4) (hs : |s.im| ≤ T/4)
    (hr : 0 < (1/2+alpha+s).re) :
    ‖Complex.digamma ((1/2+alpha+s+(t:ℂ)*I)/2) -
      Complex.log ((1/2+alpha+s+(t:ℂ)*I)/2)‖ ≤ 50/T := by
  apply digamma_error T _ hT
  · simpa using half_pos hr
  · have he : t = (alpha.im+s.im+t)-(alpha.im+s.im) := by ring
    have hh := abs_sub (alpha.im+s.im+t) (alpha.im+s.im)
    rw [← he] at hh
    have hc := abs_add_le alpha.im s.im
    simp only [Complex.div_ofNat_im,Complex.add_im,Complex.div_ofNat_im,
      Complex.one_im,zero_div,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
      Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith

#print axioms gamma_argument_error
#print axioms digamma_error
end XiPrime8845.PRZZAFEGamma
