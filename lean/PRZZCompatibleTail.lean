import PRZZLiteralAFEJoin

/-! Actual Fourier tails above a supplied common cutoff. The analytic
H^-n envelope, not the norm of a complex tail, is monotone. A concrete
cutoff covers every native dyadic row; no cancellation premise is used. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZCompatibleTail
set_option maxHeartbeats 3000000

def commonCutoff (N : ℕ) (T eH : ℝ) : ℕ := ⌈(N:ℝ)*T^eH⌉₊

theorem cutoff_dominates (N s v : ℕ) (T eH : ℝ) (hT : 0 < T) (hv : v ≤ N) :
    ⌈PRZZSourceCutoffs.poissonCutoff 1 T ((2:ℝ)^s) (v:ℝ) eH⌉₊ ≤ commonCutoff N T eH := by
  apply Nat.ceil_le_ceil
  unfold PRZZSourceCutoffs.poissonCutoff
  rw [one_mul]
  exact (div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hv) (Real.rpow_nonneg hT.le _))

/-- A larger common J has the same arbitrary-power tail bound, uniformly
in J. This is derived from the explicit derivative envelope at J. -/
theorem actual_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M t residue d Q1 : ℝ) (J : ℕ)
      (z : PRZZAStar.Index) (alpha beta : ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      0 < d → 0 < Q1 → Q1/2 ≤ d*z.1.1 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ ≤ J →
      ‖∑' j, PRZZFrozenTail.pair F M 1 residue z
        (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
        ((alpha+beta)/(Real.log T:ℂ)) J j t‖ ≤
        ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A)) := by
  obtain ⟨C,D,E,hc,hactual⟩ := PRZZFrozenProfileBound.actual_tail F hF hsF a ha
  obtain ⟨n,K,hK,h⟩ := PRZZUnitModulusBudget.source_tail_absorbed C D E a (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) r eD eH A hc ha.le (by positivity) hr heD he
  refine ⟨K,hK,?_⟩
  intro T M t residue d Q1 J z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta hJ
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have ht0 : 0 < t := hT0.trans_le ht.1
  have hu1 : (1:ℝ) ≤ z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hs : (alpha+beta)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  obtain ⟨hz,hp,hsi⟩ := PRZZUnitModulusBudget.sum_shift_envelopes T M b S r alpha beta hlog hM hMT hb hT0
    halpha hbeta hr hsep
  have hh := hactual n J M 1 residue t (8*T^eD) (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) ((Real.log T)^2/r^2) z
    (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    (by linarith) (by norm_num) ht0 hu hv hs (by positivity) (by positivity)
    (by simpa only [← add_div] using hz) (by simpa only [← add_div] using hp) hsi (by
      intro x hx
      exact PRZZSourceTailBudget.phase_radius T M Q1 d eD z.2.1 z.1.1 t x hT0
        (by linarith) hQ1 hd hx.1 hleft (by simpa [abs_of_pos ht0] using ht.2) hdelta)
  have hh' := h T M z.1.1 z.1.2 t z.1.2 hT hM hu1 hv0 hvT ht0 ht.2 hv0.le (by linarith)
  let B := (3*M-M/2)*(PRZZJetUniform.uniformCap C D E a
    (2*Real.pi*z.1.1/(t*z.1.2)) M (8*T^eD) (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) ((Real.log T)^2/r^2) (n+2)/(M/2)^(n+2))
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply mul_nonneg (by linarith)
    apply div_nonneg _ (by positivity)
    unfold PRZZJetUniform.uniformCap
    apply PRZZEnvelopeMass.convolution_nonneg
    · intro j
      apply PRZZEnvelopeMass.convolution_nonneg
      · intro k
        exact PRZZEnvelopeMass.convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity) k
      · intro i
        have hh := PRZZReciprocalJets.envelope_nonneg i 1 (by norm_num)
        positivity
    · intro i
      obtain ⟨hd,he⟩ := (hc i).2
      positivity
  have hpow : ((⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊:ℕ):ℝ)+1 ≤ (J:ℝ)+1 := by
    exact_mod_cast Nat.add_le_add_right hJ 1
  dsimp only at hh hh' ⊢
  apply hh.2.trans
  have hden : 2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*((J:ℝ)+1)^n)*PRZZWeightTail.squareMass ≤
      2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*
        (((⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊:ℕ):ℝ)+1)^n)*PRZZWeightTail.squareMass := by
    have hsquare : 0 ≤ PRZZWeightTail.squareMass := tsum_nonneg (fun j => by positivity)
    gcongr
  have hb := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*((z.1.2:ℝ)/M) by positivity)
  have hb' := mul_le_mul_of_nonneg_left hh'
    (norm_nonneg (exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))))
  have hb'' := hb.trans (by simpa only [B,mul_assoc] using hb')
  simpa only [B,← add_div,pow_two,one_mul] using hb''

/-- The actual central transfer band is bounded by the two proved tails,
at the local and the common cutoff, with one constant before all row data. -/
theorem central_band (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M t residue d Q1 : ℝ) (J : ℕ)
      (z : PRZZAStar.Index) (alpha beta : ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      0 < d → 0 < Q1 → Q1/2 ≤ d*z.1.1 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ ≤ J →
      ‖PRZZCentralTail.central F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
          ((alpha+beta)/(Real.log T:ℂ)) t J-
        PRZZCentralTail.central F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
          ((alpha+beta)/(Real.log T:ℂ)) t
            ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊‖ ≤
        ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A)) := by
  obtain ⟨K,hK,h⟩ := actual_tail F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨2*K,by positivity,?_⟩
  intro T M t residue d Q1 J z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta hJ
  have h1 := h T M t residue d Q1 J z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta hJ
  have h2 := h T M t residue d Q1 _ z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta le_rfl
  have hs : (alpha+beta)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  have hc := PRZZCentralTail.poisson_split F hF hsF M 1 residue t z
    (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) J
    (by linarith) (by norm_num) (by linarith [ht.1]) hu hv hs
  have hl := PRZZCentralTail.poisson_split F hF hsF M 1 residue t z
    (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊
    (by linarith) (by norm_num) (by linarith [ht.1]) hu hv hs
  have heq : PRZZCentralTail.central F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
      ((alpha+beta)/(Real.log T:ℂ)) t J-
      PRZZCentralTail.central F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
      ((alpha+beta)/(Real.log T:ℂ)) t ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ =
      (∑' j, PRZZFrozenTail.pair F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
        ((alpha+beta)/(Real.log T:ℂ)) ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ j t)-
      ∑' j, PRZZFrozenTail.pair F M 1 residue z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
        ((alpha+beta)/(Real.log T:ℂ)) J j t := by linear_combination hl-hc
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add h2 h1).trans_eq (by ring))

/-- Actual coefficients and time integration of the central transfer.
The remaining coefficient mass is displayed, not supplied as an estimate.
The time weight can be the genuine Gamma-weighted dual profile. -/
theorem band_time (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset PRZZAStar.Index) (c : PRZZAStar.Index → ℂ)
      (residue : PRZZAStar.Index → ℝ) (T M d Q1 : ℝ) (J : ℕ) (alpha beta : ℂ) (phi : ℝ → ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      0 < d → 0 < Q1 → Continuous phi →
      (∀ z ∈ s, 0 < z.1.1 ∧ 0 < z.1.2 ∧ (z.1.2:ℝ) ≤ T ∧ Q1/2 ≤ d*z.1.1 ∧
        |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d ∧
        ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ ≤ J) →
      ‖∫ t in Icc T (2*T), phi t*∑ z ∈ s, c z*
        (PRZZCentralTail.central F M 1 (residue z) z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
            ((alpha+beta)/(Real.log T:ℂ)) t J-
         PRZZCentralTail.central F M 1 (residue z) z (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
            ((alpha+beta)/(Real.log T:ℂ)) t ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊)‖ ≤
        ((∑ z ∈ s, ‖c z*exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖)*
          (K*T^(-A)))*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨K,hK,h⟩ := central_band F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro s c residue T M d Q1 J alpha beta phi hT hlog hM hMT hA hB hsep hd hQ hphi hdomain
  let C := (∑ z ∈ s, ‖c z*exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖)*(K*T^(-A))
  have hi : IntegrableOn (fun t => C*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul,mul_comm C]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    dsimp only [C]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro z hz
    obtain ⟨hu,hv,hvT,hleft,hgap,hcut⟩ := hdomain z hz
    have hh := h T M t (residue z) d Q1 J z alpha beta hT hlog hM hMT hu hv hvT ht
      hA hB hsep hd hQ hleft hgap hcut
    simpa only [norm_mul,mul_assoc] using mul_le_mul_of_nonneg_left hh (norm_nonneg (c z))

#print axioms band_time
#print axioms cutoff_dominates
#print axioms actual_tail
#print axioms central_band
end XiPrime8845.PRZZCompatibleTail
