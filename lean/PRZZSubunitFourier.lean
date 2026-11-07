import PRZZCompatibleTail

/-! All nonzero Fourier modes in the subunit local-frequency region.
The actual tail at cutoff zero is bounded from the explicit derivative
envelope. Replacing ceil(Hraw)+1 by 1 costs the fixed factor 2^n;
the differentiation order is selected before height and every row. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZSubunitFourier
set_option maxHeartbeats 7000000

theorem tail_zero (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M t residue d Q1 : ℝ)
      (z : PRZZAStar.Index) (alpha beta : ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      0 < d → 0 < Q1 → Q1/2 ≤ d*z.1.1 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH ≤ 1 →
      ‖∑' j, PRZZFrozenTail.pair F M 1 residue z
        (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
        ((alpha+beta)/(Real.log T:ℂ)) 0 j t‖ ≤
        ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A)) := by
  obtain ⟨C,D,E,hc,hactual⟩ := PRZZFrozenProfileBound.actual_tail F hF hsF a ha
  obtain ⟨n,K,hK,h⟩ := PRZZUnitModulusBudget.source_tail_absorbed C D E a (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) r eD eH A hc ha.le (by positivity) hr heD he
  refine ⟨(2:ℝ)^n*K,by positivity,?_⟩
  intro T M t residue d Q1 z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta hraw
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have ht0 : 0 < t := hT0.trans_le ht.1
  have hu1 : (1:ℝ) ≤ z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hs : (alpha+beta)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  obtain ⟨hz,hp,hsi⟩ := PRZZUnitModulusBudget.sum_shift_envelopes T M b S r alpha beta hlog hM hMT hb hT0
    halpha hbeta hr hsep
  have hh := hactual n 0 M 1 residue t (8*T^eD) (2*S)
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

  let q : ℝ := (⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊:ℕ)+1
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq : q ≤ 2 := by
    have hh : ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ ≤ 1 :=
      Nat.ceil_le.mpr (by simpa using hraw)
    dsimp [q]
    exact_mod_cast Nat.add_le_add_right hh 1
  have hsquare : 0 ≤ PRZZWeightTail.squareMass := tsum_nonneg (fun j => by positivity)
  dsimp only at hh hh' ⊢
  apply hh.2.trans
  have hden : 2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*((0:ℝ)+1)^n)*PRZZWeightTail.squareMass ≤
      (2:ℝ)^n*(2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*q^n)*PRZZWeightTail.squareMass) := by
    calc
      _ = q^n*(2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*q^n)*PRZZWeightTail.squareMass) := by
        field_simp
        simp
      _ ≤ _ := by gcongr
  have hb := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*((z.1.2:ℝ)/M) by positivity)
  have hb' := mul_le_mul_of_nonneg_left hh'
    (norm_nonneg (exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))))
  have hb'' := hb.trans (show
    ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*((z.1.2:ℝ)/M)*
      ((2:ℝ)^n*(2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*q^n)*PRZZWeightTail.squareMass)) ≤
    ‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*((2:ℝ)^n*K*T^(-A)) from by
    have hp := mul_le_mul_of_nonneg_left hb' (show 0 ≤ (2:ℝ)^n by positivity)
    calc
      _ = (2:ℝ)^n*(‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*
        ((z.1.2:ℝ)/M*(2*B*(z.1.2:ℝ)^(n+1)/((2*Real.pi)^(n+2)*q^n)*PRZZWeightTail.squareMass))) := by ring
      _ ≤ (2:ℝ)^n*(‖exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-A))) := by
        simpa only [q,B] using hp
      _ = _ := by ring)
  simpa only [B,← add_div,pow_two,one_mul,Nat.cast_zero,zero_add,one_pow,mul_assoc] using hb''

/-- Retain the zero mode exactly and estimate the actual remaining
central modes. Both the all-nonzero tail and the tail above J are proved
bounds; the subunit region is not declared to have no nonzero modes. -/
theorem central_zero (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH power : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T M t residue d Q : ℝ) (J : ℕ)
      (z : PRZZAStar.Index) (A B : ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      0 < d → 0 < Q → Q/2 ≤ d*z.1.1 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eD/d →
      PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH ≤ 1 →
      ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ ≤ J →
      ‖PRZZCentralTail.central F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          ((A+B)/(Real.log T:ℂ)) t J-
        PRZZCentralTail.central F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          ((A+B)/(Real.log T:ℂ)) t 0‖ ≤
        ‖exp (((A+B)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*(K*T^(-power)) := by
  obtain ⟨C0,hC0,h0⟩ := tail_zero F hF hsF a b S r eD eH power ha hb hS hr heD he
  obtain ⟨C1,hC1,h1⟩ := PRZZCompatibleTail.actual_tail F hF hsF a b S r eD eH power
    ha hb hS hr heD he
  refine ⟨C0+C1,by positivity,?_⟩
  intro T M t residue d Q J z A B hT hlog hM hMT hu hv hvT ht hA hB hsep hd hQ hleft hgap hraw hJ
  have hz := h0 T M t residue d Q z A B hT hlog hM hMT hu hv hvT ht hA hB hsep hd hQ hleft hgap hraw
  have hj := h1 T M t residue d Q J z A B hT hlog hM hMT hu hv hvT ht hA hB hsep hd hQ hleft hgap hJ
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  have hc := PRZZCentralTail.poisson_split F hF hsF M 1 residue t z
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) J
    (by linarith) (by norm_num) (by linarith [ht.1]) hu hv hs
  have hzero := PRZZCentralTail.poisson_split F hF hsF M 1 residue t z
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) 0
    (by linarith) (by norm_num) (by linarith [ht.1]) hu hv hs
  have heq : PRZZCentralTail.central F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      ((A+B)/(Real.log T:ℂ)) t J-
      PRZZCentralTail.central F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      ((A+B)/(Real.log T:ℂ)) t 0 =
      (∑' j, PRZZFrozenTail.pair F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
        ((A+B)/(Real.log T:ℂ)) 0 j t)-
      ∑' j, PRZZFrozenTail.pair F M 1 residue z (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
        ((A+B)/(Real.log T:ℂ)) J j t := by linear_combination hzero-hc
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hz hj).trans_eq (by ring))

#print axioms tail_zero
#print axioms central_zero
end XiPrime8845.PRZZSubunitFourier

