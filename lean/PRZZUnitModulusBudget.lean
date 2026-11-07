import PRZZProfileTimeBudget
import PRZZExtendedTailDomain
import PRZZSourceTailBudget

/-! Suppliers for the source lattice: frozen modulus one, transformed modulus v. The positive lattice
support and source length bounds remain explicit. This does not identify
the complete AFE decomposition or discard the intermediate frequency band. -/
noncomputable section
open scoped ContDiff
open scoped BigOperators
open Set MeasureTheory
namespace XiPrime8845.PRZZUnitModulusBudget
set_option maxHeartbeats 2000000

theorem scales (T M u v t V : ℝ) (hT : 36 ≤ T) (hM : 1 ≤ 3*M)
    (hu : 1 ≤ u) (hv : 0 < v) (hvT : v ≤ T)
    (ht : 0 < t) (htT : t ≤ 2*T) (hV : V ≤ 2*T) :
    T^(-(4:ℝ)) ≤ (2*Real.pi*u/(t*v))*(M/2)^2 ∧
      v/M ≤ T^(3:ℝ) ∧ V/M ≤ T^(2:ℝ) := by
  have hM0 : 0 < M := by linarith
  refine ⟨(PRZZExtendedTailDomain.scales T M u v t v hT hM hu hv hvT
    ht htT hv.le hvT).1,?_,?_⟩
  · rw [Real.rpow_ofNat]
    have hh : v/M ≤ 3*T := (div_le_iff₀ hM0).mpr (by nlinarith)
    exact hh.trans (by nlinarith [sq_nonneg T])
  · rw [Real.rpow_ofNat]
    have hh : V/M ≤ 6*T := (div_le_iff₀ hM0).mpr (by nlinarith)
    exact hh.trans (by nlinarith)

theorem sum_shift_envelopes (T M b S r : ℝ) (A B : ℂ)
    (hlog : 1 ≤ Real.log T) (hM : 1 ≤ 3*M) (hMT : M ≤ T^b)
    (hb : 0 ≤ b) (hT : 0 < T) (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S)
    (hr : 0 < r) (hsep : r ≤ ‖A+B‖) :
    ‖(A+B)/(Real.log T:ℂ)‖ ≤ 2*S ∧
    ‖(A+B)/(Real.log T:ℂ)‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤
      (2*S)*(2*b+Real.log 2+3*Real.log 3) ∧
    1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ (Real.log T)^2/r^2 := by
  have hab : ‖A+B‖ ≤ 2*S := (norm_add_le _ _).trans (by linarith)
  simpa using PRZZExtendedTailDomain.shift_envelopes T M b (2*S) r (A+B) 0
    hlog hM hMT hb hT hab hr (by simpa using hsep)

theorem source_tail_absorbed (C D E : ℕ → ℝ) (a Z P r eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ T M u v t V : ℝ,
      36 ≤ T → 1 ≤ 3*M → 1 ≤ u → 0 < v → v ≤ T →
      0 < t → t ≤ 2*T → 0 ≤ V → V ≤ 2*T →
      let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M v eH⌉₊
      let B := (3*M-M/2)*(PRZZJetUniform.uniformCap C D E a
        (2*Real.pi*u/(t*v)) M (8*T^eD) Z P ((Real.log T)^2/r^2) (n+2)/(M/2)^(n+2))
      (V/M)*(2*B*v^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*
        PRZZWeightTail.squareMass) ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := PRZZProfileTimeBudget.full_tail_absorbed C D E a Z P r
    4 3 2 eD eH A hc ha hZ hr heD he
  refine ⟨n,K,hK,?_⟩
  intro T M u v t V hT hM hu hv hvT ht htT hV hVT
  obtain ⟨hk,hq,hv'⟩ := scales T M u v t V hT hM hu hv hvT ht htT hVT
  exact h T M v V (2*Real.pi*u/(t*v)) (by linarith) (by linarith)
    (by positivity) hV (by positivity) hk hq hv'

/-- The actual transformed Fourier tail. The source delta cutoff supplies
the reciprocal-phase bound, and both shifts supply the profile envelope. -/
theorem actual_tail_absorbed (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ T M t residue d Q1 : ℝ,
      ∀ z : PRZZAStar.Index, ∀ alpha beta : ℂ,
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < z.1.1 → 0 < z.1.2 → (z.1.2:ℝ) ≤ T → t ∈ Icc T (2*T) →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      0 < d → 0 < Q1 → Q1/2 ≤ d*z.1.1 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      let H : ℕ := ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊
      ‖∑' j, PRZZFrozenTail.pair F M 1 residue z
        (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ))
        ((alpha+beta)/(Real.log T:ℂ)) H j t‖ ≤
        ‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*
          (K*T^(-A)) := by
  obtain ⟨C,D,E,hc,hactual⟩ := PRZZFrozenProfileBound.actual_tail F hF hsF a ha
  obtain ⟨n,K,hK,h⟩ := source_tail_absorbed C D E a (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) r eD eH A hc ha.le (by positivity) hr heD he
  refine ⟨K,hK,?_⟩
  intro T M t residue d Q1 z alpha beta hT hlog hM hMT hu hv hvT ht halpha hbeta hsep
    hd hQ1 hleft hdelta
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := hT0.trans_le ht.1
  have hu1 : (1:ℝ) ≤ z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hs : (alpha+beta)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  obtain ⟨hz,hp,hsi⟩ := sum_shift_envelopes T M b S r alpha beta hlog hM hMT hb hT0
    halpha hbeta hr hsep
  have hh := hactual n ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊
    M 1 residue t (8*T^eD) (2*S)
    ((2*S)*(2*b+Real.log 2+3*Real.log 3)) ((Real.log T)^2/r^2) z
    (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    (by linarith) (by norm_num) ht0 hu hv hs (by positivity) (by positivity)
    (by simpa only [← add_div] using hz) (by simpa only [← add_div] using hp) hsi (by
      intro x hx
      exact PRZZSourceTailBudget.phase_radius T M Q1 d eD z.2.1 z.1.1 t x hT0
        (by linarith) hQ1 hd hx.1 hleft (by simpa [abs_of_pos ht0] using ht.2) hdelta)
  have hh' := h T M z.1.1 z.1.2 t z.1.2 hT hM hu1 hv0 hvT ht0 ht.2 hv0.le (by linarith)
  dsimp only at hh hh' ⊢
  apply hh.2.trans
  convert mul_le_mul_of_nonneg_left hh' (norm_nonneg
    (Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ)))) using 1 <;>
    simp only [← add_div, pow_two, one_mul] <;> ring

/-- Every retained original index supplies the arithmetic domain. Zero
prefactors can be pruned before applying the integrated bound. -/
theorem retained_conditions (N d : ℕ) (T M Q1 eD H : ℝ)
    (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hNT : (N:ℝ) ≤ T)
    (hF1 : Function.support F1 ⊆ Icc (Q1/2) (3*Q1))
    (hz : z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T M Q1 eD) H)
    (hn : PRZZAStar.prefactor a F1 F2 d alpha beta z ≠ 0) :
    0 < z.1.1 ∧ 0 < z.1.2 ∧ (z.1.2:ℝ) ≤ T ∧
      Q1/2 ≤ (d:ℝ)*z.1.1 ∧
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d := by
  have hz' := Finset.mem_product.mp hz
  have hpair := Finset.mem_product.mp (Finset.mem_filter.mp hz'.1).1
  have hu := Finset.mem_Icc.mp hpair.1
  have hv := Finset.mem_Icc.mp hpair.2
  have hdelta := (Finset.mem_filter.mp (Finset.mem_product.mp hz'.2).1).2
  have hf : F1 ((d:ℝ)*z.1.1) ≠ 0 := by
    intro hf
    apply hn
    simp [PRZZAStar.prefactor,hf]
  exact ⟨by omega,by omega,(by exact_mod_cast hv.2 : (z.1.2:ℝ) ≤ N).trans hNT,
    (hF1 hf).1,hdelta.2.le⟩

/-- Finite arithmetic families and the whole supported time interval.
No per-row tail-bound premise is used; the literal coefficient mass and
the complex-power multiplier are retained in the conclusion. -/
theorem integrated (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset PRZZAStar.Index) (c : PRZZAStar.Index → ℂ)
      (residue : PRZZAStar.Index → ℝ) (T M d Q1 : ℝ) (alpha beta : ℂ) (w : ℝ → ℂ),
      36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ → 0 < d → 0 < Q1 →
      Continuous w →
      (∀ z ∈ s, 0 < z.1.1 ∧ 0 < z.1.2 ∧ (z.1.2:ℝ) ≤ T ∧
        Q1/2 ≤ d*z.1.1 ∧ |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d) →
      ‖∫ t in Icc T (2*T), w t * ∑ z ∈ s, c z *
        ∑' j, PRZZFrozenTail.pair F M 1 (residue z) z
          (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
          ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ j t‖ ≤
      (∑ z ∈ s, ‖c z‖ *
        (‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*
          (K*T^(-A)))) * ∫ t in Icc T (2*T), ‖w t‖ := by
  obtain ⟨K,hK,h⟩ := actual_tail_absorbed F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro s c residue T M d Q1 alpha beta w hT hlog hM hMT halpha hbeta hsep hd hQ hw hrows
  simpa only [one_div_one,one_mul,mul_assoc] using
    PRZZExpandedCutoff.mass_time s c (fun _ => 1) (fun _ => 1)
      (fun z => ‖Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (z.1.2:ℝ):ℂ))‖*
        (K*T^(-A)))
      (fun z t => ∑' j, PRZZFrozenTail.pair F M 1 (residue z) z
        (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
        ⌈PRZZSourceCutoffs.poissonCutoff 1 T M (z.1.2:ℝ) eH⌉₊ j t)
      w hw T (2*T) (by
        intro t ht z hz
        obtain ⟨hu,hv,hvT,hleft,hdelta⟩ := hrows z hz
        simpa only [one_div_one,one_mul] using
          h T M t (residue z) d Q1 z alpha beta hT hlog hM hMT hu hv hvT ht
            halpha hbeta hsep hd hQ hleft hdelta)

#print axioms integrated
#print axioms retained_conditions
#print axioms actual_tail_absorbed
#print axioms scales
#print axioms sum_shift_envelopes
#print axioms source_tail_absorbed
end XiPrime8845.PRZZUnitModulusBudget

