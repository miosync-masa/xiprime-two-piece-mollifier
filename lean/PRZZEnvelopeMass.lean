import PRZZSourceTailBudget

/-! Explicit spatial mass budget. No supremum depending on height is used.
The power coefficient, shift singularity and phase polynomial remain visible.
This is not yet the optimized PRZZ exponent. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform
open MeasureTheory Set
namespace XiPrime8845.PRZZEnvelopeMass
open PRZZFullWeightJets
set_option maxHeartbeats 2000000

theorem convolution_nonneg (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hB : ∀ i, 0 ≤ B i) (n : ℕ) : 0 ≤ convolution A B n := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))

theorem convolution_mono (A B A' B' : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (ha : ∀ i, A i ≤ A' i) (hb : ∀ i, B i ≤ B' i) (n : ℕ) :
    convolution A B n ≤ convolution A' B' n := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i) (Nat.cast_nonneg _))
    (hb _) (hB _) (mul_nonneg (Nat.cast_nonneg _) ((hA i).trans (ha i)))

def cap (C D E : ℕ → ℝ) (a k M R L : ℝ) (z sigma : ℂ) (n : ℕ) : ℝ :=
  convolution (convolution (convolution C
    (fun i => ‖PRZZPowerJets.coeff z i‖*Real.exp (‖z‖*L)))
    (fun i => PRZZReciprocalJets.envelope i R))
    (fun i => (D i+E i/‖sigma‖^2)*(k*(M/2)^2)^(-a)) n

theorem cap_nonneg (C D E : ℕ → ℝ) (a k M R L : ℝ) (z sigma : ℂ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (hR : 0 ≤ R) (hk : 0 ≤ k) :
    0 ≤ cap C D E a k M R L z sigma n := by
  apply convolution_nonneg
  · apply convolution_nonneg
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
  · intro i; obtain ⟨hd,he⟩ := (hc i).2; positivity

theorem envelope_le_cap (C D E : ℕ → ℝ) (a k M x R L : ℝ) (z sigma : ℂ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i)
    (ha : 0 ≤ a) (hk : 0 < k) (hM : 0 < M) (hx : M/2 ≤ x)
    (hR : 0 ≤ R) (hlog : |Real.log x| ≤ L) :
    envelope C D E a k x R z sigma n ≤ cap C D E a k M R L z sigma n := by
  have hx0 : 0 < x := by linarith
  have hp : Real.exp (-z.re*Real.log x) ≤ Real.exp (‖z‖*L) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |z.re| * |Real.log x| := by simpa [abs_mul] using le_abs_self (-z.re*Real.log x)
      _ ≤ ‖z‖*L := mul_le_mul (Complex.abs_re_le_norm z) hlog (abs_nonneg _) (norm_nonneg _)
  have hw : (k*x^2)^(-a) ≤ (k*(M/2)^2)^(-a) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (by positivity) hx0.le |>.mpr hx) hk.le
  unfold envelope cap
  apply convolution_mono
  · apply convolution_nonneg
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
  · intro i; obtain ⟨hd,he⟩ := (hc i).2; positivity
  · intro i
    apply convolution_mono
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
    · intro j
      exact convolution_mono _ _ _ _ (fun i => (hc i).1) (fun i => by positivity)
        (fun i => le_rfl) (fun i => mul_le_mul_of_nonneg_left hp (norm_nonneg _)) j
    · exact fun i => le_rfl
  · intro i
    apply mul_le_mul_of_nonneg_left hw
    obtain ⟨hd,he⟩ := (hc i).2; positivity

/-- A computable finite convolution budget times the actual support width. -/
theorem integral_cap (C D E : ℕ → ℝ) (a k M R L : ℝ) (z sigma : ℂ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i)
    (ha : 0 ≤ a) (hk : 0 < k) (hM : 0 < M) (hR : 0 ≤ R)
    (hlog : ∀ x ∈ Icc (M/2) (3*M), |Real.log x| ≤ L) :
    (∫ x in Icc (M/2) (3*M), envelope C D E a k x R z sigma n/x^n) ≤
      (3*M-M/2)*(cap C D E a k M R L z sigma n/(M/2)^n) := by
  have hcap := cap_nonneg C D E a k M R L z sigma n hc hR hk.le
  have hpoint : ∀ x ∈ Icc (M/2) (3*M),
      envelope C D E a k x R z sigma n/x^n ≤
        cap C D E a k M R L z sigma n/(M/2)^n := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact (div_le_div_of_nonneg_right
      (envelope_le_cap C D E a k M x R L z sigma n hc ha hk hM hx.1 hR (hlog x hx))
      (by positivity)).trans (div_le_div_of_nonneg_left hcap (by positivity)
        (pow_le_pow_left₀ (by positivity) hx.1 n))
  have hn : ∀ x ∈ Icc (M/2) (3*M), 0 ≤ envelope C D E a k x R z sigma n/x^n := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    unfold envelope
    apply div_nonneg _ (pow_nonneg hx0 n)
    apply convolution_nonneg
    · apply convolution_nonneg
      · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
      · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
    · intro i; obtain ⟨hd,he⟩ := (hc i).2; positivity
  have hh := integral_mono_of_nonneg
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact hn x hx)
    (show IntegrableOn (fun _ : ℝ => cap C D E a k M R L z sigma n/(M/2)^n)
      (Icc (M/2) (3*M)) from continuousOn_const.integrableOn_compact isCompact_Icc)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact hpoint x hx)
  simpa [Real.volume_Icc, max_eq_left (by linarith : 0 ≤ 3*M-M/2)] using hh

/-- Logarithmic control is supplied by the endpoints, not assumed pointwise. -/
theorem support_log (M x : ℝ) (hM : 0 < M) (hx : x ∈ Icc (M/2) (3*M)) :
    |Real.log x| ≤ |Real.log (M/2)|+|Real.log (3*M)| := by
  have hx0 : 0 < x := by linarith [hx.1]
  have h1 := Real.log_le_log (by positivity : 0 < M/2) hx.1
  have h2 := Real.log_le_log hx0 hx.2
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (M/2)),abs_nonneg (Real.log (3*M))]
  · linarith [le_abs_self (Real.log (3*M)),abs_nonneg (Real.log (M/2))]

/-- The common analytic mass is supplied explicitly for every derivative order. -/
theorem mass_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (M k omega R : ℝ) (z sigma : ℂ),
      0 < M → 0 < k → 0 ≤ R → sigma ≠ 0 →
      (∀ x ∈ Icc (M/2) (3*M), |omega/x| ≤ R) →
      (∫ x, ‖iteratedDeriv n (PRZZFullWeightSmooth.weight F M k omega z sigma) x‖) ≤
        (3*M-M/2)*(cap C D E a k M R
          (|Real.log (M/2)|+|Real.log (3*M)|) z sigma n/(M/2)^n) := by
  obtain ⟨C,D,E,hpos,h⟩ := PRZZWeightFourier.mass_uniform (1/2) 3 (by norm_num) F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n M k omega R z sigma hM hk hR hsigma hp
  have hh := h n M k omega R z sigma hM hk hsigma (by simpa only [one_div_mul_eq_div] using hp)
  have he : (1/2:ℝ)*M = M/2 := by ring
  rw [he] at hh
  exact hh.trans (integral_cap C D E a k M R _ z sigma n hpos ha.le hk hM hR
    (fun x hx => support_log M x hM hx))

/-- Two-sided Poisson tail with no remaining spatial integral in its bound. -/
theorem tail_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (M k omega R q : ℝ) (z sigma : ℂ),
      0 < M → 0 < k → 0 ≤ R → 0 < q → sigma ≠ 0 →
      (∀ x ∈ Icc (M/2) (3*M), |omega/x| ≤ R) →
      let f := PRZZFullWeightSmooth.weight F M k omega z sigma
      let B := (3*M-M/2)*(cap C D E a k M R
        (|Real.log (M/2)|+|Real.log (3*M)|) z sigma (n+2)/(M/2)^(n+2))
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
      Summable tail ∧ (∑' j, tail j) ≤
        2*B*(q/(2*Real.pi))^(n+2)/((H:ℝ)+1)^n*PRZZWeightTail.squareMass := by
  obtain ⟨C,D,E,hpos,h⟩ := mass_bound F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H M k omega R q z sigma hM hk hR hq hsigma hp
  have ht := PRZZWeightTail.actual_tail (1/2) 3 (by norm_num) F hF M k omega z sigma hM hk hsigma hs n H q hq
  refine ⟨ht.1,ht.2.trans ?_⟩
  have hm := h (n+2) M k omega R z sigma hM hk hR hsigma hp
  rw [PRZZWeightFourier.mass_on_support (1/2) 3 (by norm_num) F M k omega z sigma hM hs (n+2)] at hm
  have hz : 0 ≤ PRZZWeightTail.squareMass := tsum_nonneg (fun j => by positivity)
  dsimp only at *
  gcongr

/-- Original Delta cutoff supplies the phase premise in the integral-free tail. -/
theorem source_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (T M Q d eps delta u v t q : ℝ) (z sigma : ℂ),
      0 < T → 0 < M → 0 < Q → 0 < d → 0 < v → 0 < t → 0 < q →
      Q/2 ≤ d*u → |t| ≤ 2*T →
      |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d → sigma ≠ 0 →
      let k := 2*Real.pi*u/(t*v)
      let f := PRZZFullWeightSmooth.weight F M k (delta*t/u) z sigma
      let B := (3*M-M/2)*(cap C D E a k M (8*T^eps)
        (|Real.log (M/2)|+|Real.log (3*M)|) z sigma (n+2)/(M/2)^(n+2))
      let tail := fun j : ℕ => ‖𝓕 f (((H+j:ℝ)+1)/q)‖+‖𝓕 f (-(((H+j:ℝ)+1)/q))‖
      Summable tail ∧ (∑' j, tail j) ≤
        2*B*(q/(2*Real.pi))^(n+2)/((H:ℝ)+1)^n*PRZZWeightTail.squareMass := by
  obtain ⟨C,D,E,hpos,h⟩ := tail_bound F hF hs a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H T M Q d eps delta u v t q z sigma hT hM hQ hd hv ht hq hu htt hdelta hsigma
  have hu0 : 0 < u := by nlinarith
  exact h n H M (2*Real.pi*u/(t*v)) (delta*t/u) (8*T^eps) q z sigma
    hM (by positivity) (by positivity) hq hsigma
    (fun x hx => PRZZSourceTailBudget.phase_radius T M Q d eps delta u t x
      hT hM hQ hd hx.1 hu htt hdelta)

#print axioms source_tail
#print axioms mass_bound
#print axioms tail_bound
#print axioms support_log
#print axioms integral_cap
#print axioms convolution_nonneg
#print axioms convolution_mono
#print axioms cap_nonneg
#print axioms envelope_le_cap
end XiPrime8845.PRZZEnvelopeMass
