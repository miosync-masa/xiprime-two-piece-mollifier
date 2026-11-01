import PRZZMellinTypeII

/-! Positive compact smooth cutoffs supply the Mellin hypotheses, rather than
assuming Mellin decay. The logarithmic pullback is Schwartz. This does not
construct the original dyadic partition or perform the remaining h summation. -/
noncomputable section
open scoped FourierTransform SchwartzMap ContDiff
open MeasureTheory Complex Set
namespace XiPrime8845.PRZZSmoothMellin
open PRZZMellinSeparation
set_option maxHeartbeats 1500000

def logPull (F : ℝ → ℂ) (u : ℝ) : ℂ := F (Real.exp (-u))

theorem logPull_support (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) :
    Function.support (logPull F) ⊆ Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hx := hs hu
  have hb : 0 < b := (Real.exp_pos _).trans_le hx.2
  have h1 := Real.log_le_log ha hx.1
  have h2 := Real.log_le_log (Real.exp_pos (-u)) hx.2
  rw [Real.log_exp] at h1 h2
  constructor <;> linarith

theorem logPull_compact (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) : HasCompactSupport (logPull F) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -Real.log b) (b := -Real.log a))
  intro x hx
  by_contra hn
  exact hx (logPull_support F a b ha hs hn)

def logSchwartz (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) : 𝓢(ℝ, ℂ) :=
  (logPull_compact F a b ha hs).toSchwartzMap (hf.comp (by fun_prop))

theorem mellin_fourier (F : ℝ → ℂ) (t : ℝ) :
    mellin F (t*I) = 𝓕 (logPull F) (t/(2*Real.pi)) := by
  change mellin F (t*I) = 𝓕 (fun u => F (Real.exp (-u))) (t/(2*Real.pi))
  simpa using (mellin_eq_fourier F (s := (t:ℂ)*I))

theorem vertical_integrable (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) :
    VerticalIntegrable (mellin F) 0 := by
  let g := logSchwartz F a b ha hs hf
  have hg : Integrable (𝓕 (g : ℝ → ℂ)) := (𝓕 g).integrable
  have h := hg.comp_mul_right' (show (2*Real.pi)⁻¹ ≠ 0 by positivity)
  simp only [VerticalIntegrable,Complex.ofReal_zero,zero_add,mellin_fourier]
  change Integrable (fun t : ℝ => 𝓕 (g : ℝ → ℂ) (t/(2*Real.pi)))
  simpa only [div_eq_mul_inv] using h

theorem mellin_convergent (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : Continuous F) : MellinConvergent F 0 := by
  have hi : IntegrableOn (fun x : ℝ => (x:ℂ)⁻¹ * F x) (Icc a b) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.mul _ hf.continuousOn
    exact Complex.continuous_ofReal.continuousOn.inv₀ (fun x hx => by
      exact_mod_cast (ha.trans_le hx.1).ne')
  have hz : ∀ x, x ∉ Icc a b → (x:ℂ)⁻¹*F x = 0 := by
    intro x hx
    have : F x = 0 := by contrapose! hx; exact hs hx
    simp [this]
  have h := (hi.integrable_of_forall_notMem_eq_zero hz).integrableOn (s := Ioi 0)
  simpa [MellinConvergent,smul_eq_mul,Complex.cpow_neg_one] using h

/-- Arbitrarily high polynomial decay, with a constant for the fixed cutoff. -/
theorem rapid_decay (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t|^k*‖mellin F (t*I)‖ ≤ C := by
  let g := logSchwartz F a b ha hs hf
  obtain ⟨C,hC,h⟩ := (𝓕 g).decay k 0
  refine ⟨(2*Real.pi)^k*C, by positivity, ?_⟩
  intro t
  have hh := h (t/(2*Real.pi))
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hh
  rw [mellin_fourier]
  have he : 𝓕 (logPull F) = ⇑(𝓕 g : 𝓢(ℝ, ℂ)) := rfl
  rw [he]
  have hp : 0 < (2*Real.pi)^k := by positivity
  rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi),div_pow] at hh
  exact ((div_le_iff₀ hp).mp (by simpa only [div_mul_eq_mul_div] using hh)).trans_eq
    (mul_comm C ((2*Real.pi)^k))

/-- Every positive scale now supplies all hypotheses of the separation API. -/
theorem scaled_rapid_decay (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ t : ℝ,
      |t|^k*‖mellin (scaledCutoff F N) (t*I)‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := rapid_decay F a b ha hs hf k
  refine ⟨C,hC,?_⟩
  intro N hN t
  rw [scaled_mellin_norm F N t hN]
  exact h t

theorem scaled_suppliers (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) (N : ℝ) (hN : 0 < N) :
    Continuous (scaledCutoff F N) ∧ MellinConvergent (scaledCutoff F N) 0 ∧
      VerticalIntegrable (mellin (scaledCutoff F N)) 0 := by
  refine ⟨hf.continuous.comp (continuous_const.mul continuous_id), ?_, ?_⟩
  · exact (MellinConvergent.comp_mul_left (inv_pos.mpr hN)).mpr
      (mellin_convergent F a b ha hs hf.continuous)
  · exact scaled_verticalIntegrable F N hN (vertical_integrable F a b ha hs hf)

/-- A fixed smooth cutoff costs one fixed constant, uniformly in its scale.
Only DI remains an analytic input to this positive-frequency block estimate. -/
theorem coupled_bound_smooth (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (ε : ℝ) (hε : 0 < ε) (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b) (hf : ContDiff ℝ ∞ F) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Finset.Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ d ∈ Finset.Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Finset.Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ N kappa : ℝ, 0 < N → 0 < kappa →
      ‖PRZZMellinTypeII.coupled C D U V rho r beta nu alpha (scaledCutoff F N) kappa‖ ≤
        K*(R*S*(P*Q)*PRZZKloostermanInputs.diBound ε C D U V rho) := by
  obtain ⟨K,hK,h⟩ := PRZZMellinTypeII.coupled_bound hDI ε hε
  let M : ℝ := (1/(2*Real.pi))*(∫ t : ℝ, ‖mellin F (t*I)‖)
  have hM : 0 ≤ M := mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨K*(M+1), by positivity, ?_⟩
  intro C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn hal N kappa hN hk
  obtain ⟨hc,hconv,hvert⟩ := scaled_suppliers F a b ha hs hf N hN
  have hh := h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    r beta nu alpha hr hb hn hal (scaledCutoff F N) hc hconv hvert kappa hk
  rw [scaled_mellin_mass F N hN] at hh
  have hx : 0 ≤ R*S*(P*Q)*PRZZKloostermanInputs.diBound ε C D U V rho := by
    have hC0 : 0 ≤ C := le_trans (by norm_num) hC
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    have hU0 : 0 ≤ U := le_trans (by norm_num) hU
    have hV0 : 0 ≤ V := le_trans (by norm_num) hV
    unfold PRZZKloostermanInputs.diBound
    apply mul_nonneg (by positivity)
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)))
  apply hh.trans
  change _ ≤ K*(M+1)*(R*S*(P*Q)*PRZZKloostermanInputs.diBound ε C D U V rho)
  dsimp [M]
  nlinarith [mul_nonneg hK.le hx]

#print axioms logPull_support
#print axioms logPull_compact
#print axioms vertical_integrable
#print axioms mellin_convergent
#print axioms rapid_decay
#print axioms scaled_rapid_decay
#print axioms scaled_suppliers
#print axioms coupled_bound_smooth
end XiPrime8845.PRZZSmoothMellin
