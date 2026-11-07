import PRZZZeroGap
import PRZZSourceCutoffs

/-! Quantitative correspondence with the original Delta cutoff.
The physical spatial scale is M; after normalization the profile scale
is M/v and the reciprocal-phase denominator is u*v*x. The source cutoff
is substituted before taking arbitrary IBP powers. Outer coefficient
aggregation and the improper cosine Mellin evaluation are separate. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZZeroSourceHeight
open PRZZZeroGap PRZZCentralFubini
set_option maxHeartbeats 5000000

theorem cutoff_ratio (T M Q d eps : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 < Q) (hd : 0 < d) :
    M*Q/(d*(PRZZSourceCutoffs.deltaCutoff T M Q eps/d)*T) = T^(-eps) := by
  unfold PRZZSourceCutoffs.deltaCutoff
  rw [Real.rpow_sub hT,Real.rpow_one,Real.rpow_neg hT.le]
  field_simp

/-- Both the original u cutoff and the nonzero profile value determine
the actual reciprocal frequency. The constant 3 is the support width. -/
theorem source_phase_scale (T M Q d u v delta x eps : ℝ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hu : 0 < u) (hv : 0 < v) (hx : 0 < x)
    (huQ : d*u ≤ Q) (hxM : x ≤ 3*(M/v))
    (hgap : PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta|) :
    (u*v*x)/(|delta| * T) ≤ 3*T^(-eps) := by
  have hc : 0 < PRZZSourceCutoffs.deltaCutoff T M Q eps/d := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hg : 0 < |delta| := hc.trans_le hgap
  have hgeom : u*v*x ≤ 3*M*Q/d := by
    have h1 := mul_le_mul_of_nonneg_left hxM (mul_pos hu hv).le
    have h2 : u ≤ Q/d := (le_div_iff₀ hd).mpr (by simpa [mul_comm] using huQ)
    have he : u*v*(3*(M/v)) = 3*u*M := by field_simp <;> ring
    rw [he] at h1
    calc
      _ ≤ 3*u*M := h1
      _ ≤ 3*(Q/d)*M := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (3*M*Q/d)/(|delta| * T) := div_le_div_of_nonneg_right hgeom (by positivity)
    _ = 3*(M*Q/(d*|delta| * T)) := by ring
    _ ≤ 3*(M*Q/(d*(PRZZSourceCutoffs.deltaCutoff T M Q eps/d)*T)) := by gcongr
    _ = _ := by rw [cutoff_ratio T M Q d eps hT hM hQ hd]

/-- An actual nonzero spatial row gets T^(-n*eps) from n extra time
derivatives, while the two base derivatives keep the summable gap factor.
U is supplied by sourceW, before all heights and arithmetic scales. -/
theorem actual_row_gain (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      ∀ (n : ℕ) (F : ℝ → ℂ) (T M Q d u v delta x eps : ℝ) (sigma : ℂ),
      Function.support F ⊆ Icc (1/2:ℝ) 3 → sigma ≠ 0 →
      0 < T → 0 < M → 0 < Q → 0 < d → 0 < u → 0 < v → 0 < x → d*u ≤ Q →
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta| →
      ‖∫ t : ℝ, kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        ‖F ((M/v)⁻¹*x)‖*(x^(-(sigma.re+1))*U (n+2) sigma*
          ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
            (3*T^(-eps))^n) := by
  obtain ⟨U,hU,hb⟩ := core_decay Phi hPhi hcPhi hsPhi a ha
  refine ⟨U,hU,?_⟩
  intro n F T M Q d u v delta x eps sigma hF hs hT hM hQ hd hu hv hx huQ hgap
  have hUn := hU (n+2) sigma
  have hc : 0 < PRZZSourceCutoffs.deltaCutoff T M Q eps/d := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hd0 : delta ≠ 0 := abs_pos.mp (hc.trans_le hgap)
  rw [kernel_time,norm_mul]
  by_cases hz : F ((M/v)⁻¹*x) = 0
  · rw [hz,norm_zero,zero_mul,zero_mul]
  have hxM : x ≤ 3*(M/v) := (div_le_iff₀ (div_pos hM hv)).mp (by
    simpa only [div_eq_mul_inv,mul_comm] using (hF hz).2)
  have hp := source_phase_scale T M Q d u v delta x eps hT hM hQ hd hu hv hx huQ hxM hgap
  have hcore := hb (n+2) sigma T (u*v) delta x hs hT (mul_pos hu hv) hd0 hx
  have he : x^(-(sigma.re+1))*U (n+2) sigma*
      ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^(n+2)*(u*v*x)^(n+2)/|delta|^(n+2) =
      x^(-(sigma.re+1))*U (n+2) sigma*
        ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
          ((u*v*x)/(|delta| * T))^n := by
    simp only [pow_add,mul_pow,div_pow]
    field_simp
    <;> ring
  rw [he] at hcore
  apply (mul_le_mul_of_nonneg_left hcore (norm_nonneg _)).trans
  gcongr

/-- The factor 3^n is height independent. This is the explicit order
selection for a fixed polynomial prefactor, not an assumed error bound. -/
theorem source_tail_order (eps B A : ℝ) (heps : 0 < eps) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      T^B*(3*T^(-eps))^n ≤ C*T^(-A) := by
  obtain ⟨n,hn⟩ := PRZZSourceCutoffs.exists_tail_order 0 eps B A heps
  refine ⟨n,(3:ℝ)^n,by positivity,?_⟩
  intro T hT
  have hh := mul_le_mul_of_nonneg_left (hn T hT) (show 0 ≤ (3:ℝ)^n by positivity)
  simpa only [zero_sub,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms cutoff_ratio
#print axioms source_phase_scale
#print axioms actual_row_gain
#print axioms source_tail_order
end XiPrime8845.PRZZZeroSourceHeight
