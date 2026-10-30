import SmoothWeightWitness

/-! Separate interface for the audited fixed-positive-support localization.
`LocalizedEstimate` is a proposition, NOT a second axiom or a proved extension
of PRZZ. The original SmoothWeight and published-input axiom are unchanged.
All coefficients, cutoffs and shifts use the original height T. -/
noncomputable section
open MeasureTheory Filter
namespace XiPrime8845.PRZZLocalization

def SmoothWeightOn (a b : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Phi ∧ Function.support Phi ⊆ Set.Icc a b

def fullMass (Phi : ℝ → ℝ) : ℝ := ∫ u, Phi u

theorem old_weight_iff (Phi : ℝ → ℝ) :
    SmoothWeightOn 1 2 Phi ↔ PRZZ.SmoothWeight Phi := Iff.rfl

theorem compact_support {a b : ℝ} {Phi : ℝ → ℝ} (h : SmoothWeightOn a b Phi) :
    HasCompactSupport Phi :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal h.2 isClosed_Icc)

theorem integrable {a b : ℝ} {Phi : ℝ → ℝ} (h : SmoothWeightOn a b Phi) :
    Integrable Phi := h.1.continuous.integrable_of_hasCompactSupport (compact_support h)

theorem fullMass_eq {a b : ℝ} {Phi : ℝ → ℝ} (h : SmoothWeightOn a b Phi) :
    fullMass Phi = ∫ u in Set.Icc a b, Phi u := by
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by by_contra hh; exact hu (h.2 hh))

theorem scaled_support {a b T : ℝ} {Phi : ℝ → ℝ}
    (h : SmoothWeightOn a b Phi) (hT : 0 < T) (t : ℝ) (ht : Phi (t/T) ≠ 0) :
    t ∈ Set.Icc (a*T) (b*T) := by
  have hh := h.2 ht
  exact ⟨(le_div_iff₀ hT).mp hh.1, (div_le_iff₀ hT).mp hh.2⟩

theorem weighted_integrable {a b T : ℝ} {Phi : ℝ → ℝ}
    (h : SmoothWeightOn a b Phi) (hT : 0 < T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc (a*T) (b*T))) :
    Integrable (fun t => ‖f t‖^2*Phi (t/T)) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := Set.Icc (a*T) (b*T)) ?_).mp
  · exact ((hf.norm.pow 2).mul
      ((h.1.continuous.comp (continuous_id.div_const T)).continuousOn)).integrableOn_compact isCompact_Icc
  · intro t ht
    apply scaled_support h hT t
    intro hz
    exact ht (by simp [hz])

/-- Fixed a,b,Phi precede all asymptotic constants. No uniformity in a shrinking
smoothing width is requested. A supplier of this proposition is still needed. -/
def LocalizedEstimate : Prop :=
  ∀ a b : ℝ, 0 < a → a < b →
  ∀ P Q : PRZZ.Profiles, ∀ theta : ℝ, 0 < theta → theta < 4/7 →
  PRZZ.Subpower (PRZZ.coefficient P theta) → PRZZ.Subpower (PRZZ.coefficient Q theta) →
  ∀ Phi : ℝ → ℝ, SmoothWeightOn a b Phi →
  ∀ shiftBound poleGap eps : ℝ, 0 < shiftBound → 0 < poleGap → 0 < eps →
  ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
    ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
    ‖PRZZ.twistedMoment P Q theta T Phi A B-PRZZ.gcdMainTerm P Q theta T Phi A B‖ ≤
      C*Real.rpow T eps*(Real.rpow (PRZZ.length theta T) (7/4)+
        Real.rpow (PRZZ.length theta T) (7/8)*Real.rpow T (1/2))

#print axioms old_weight_iff
#print axioms compact_support
#print axioms integrable
#print axioms fullMass_eq
#print axioms scaled_support
#print axioms weighted_integrable
end XiPrime8845.PRZZLocalization
