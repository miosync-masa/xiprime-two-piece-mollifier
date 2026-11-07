import PRZZNativeCentralLiteral

/-! The original retained field integrated in time: literal positive A*,
zero/negative modes, explicit rectangle rejection, and the actual four
other native parts plus valued cutoff complement. No remainder bound
or disappearance of a filter is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Finset
namespace XiPrime8845.PRZZKeptLiteral
open PRZZMellinSeparation PRZZRetainedNative PRZZNativeCentralLiteral
set_option maxHeartbeats 10000000

def dualProfile (Phi : ℝ → ℂ) (T : ℝ) (alpha beta : ℂ) (x : ℝ) : ℂ :=
  Phi x*PRZZAFEDual.dualMultiplier alpha beta (T*x)

/-- The exact dual time factor can be retained in the literal A* time
profile; no replacement of Gamma by a height power is used. -/
theorem dual_profile_regular (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) (T : ℝ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) :
    Continuous (dualProfile Phi T alpha beta) ∧
      Function.support (dualProfile Phi T alpha beta) ⊆ Set.Icc (1:ℝ) 2 := by
  have ar := abs_le.mp ((abs_re_le_norm alpha).trans ha)
  have br := abs_le.mp ((abs_re_le_norm beta).trans hb)
  have hg := PRZZMollifiedTime.dualMultiplier_continuous alpha beta
    (by linarith [ar.1]) (by linarith [ar.2]) (by linarith [br.1]) (by linarith [br.2])
  refine ⟨hPhi.mul (hg.comp (continuous_const.mul continuous_id)),?_⟩
  intro x hx
  exact hsPhi (fun hz => hx (by simp [dualProfile,hz]))

theorem dual_profile_time (Phi : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (alpha beta : ℂ) (t : ℝ) :
    dualProfile Phi T alpha beta (t/T) = Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t := by
  unfold dualProfile
  rw [show T*(t/T) = t by field_simp]

def remainderField (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  let seed := fun x => (P x:ℂ)
  let g := scaledCutoff G Q
  let h := scaledCutoff H V
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let part := fun which => selectedPart which L J N seed g h a
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t
  (PRZZAllPoissonRows.family L J N seed (fun _ => 1) (fun _ => 1) a alpha beta t-
    PRZZAllPoissonRows.family L J N seed g h a alpha beta t)+
    (part .tail-part .boundary+part .freeze+part .outside)

theorem kept_split (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t =
      selectedPart .central L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
      remainderField P G H js L J N T Q V eps alpha beta t := by
  rw [kept_decomposition]
  dsimp [remainderField]
  ring

theorem kept_time_literal (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t : ℝ, Phi (t/T)*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t) =
      (∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N,
        (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          2 T ((2:ℝ)^s) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (scaledCutoff G Q) (scaledCutoff H V) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
          Phi beta alpha (alpha+beta)+
         PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps) ((J:ℝ)+1) T
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
          (fun y => PRZZWRowLimit.profile (fun x => (P x:ℂ)) (((2:ℝ)^s)⁻¹*y))
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
         PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T ((2:ℝ)^s) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (scaledCutoff G Q) (scaledCutoff H V) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
          Phi beta alpha (alpha+beta)-
         ∫ t : ℝ, rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile (fun x => (P x:ℂ))) (scaledCutoff G Q) (scaledCutoff H V)
          Phi (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t))+
      ∫ t : ℝ, Phi (t/T)*remainderField P G H js L J N T Q V eps alpha beta t := by
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let seed := fun x => (P x:ℂ)
  let R := fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z
  let c := selectedPart .central L J N seed (scaledCutoff G Q) (scaledCutoff H V) a R alpha beta
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : seed x = 1 := by dsimp [seed]; simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : seed x = 0 := by dsimp [seed]; simp [hright x hx]
  have hp := PRZZWRowLimit.profile_regular seed hP hl hr
  have hc : Integrable (fun t => Phi (t/T)*c t) := by
    dsimp only [c,R]
    simp_rw [retained_central_cells]
    apply integrable_finsetSum; intro s hss
    apply integrable_finsetSum; intro d hd
    change Integrable (fun t => cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile seed) (scaledCutoff G Q) (scaledCutoff H V) Phi a alpha beta t)
    simp_rw [cell_rectangle]
    apply integrable_finsetSum; intro z hz
    by_cases hg : good L N d ((2:ℝ)^s) z
    · simp only [if_pos hg]
      have hz' := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
      exact term_integrable d J _ _ _ Phi a T _ alpha beta z hp.1.continuous hPhi hT
        (by positivity) (mem_Icc.mp hz'.1).1 (mem_Icc.mp hz'.2).1 hs hp.2.2 hsPhi
    · simp only [if_neg hg]; exact integrable_zero ℝ ℂ volume
  have hk : Integrable (fun t => Phi (t/T)*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t) := by
    have htime : Continuous (fun t : ℝ => Phi (t/T)) := hPhi.comp (continuous_id.div_const T)
    have hfield := PRZZPrunedAFEError.field_continuous L J N seed hP hl hr a alpha beta hs T hT
    have hsel := PRZZPrunedAFEError.selected_continuous L J N seed (scaledCutoff G Q) (scaledCutoff H V)
      hP hl hr a (PRZZSourceMaskFamily.discarded T Q eps) alpha beta hs T hT
    have hi : IntegrableOn (fun t => Phi (t/T)*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t)
        (Set.Icc T (2*T)) := (htime.continuousOn.mul (hfield.sub hsel)).integrableOn_compact isCompact_Icc
    apply hi.integrable_of_forall_notMem_eq_zero
    intro t ht
    have hz : Phi (t/T) = 0 := by
      by_contra hn
      have hh := hsPhi hn
      exact ht ⟨by have := (le_div_iff₀ hT).mp hh.1; linarith,
        by have := (div_le_iff₀ hT).mp hh.2; linarith⟩
    simp [hz]
  have hrem : Integrable (fun t => Phi (t/T)*remainderField P G H js L J N T Q V eps alpha beta t) := by
    apply (hk.sub hc).congr
    apply Filter.Eventually.of_forall; intro t
    dsimp only [Pi.sub_apply,c]
    rw [kept_split]
    ring
  have he : (∫ t : ℝ, Phi (t/T)*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t) =
      (∫ t : ℝ, Phi (t/T)*c t)+(∫ t : ℝ, Phi (t/T)*remainderField P G H js L J N T Q V eps alpha beta t) := by
    rw [← integral_add hc hrem]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall; intro t
    dsimp only [c]
    rw [kept_split]
    ring
  rw [he]
  congr 1
  exact retained_central_time L J N seed (scaledCutoff G Q) (scaledCutoff H V) Phi a
    hP hl hr hPhi hsPhi T Q eps hT alpha beta hs

#print axioms kept_split
#print axioms kept_time_literal
#print axioms dual_profile_regular
#print axioms dual_profile_time
end XiPrime8845.PRZZKeptLiteral
