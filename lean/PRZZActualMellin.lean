import PRZZWindowDominance

/-! Fubini for the actual localized Mellin kernel. The cutoff window is
retained, and constants may depend on the fixed parameters. No DI bound
or uniform-in-height estimate is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex
namespace XiPrime8845.PRZZActualMellin
open PRZZAStar PRZZAStarMellin PRZZAStarWindow PRZZMellinSeparation
set_option maxHeartbeats 2000000

private def unitTwist (x t : ℝ) : ℂ :=
  Complex.exp ((Real.log x:ℂ)*(-((t:ℂ)*I)))

private theorem unitTwist_eq (x t : ℝ) (hx : 0 < x) : unitTwist x t = twist x t := by
  rw [unitTwist,twist,Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.ofReal_log hx.le]

private theorem unitTwist_norm (x t : ℝ) : ‖unitTwist x t‖ = 1 := by
  simp [unitTwist,Complex.norm_exp]

theorem amplitude_continuous (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    ContinuousOn (fun p : ℝ × ℝ => amplitude d a F1 F2 FM W α β p.1 p.2 z)
      (window N T A B) := by
  have hx : ∀ p ∈ window N T A B, 0 < p.1 :=
    fun p hp => (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
  have hy : ∀ p ∈ window N T A B, 0 < p.2 :=
    fun p hp => (div_pos hT (by positivity)).trans_le hp.2.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)^(α+β)) (window N T A B) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.cpow_const
      (fun p hp => by simpa using hx p hp)
  have hn : ∀ p ∈ window N T A B, (p.1:ℂ)^(α+β) ≠ 0 := fun p hp =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne'))
  unfold amplitude outerKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply continuousOn_const.mul
      apply ContinuousOn.div _ hc hn
      unfold PRZZKloostermanInputs.e; fun_prop
    · unfold PRZZKloostermanInputs.e; fun_prop
  · exact hW.comp_continuousOn ((continuousOn_const.mul continuous_fst.continuousOn).div
      continuous_snd.continuousOn (fun p hp => (hy p hp).ne'))

def localized (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
  (window N T A B).indicator
    (fun p => amplitude d a F1 F2 FM W α β p.1 p.2 z) p *
    mellin Phi (t*I) * (twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t)

theorem localized_integrable (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (Function.uncurry (localized N d T A B a F1 F2 FM W Phi α β z)) := by
  have hcompact : IsCompact (window N T A B) := isCompact_Icc.prod isCompact_Icc
  have hi : Integrable ((window N T A B).indicator
      (fun p : ℝ × ℝ => amplitude d a F1 F2 FM W α β p.1 p.2 z)) :=
    (integrable_indicator_iff hcompact.measurableSet).mpr
      ((amplitude_continuous N d T A B a F1 F2 FM W α β z
        hFM hW hN hT hA hB).integrableOn_compact hcompact)
  have hm : Integrable (fun t : ℝ => mellin Phi (t*I)) := by
    simpa [VerticalIntegrable] using
      PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hs hPhi
  let U := fun q : (ℝ × ℝ) × ℝ =>
    unitTwist (q.1.1*q.1.2/T) q.2*unitTwist z.1.1 q.2*unitTwist z.1.2 q.2
  have hU : Measurable U := by unfold U unitTwist; fun_prop
  have hUn : ∀ q, ‖U q‖ ≤ (1:ℝ) := by
    intro q; simp [U,unitTwist_norm]
  have hj := (hi.mul_prod hm).mul_bdd hU.aestronglyMeasurable (Filter.Eventually.of_forall hUn)
  apply hj.congr
  apply Filter.Eventually.of_forall
  intro q
  dsimp only [Function.uncurry,localized]
  by_cases hp : q.1 ∈ window N T A B
  · have hx : 0 < q.1.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
    have hy : 0 < q.1.2 := (div_pos hT (by positivity)).trans_le hp.2.1
    dsimp only [U]
    rw [unitTwist_eq _ _ (by positivity),unitTwist_eq _ _ (by exact_mod_cast hn1),
      unitTwist_eq _ _ (by exact_mod_cast hn2)]
  · simp [hp]

theorem localized_swap (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    (∫ p, ∫ t, localized N d T A B a F1 F2 FM W Phi α β z p t) =
      ∫ t, ∫ p, localized N d T A B a F1 F2 FM W Phi α β z p t :=
  integral_integral_swap (localized_integrable N d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hs hN hT hA hB hn1 hn2)

#print axioms amplitude_continuous
#print axioms localized_integrable
#print axioms localized_swap

/-- The entire original finite index set, not just a single summand.
All measurability and integrability inputs are supplied above. -/
theorem finite_swap (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    (∫ p, ∫ t, ∑ z ∈ indices N d D H,
      localized N d T A B a F1 F2 FM W Phi α β z p t) =
      ∫ t, ∫ p, ∑ z ∈ indices N d D H,
        localized N d T A B a F1 F2 FM W Phi α β z p t := by
  apply integral_integral_swap
  apply integrable_finsetSum
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact localized_integrable N d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hs hN hT hA hB
    (by have := (Finset.mem_Icc.mp hn.1).1; omega)
    (by have := (Finset.mem_Icc.mp hn.2).1; omega)

#print axioms finite_swap

/-- A supplied majorant, rather than an assumed bound on the actual kernel.
C is fixed before p and t; it may depend on the window and arithmetic data. -/
theorem localized_bound (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : Continuous W)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t,
      ‖localized N d T A B a F1 F2 FM W Phi α β z p t‖ ≤
        (window N T A B).indicator (fun _ => C) p * ‖mellin Phi (t*I)‖ := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (amplitude_continuous N d T A B a F1 F2 FM W α β z hFM hW hN hT hA hB)
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p t
  by_cases hp : p ∈ window N T A B
  · have hx : 0 < p.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
    have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hp.2.1
    simp only [localized,Set.indicator_of_mem hp,norm_mul,
      twist_norm _ _ (div_pos (mul_pos hx hy) hT),
      twist_norm (z.1.1:ℝ) t (by exact_mod_cast hn1),
      twist_norm (z.1.2:ℝ) t (by exact_mod_cast hn2),mul_one]
    exact mul_le_mul_of_nonneg_right ((hC p hp).trans (le_max_left _ _)) (norm_nonneg _)
  · simp [localized,hp]

#print axioms localized_bound
end XiPrime8845.PRZZActualMellin
