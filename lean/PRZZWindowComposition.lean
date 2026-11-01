import PRZZDyadicEnvelope

/-! Exact sharp-window composition with the original A*. Both indicators
survive Mellin inversion. All coprimality and strict frequency cutoffs are
those of signedSum; no Type I/II estimate is an input to this identity. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex Finset
namespace XiPrime8845.PRZZWindowComposition
open PRZZAStar PRZZActualMellin PRZZDyadicWindow PRZZAStarNu
set_option maxHeartbeats 2000000

theorem literal_windowed (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi)
    (hs1 : Function.support F1 ⊆ Set.Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Set.Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (box T M X V).indicator (fun p =>
          ∑ z ∈ indices N d D H,
            localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t) p := by
  let f := fun p t => ∑ z ∈ indices N d D H,
    localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t
  have his (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (Function.uncurry
        (localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z)) := by
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact localized_integrable N d T (M/2) (3*M) a F1 F2 FM W Phi α β z
      hFM hW hPhi hsP hN hT (by positivity) (by positivity)
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hi : Integrable (Function.uncurry f) := integrable_finsetSum _ his
  have hm : MeasurableSet (box T M X V) := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hj : Integrable (Function.uncurry (fun p t =>
      (box T M X V).indicator (fun p => f p t) p)) := by
    apply (hi.indicator (hm.preimage measurable_fst)).congr
    apply Filter.Eventually.of_forall
    intro q
    by_cases hp : q.1 ∈ box T M X V <;> simp [Function.uncurry,Set.indicator,hp]
  rw [PRZZAStarTransform.literal_mellin N d D H T (M/2) (3*M) a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hT (by positivity) (by positivity)]
  change (1/(2*Real.pi):ℂ)*(∫ t, ∫ p, f p t) = _
  rw [← integral_integral_swap hi,← integral_integral_swap hj,
    ← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  have hall : ∀ᵐ p, ∀ z ∈ indices N d D H,
      Integrable (fun t => localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t) :=
    (Filter.eventually_all_finset _).mpr (fun z hz => (his z hz).prod_right_ae)
  filter_upwards [hall] with p hip
  by_cases hp : p ∈ box T M X V
  · simp only [Set.indicator_of_mem hp]
  · simp only [Set.indicator_of_notMem hp,integral_zero,mul_zero]
    have hz (z : Index) (hzi : z ∈ indices N d D H) :
        kernel d T a F1 F2 FM W Phi α β z p.1 p.2 = 0 := by
      by_contra hh
      exact hp (support_box_of_cutoffs d T M X V a F1 F2 FM W Phi α β z
        hd hT hM hX hV hs1 hs2 hsM hsP hh)
    have hs : (1/(2*Real.pi):ℂ)*(∫ t, f p t) =
        ∑ z ∈ indices N d D H, kernel d T a F1 F2 FM W Phi α β z p.1 p.2 := by
      dsimp only [f]
      rw [integral_finsetSum _ hip,mul_sum]
      apply sum_congr rfl
      intro z hzi
      exact (PRZZAStarTransform.kernel_inversion N d D H T (M/2) (3*M) a
        F1 F2 FM W Phi α β z hPhi hsP hsM hN hT (by positivity) (by positivity) hzi p).symm
    rw [hs]
    exact sum_eq_zero hz

/-- Exact arithmetic form on the intersection of the two proven support
windows. Dropping either indicator after inversion is not claimed. -/
theorem literal_windowed_nu (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi)
    (hs1 : Function.support F1 ⊆ Set.Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Set.Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (box T M X V ∩ PRZZAStarWindow.window N T (M/2) (3*M)).indicator
          (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(α+β))) p *
        mellin Phi (t*I)*PRZZMellinSeparation.twist (p.1*p.2/T) t *
        signedSum N d D H a F1 F2 FM α β p.1 p.2 t := by
  rw [literal_windowed N d D H T M X V a F1 F2 FM W Phi α β
    hN hd hT hM hX hV hFM hW hPhi hs1 hs2 hsM hsP]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p ∈ box T M X V
  · rw [Set.indicator_of_mem hp,localized_nu]
    by_cases hw : p ∈ PRZZAStarWindow.window N T (M/2) (3*M) <;> simp [hp,hw]
  · simp [hp]

#print axioms literal_windowed
#print axioms literal_windowed_nu
end XiPrime8845.PRZZWindowComposition
