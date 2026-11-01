import PRZZWindowComposition
import PRZZSourceWOuter

/-! Positive-argument continuity suffices for the exact literal A* transform.
Both original support indicators are retained. No arithmetic bound is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex Finset
namespace XiPrime8845.PRZZPositiveMellin
open PRZZAStar PRZZAStarWindow PRZZAStarMellin PRZZActualMellin
open PRZZMellinSeparation PRZZDyadicWindow PRZZAStarNu PRZZAStarTransform
open PRZZKloostermanInputs
set_option maxHeartbeats 2000000

theorem kernel_integrable_positive (d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0)) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc A B)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) := by
  have h1 : (0:ℝ) < z.1.1 := by exact_mod_cast hn1
  have h2 : (0:ℝ) < z.1.2 := by exact_mod_cast hn2
  let s := Icc (A/z.1.2) (B/z.1.2) ×ˢ Icc (T/(B*z.1.1)) (2*T/(A*z.1.1))
  have hs : Function.support (fun p : ℝ × ℝ =>
      kernel d T a F1 F2 FM W Phi α β z p.1 p.2) ⊆ s := by
    intro p hp
    have hm : FM (p.1*z.1.2) ≠ 0 := by
      intro hz; exact hp (by simp [kernel,outerKernel,hz])
    have hph : Phi (p.1*p.2*z.1.1*z.1.2/T) ≠ 0 := by
      intro hz; exact hp (by simp [kernel,innerKernel,hz])
    have hm' := hsM hm
    have hp' := hsP hph
    have hx : 0 < p.1 := by nlinarith [hm'.1]
    have hy : 0 < p.2 := by
      have hh := (le_div_iff₀ hT).mp hp'.1
      have : 0 < p.1*p.2*z.1.1*z.1.2 := by linarith
      by_contra hn
      have hh' := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hx.le (le_of_not_gt hn)) h1.le) h2.le
      linarith
    refine ⟨⟨(div_le_iff₀ h2).mpr hm'.1,(le_div_iff₀ h2).mpr hm'.2⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ (mul_pos hB h1)).mpr
      have hh := (le_div_iff₀ hT).mp hp'.1
      have hb := mul_le_mul_of_nonneg_right hm'.2 (mul_pos hy h1).le
      nlinarith
    · apply (le_div_iff₀ (mul_pos hA h1)).mpr
      have hh := (div_le_iff₀ hT).mp hp'.2
      have ha := mul_le_mul_of_nonneg_right hm'.1 (mul_pos hy h1).le
      nlinarith
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hx : ∀ p ∈ s, 0 < p.1 := fun p hp => (div_pos hA h2).trans_le hp.1.1
  have hy : ∀ p ∈ s, 0 < p.2 := fun p hp => (div_pos hT (mul_pos hB h1)).trans_le hp.2.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)^(α+β)) s :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.cpow_const
      (fun p hp => by simpa using (hx p hp))
  have hn : ∀ p ∈ s, (p.1:ℂ)^(α+β) ≠ 0 := fun p hp =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne'))
  unfold kernel outerKernel innerKernel
  apply ContinuousOn.mul
  · apply continuousOn_const.mul
    apply ContinuousOn.div _ hc hn
    unfold e
    fun_prop
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · unfold e; fun_prop
      · apply hW.comp
        · exact (continuousOn_const.mul continuous_fst.continuousOn).div
            continuous_snd.continuousOn (fun p hp => (hy p hp).ne')
        · intro p hp
          exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hx p hp)) (hy p hp)
    · fun_prop

theorem amplitude_continuous_positive (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
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
  · exact hW.comp ((continuousOn_const.mul continuous_fst.continuousOn).div
      continuous_snd.continuousOn (fun p hp => (hy p hp).ne')) (by
      intro p hp
      exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hx p hp)) (hy p hp))

private def positiveUnitTwist (x t : ℝ) : ℂ :=
  Complex.exp ((Real.log x:ℂ)*(-((t:ℂ)*I)))
private theorem positiveUnitTwist_eq (x t : ℝ) (hx : 0 < x) : positiveUnitTwist x t = twist x t := by
  rw [positiveUnitTwist,twist,Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.ofReal_log hx.le]
private theorem positiveUnitTwist_norm (x t : ℝ) : ‖positiveUnitTwist x t‖ = 1 := by
  simp [positiveUnitTwist,Complex.norm_exp]

theorem localized_integrable_positive (N d : ℕ) (T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (Function.uncurry (PRZZActualMellin.localized N d T A B a F1 F2 FM W Phi α β z)) := by
  have hcompact : IsCompact (window N T A B) := isCompact_Icc.prod isCompact_Icc
  have hi : Integrable ((window N T A B).indicator
      (fun p : ℝ × ℝ => amplitude d a F1 F2 FM W α β p.1 p.2 z)) :=
    (integrable_indicator_iff hcompact.measurableSet).mpr
      ((amplitude_continuous_positive N d T A B a F1 F2 FM W α β z
        hFM hW hN hT hA hB).integrableOn_compact hcompact)
  have hm : Integrable (fun t : ℝ => mellin Phi (t*I)) := by
    simpa [VerticalIntegrable] using
      PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hs hPhi
  let U := fun q : (ℝ × ℝ) × ℝ =>
    positiveUnitTwist (q.1.1*q.1.2/T) q.2*positiveUnitTwist z.1.1 q.2*positiveUnitTwist z.1.2 q.2
  have hU : Measurable U := by unfold U positiveUnitTwist; fun_prop
  have hUn : ∀ q, ‖U q‖ ≤ (1:ℝ) := by
    intro q; simp [U,positiveUnitTwist_norm]
  have hj := (hi.mul_prod hm).mul_bdd hU.aestronglyMeasurable (Filter.Eventually.of_forall hUn)
  apply hj.congr
  apply Filter.Eventually.of_forall
  intro q
  dsimp only [Function.uncurry,PRZZActualMellin.localized]
  by_cases hp : q.1 ∈ window N T A B
  · have hx : 0 < q.1.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
    have hy : 0 < q.1.2 := (div_pos hT (by positivity)).trans_le hp.2.1
    dsimp only [U]
    rw [positiveUnitTwist_eq _ _ (by positivity),positiveUnitTwist_eq _ _ (by exact_mod_cast hn1),
      positiveUnitTwist_eq _ _ (by exact_mod_cast hn2)]
  · simp [hp]

theorem finite_swap_positive (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    (∫ p, ∫ t, ∑ z ∈ indices N d D H,
      PRZZActualMellin.localized N d T A B a F1 F2 FM W Phi α β z p t) =
      ∫ t, ∫ p, ∑ z ∈ indices N d D H,
        PRZZActualMellin.localized N d T A B a F1 F2 FM W Phi α β z p t := by
  apply integral_integral_swap
  apply integrable_finsetSum
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact localized_integrable_positive N d T A B a F1 F2 FM W Phi α β z
    hFM hW hPhi hs hN hT hA hB
    (by have := (Finset.mem_Icc.mp hn.1).1; omega)
    (by have := (Finset.mem_Icc.mp hn.2).1; omega)

theorem literal_mellin_positive (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t, ∫ p : ℝ × ℝ,
        ∑ z ∈ indices N d D H, PRZZActualMellin.localized N d T A B a F1 F2 FM W Phi α β z p t := by
  have hi (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi α β z p.1 p.2) := by
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact kernel_integrable_positive d T A B a F1 F2 FM W Phi α β z
      hFM hW hPhi.continuous hsM hsP hA hB hT
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hz0 (z : Index) (hz : z ∈ indices N d D H) (x : ℝ) (hx : x ∉ Set.Ioi (0:ℝ)) :
      (∫ y, kernel d T a F1 F2 FM W Phi α β z x y) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change kernel d T a F1 F2 FM W Phi α β z x y = 0
    have hp : (x,y) ∉ window N T A B := by
      intro hh
      exact hx ((div_pos hA (by exact_mod_cast hN)).trans_le hh.1.1)
    have hh := congrFun (indicator_kernel N d D H T A B a F1 F2 FM W Phi α β z
      hsM hsP hA hB hT hz) (x,y)
    simpa only [Set.indicator_of_notMem hp] using hh.symm
  have he : literal N d D H T a F1 F2 FM W Phi α β =
      ∫ p : ℝ × ℝ, ∑ z ∈ indices N d D H, kernel d T a F1 F2 FM W Phi α β z p.1 p.2 := by
    rw [literal_eq_sum_integrals,integral_finsetSum _ hi]
    apply sum_congr rfl
    intro z hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hz0 z hz)]
    exact (integral_prod _ (hi z hz)).symm
  rw [he,← finite_swap_positive N d D H T A B a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hN hT hA hB,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [integral_finsetSum]
  · rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    exact kernel_inversion N d D H T A B a F1 F2 FM W Phi α β z hPhi hsP hsM hN hT hA hB hz p
  · intro z hz
    unfold PRZZActualMellin.localized
    by_cases hp : p ∈ window N T A B
    · have hx : 0 < p.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
      have hy : 0 < p.2 := (div_pos hT (by positivity)).trans_le hp.2.1
      have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
      have h1 : (0:ℝ) < z.1.1 := by exact_mod_cast (show 0 < z.1.1 by have := (mem_Icc.mp hn.1).1; omega)
      have h2 : (0:ℝ) < z.1.2 := by exact_mod_cast (show 0 < z.1.2 by have := (mem_Icc.mp hn.2).1; omega)
      have hh := (PRZZMellinSeparation.kernel_integrable Phi
        (PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hsP hPhi)
        (p.1*p.2/T*z.1.1*z.1.2) (by positivity)).const_mul
        (amplitude d a F1 F2 FM W α β p.1 p.2 z)
      have ht (t : ℝ) : twist (p.1*p.2/T*z.1.1*z.1.2) t =
          twist (p.1*p.2/T) t*twist z.1.1 t*twist z.1.2 t := by
        rw [twist_mul _ _ _ (by positivity) h2.le,
          twist_mul _ _ _ (by positivity) h1.le]
      simp_rw [ht] at hh
      simpa only [Set.indicator_of_mem hp,mul_assoc] using hh
    · simp only [Set.indicator_of_notMem hp,zero_mul]
      exact integrable_zero _ _ _

theorem literal_windowed_positive (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi)
    (hs1 : Function.support F1 ⊆ Set.Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Set.Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM W Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (box T M X V).indicator (fun p =>
          ∑ z ∈ indices N d D H,
            PRZZActualMellin.localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t) p := by
  let f := fun p t => ∑ z ∈ indices N d D H,
    PRZZActualMellin.localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t
  have his (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (Function.uncurry
        (PRZZActualMellin.localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z)) := by
    have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact localized_integrable_positive N d T (M/2) (3*M) a F1 F2 FM W Phi α β z
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
  rw [literal_mellin_positive N d D H T (M/2) (3*M) a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hT (by positivity) (by positivity)]
  change (1/(2*Real.pi):ℂ)*(∫ t, ∫ p, f p t) = _
  rw [← integral_integral_swap hi,← integral_integral_swap hj,
    ← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  have hall : ∀ᵐ p, ∀ z ∈ indices N d D H,
      Integrable (fun t => PRZZActualMellin.localized N d T (M/2) (3*M) a F1 F2 FM W Phi α β z p t) :=
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

theorem literal_windowed_nu_positive (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
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
  rw [literal_windowed_positive N d D H T M X V a F1 F2 FM W Phi α β
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

#print axioms kernel_integrable_positive
#print axioms amplitude_continuous_positive
#print axioms localized_integrable_positive
#print axioms finite_swap_positive
#print axioms literal_mellin_positive
#print axioms literal_windowed_positive
#print axioms literal_windowed_nu_positive
theorem sourceW_literal_windowed_nu (N d : ℕ) (D H T M X V : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM Phi : ℝ → ℂ) (α β sigma : ℂ) (hsigma : sigma ≠ 0)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hX : 0 < X) (hV : 0 < V)
    (hFM : Continuous FM)
    (hPhi : ContDiff ℝ ∞ Phi)
    (hs1 : Function.support F1 ⊆ Set.Icc ((d:ℝ)*X) (2*((d:ℝ)*X)))
    (hs2 : Function.support F2 ⊆ Set.Icc ((d:ℝ)*V) (2*((d:ℝ)*V)))
    (hsM : Function.support FM ⊆ Set.Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM (PRZZDyadicEnvelope.sourceW sigma) Phi α β =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (box T M X V ∩ PRZZAStarWindow.window N T (M/2) (3*M)).indicator
          (fun p => (PRZZDyadicEnvelope.sourceW sigma) (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(α+β))) p *
        mellin Phi (t*I)*PRZZMellinSeparation.twist (p.1*p.2/T) t *
        signedSum N d D H a F1 F2 FM α β p.1 p.2 t :=
  literal_windowed_nu_positive N d D H T M X V a F1 F2 FM
    (PRZZDyadicEnvelope.sourceW sigma) Phi α β hN hd hT hM hX hV hFM
    (PRZZSourceWOuter.sourceW_continuous sigma hsigma) hPhi hs1 hs2 hsM hsP

#print axioms sourceW_literal_windowed_nu

end XiPrime8845.PRZZPositiveMellin
