import PRZZNativeCentralLiteral

/-! Actual integrated Fourier rows with the frequency cutoff removed.
The summable envelope is supplied by the actual weight, including its
complex power, sourceW and reciprocal phase. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZFourierExhaustion
open PRZZCentralTail PRZZFrozenTail PRZZNativeCentralLiteral
set_option maxHeartbeats 7000000

def coefficient (d : ℕ) (G H : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (z : PRZZAStar.Index) : ℂ :=
  PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))

def pairTerm (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ) (T M : ℝ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (j : ℕ) (t : ℝ) : ℂ :=
  Phi (t/T)*(coefficient d G H a alpha beta z*
    pair F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) 0 j t)

def integratedPair (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ) (T M : ℝ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (j : ℕ) : ℂ :=
  ∫ t in Icc T (2*T), pairTerm d F G H Phi a T M alpha beta z j t

def allModes (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ) (T M : ℝ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) : ℂ :=
  (∫ t in Icc T (2*T), centralTerm d 0 F G H Phi a T M alpha beta z t)+
    ∑' j, integratedPair d F G H Phi a T M alpha beta z j

theorem pair_domination (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ j,
      AEStronglyMeasurable (pairTerm d F G H Phi a T M alpha beta z j) (volume.restrict (Icc T (2*T))) ∧
      ∀ t ∈ Icc T (2*T), ‖pairTerm d F G H Phi a T M alpha beta z j t‖ ≤ E*(1/((j:ℝ)+1)^2) := by
  let p := fun j : ℕ => phase 1 (residue z/z.1.2) ((0+j:ℝ)+1)
  let m := fun j : ℕ => phase 1 (residue z/z.1.2) (-((0+j:ℝ)+1))
  let c := coefficient d G H a alpha beta z
  have he (j : ℕ) (t : ℝ) : pairTerm d F G H Phi a T M alpha beta z j t =
      Phi (t/T)*(c*PRZZFourierTime.term F (M/z.1.2) ((z.1.1:ℝ)*z.1.2*1) 1 ((z.2.1:ℝ)*1)
        (alpha+beta+1) (alpha+beta) 0 j p m t) := by
    unfold pairTerm
    rw [pair_eq F M 1 (residue z/z.1.2) z alpha beta (alpha+beta) 0 j t (by norm_num)]
    simp only [p,m,c,Nat.cast_zero]
  obtain ⟨D,hD,hd⟩ := PRZZFourierTime.term_domination F hF hsF T (M/z.1.2)
    ((z.1.1:ℝ)*z.1.2*1) 1 ((z.2.1:ℝ)*1) (alpha+beta+1) (alpha+beta) 0 p m
    hT (by positivity) (by positivity) (by norm_num) hs
    (fun j => (phase_norm _ _ _).le) (fun j => (phase_norm _ _ _).le)
  have hp : Continuous (fun t : ℝ => Phi (t/T)) := hPhi.comp (continuous_id.div_const T)
  obtain ⟨U,hU⟩ := isCompact_Icc.exists_bound_of_continuousOn hp.continuousOn
  refine ⟨max U 0*‖c‖*D,by positivity,?_⟩
  intro j
  have hmeas : StronglyMeasurable (fun t => PRZZFourierTime.term F (M/z.1.2)
      ((z.1.1:ℝ)*z.1.2*1) 1 ((z.2.1:ℝ)*1) (alpha+beta+1) (alpha+beta) 0 j p m t) := by
    unfold PRZZFourierTime.term
    exact (((PRZZFourierTime.fourier_measurable F hF.continuous _ _ _ _ _ _ _).mul_const _).add
      ((PRZZFourierTime.fourier_measurable F hF.continuous _ _ _ _ _ _ _).mul_const _)).const_smul ((1:ℝ)⁻¹)
  constructor
  · change AEStronglyMeasurable (fun t => pairTerm d F G H Phi a T M alpha beta z j t) _
    simp_rw [he]
    exact (hp.stronglyMeasurable.mul (hmeas.const_mul c)).aestronglyMeasurable
  · intro t ht
    rw [he,norm_mul,norm_mul]
    exact (mul_le_mul ((hU t ht).trans (le_max_left _ _))
      (mul_le_mul_of_nonneg_left (hd t ht j) (norm_nonneg _))
      (by positivity) (le_max_right _ _)).trans_eq (by ring)

theorem pair_integrable_summable (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    (∀ j, IntegrableOn (pairTerm d F G H Phi a T M alpha beta z j) (Icc T (2*T))) ∧
      Summable (fun j => integratedPair d F G H Phi a T M alpha beta z j) := by
  obtain ⟨E,hE,he⟩ := pair_domination d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs
  have hc (j : ℕ) : IntegrableOn (fun _ : ℝ => E*(1/((j:ℝ)+1)^2)) (Icc T (2*T)) :=
    continuous_const.integrableOn_Icc
  have hi (j : ℕ) : IntegrableOn (pairTerm d F G H Phi a T M alpha beta z j) (Icc T (2*T)) := by
    apply (hc j).mono' (he j).1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (he j).2 t ht
  refine ⟨hi,?_⟩
  apply Summable.of_norm
  have hsum := PRZZWeightTail.square_summable.mul_left (E*((volume (Icc T (2*T))).toReal))
  apply hsum.of_nonneg_of_le (fun j => norm_nonneg _)
  intro j
  apply (norm_integral_le_integral_norm _).trans
  have hb := setIntegral_mono_on (hi j).norm
    (show IntegrableOn (fun _ : ℝ => E*(1/((j:ℝ)+1)^2)) (Icc T (2*T)) from continuous_const.integrableOn_Icc)
    measurableSet_Icc (he j).2
  exact hb.trans_eq (by simp only [setIntegral_const,smul_eq_mul,Measure.real]; ring)

theorem central_time_eq (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    (∫ t in Icc T (2*T), centralTerm d J F G H Phi a T M alpha beta z t) =
      (∫ t in Icc T (2*T), centralTerm d 0 F G H Phi a T M alpha beta z t)+
        ∑ j ∈ Finset.range J, integratedPair d F G H Phi a T M alpha beta z j := by
  have hi := (pair_integrable_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs).1
  have hi0 : IntegrableOn (centralTerm d 0 F G H Phi a T M alpha beta z) (Icc T (2*T)) :=
    (term_integrable d 0 F G H Phi a T M alpha beta z hF.continuous hPhi hT hM hu hv hs hsF hsPhi).integrableOn
  have he (t : ℝ) : centralTerm d J F G H Phi a T M alpha beta z t =
      centralTerm d 0 F G H Phi a T M alpha beta z t+
        ∑ j ∈ Finset.range J, pairTerm d F G H Phi a T M alpha beta z j t := by
    simp [centralTerm,central,pairTerm,coefficient,mul_add,mul_sum]
  have hh := integral_add hi0 (integrable_finsetSum (Finset.range J) (fun j hj => hi j))
  rw [integral_finsetSum _ (fun j hj => hi j)] at hh
  simpa only [he,integratedPair] using hh

theorem central_time_tendsto (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => ∫ t in Icc T (2*T), centralTerm d J F G H Phi a T M alpha beta z t) atTop
      (𝓝 (allModes d F G H Phi a T M alpha beta z)) := by
  have hsum := (pair_integrable_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs).2
  have hh : Tendsto (fun J : ℕ =>
      (∫ t in Icc T (2*T), centralTerm d 0 F G H Phi a T M alpha beta z t)+
        ∑ j ∈ Finset.range J, integratedPair d F G H Phi a T M alpha beta z j) atTop
      (𝓝 (allModes d F G H Phi a T M alpha beta z)) :=
    tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  apply hh.congr'
  exact Eventually.of_forall (fun J => (central_time_eq d J F G H Phi a hF hPhi hsF hsPhi T M alpha beta z hT hM hu hv hs).symm)

theorem integral_norm_summable (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    Summable (fun j => ∫ t in Icc T (2*T), ‖pairTerm d F G H Phi a T M alpha beta z j t‖) := by
  obtain ⟨E,hE,he⟩ := pair_domination d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs
  have hi := (pair_integrable_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs).1
  have hsum := PRZZWeightTail.square_summable.mul_left (E*((volume (Icc T (2*T))).toReal))
  apply hsum.of_nonneg_of_le (fun j => integral_nonneg (fun t => norm_nonneg _))
  intro j
  have hb := setIntegral_mono_on (hi j).norm
    (show IntegrableOn (fun _ : ℝ => E*(1/((j:ℝ)+1)^2)) (Icc T (2*T)) from continuous_const.integrableOn_Icc)
    measurableSet_Icc (he j).2
  exact hb.trans_eq (by simp only [setIntegral_const,smul_eq_mul,Measure.real]; ring)

theorem pair_time_swap (d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index)
    (hT : 0 < T) (hM : 0 < M) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    (∑' j, integratedPair d F G H Phi a T M alpha beta z j) =
      ∫ t in Icc T (2*T), ∑' j, pairTerm d F G H Phi a T M alpha beta z j t := by
  exact integral_tsum_of_summable_integral_norm
    (pair_integrable_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs).1
    (integral_norm_summable d F G H Phi a hF hPhi hsF T M alpha beta z hT hM hu hv hs)

#print axioms integral_norm_summable
#print axioms pair_time_swap
#print axioms pair_domination
#print axioms pair_integrable_summable
#print axioms central_time_eq
#print axioms central_time_tendsto
end XiPrime8845.PRZZFourierExhaustion

