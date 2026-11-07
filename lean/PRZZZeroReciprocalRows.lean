import PRZZZeroReciprocal

/-! Apply the reciprocal substitution to the literal time-first zero
row. Actual cutoff values, the time-dependent endpoints, and all finite
outer coefficients are retained. No removal of the moving endpoints is
asserted in the finite identities below. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroReciprocalRows
open PRZZZeroReciprocal PRZZCosineSpatialJets
set_option maxHeartbeats 6000000

def row (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta x : ℝ) : ℂ :=
  exp (-(sigma+1)*(Real.log x:ℂ))*∫ t : ℝ,
    cos ((t*(delta/(u*x)):ℝ):ℂ)*PRZZTimeAmplitude.amplitude Phi T (2*Real.pi*u*x^2) sigma t

def integrand (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta x t : ℝ) : ℂ :=
  Phi (t/T)*weight sigma (2*Real.pi*u/t) (t*delta/u) x

def transformed (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta a b t : ℝ) : ℂ :=
  Phi (t/T)*exp (-sigma*(Real.log (t*delta/u):ℂ))*
    ∫ y in ((t*delta/u)/b)..((t*delta/u)/a),
      primitive (sigma-1) sigma ((2*Real.pi*u/t)*(t*delta/u)^2) y*cos (y:ℂ)

theorem integrand_eq (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta x t : ℝ) :
    integrand Phi T u sigma delta x t =
      exp (-(sigma+1)*(Real.log x:ℂ))*
        (cos ((t*(delta/(u*x)):ℝ):ℂ)*PRZZTimeAmplitude.amplitude Phi T (2*Real.pi*u*x^2) sigma t) := by
  have hp : (t*delta/u)/x = t*(delta/(u*x)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hw : (2*Real.pi*u/t)*x^2 = (2*Real.pi*u*x^2)/t := by ring
  have hcut : T⁻¹*t = t/T := by ring
  simp only [integrand,weight,PRZZTimeAmplitude.amplitude,PRZZMellinSeparation.scaledCutoff,
    PRZZTimeJets.reciprocal,hp,hw,hcut]
  ring

theorem time_window (Phi : ℝ → ℂ) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta x : ℝ) (hT : 0 < T) :
    row Phi T u sigma delta x = ∫ t in Icc T (2*T), integrand Phi T u sigma delta x t := by
  rw [row,← integral_const_mul]
  simp_rw [← integrand_eq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : Phi (t/T) = 0 := by
    by_contra hn
    have hh := hsPhi hn
    exact ht ⟨by simpa only [one_mul] using (le_div_iff₀ hT).mp hh.1,
      (div_le_iff₀ hT).mp hh.2⟩
  simp [integrand,hz]

theorem joint_continuous (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (T u a b : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (ha : 0 < a) (hs : sigma ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((Icc a b).prod (Icc T (2*T))) := by
  intro p hp
  have hx : 0 < p.1 := ha.trans_le hp.1.1
  have ht : 0 < p.2 := hT.trans_le hp.2.1
  have hx0 := hx.ne'
  have ht0 := ht.ne'
  have hu0 := hu.ne'
  have hT0 := hT.ne'
  have hw := (PRZZSourceWDerivatives.source_hasDerivAt sigma hs
    ((2*Real.pi*u/p.2)*p.1^2) (by positivity)).continuousAt
  have hW := hw.comp (f := fun p : ℝ × ℝ => (2*Real.pi*u/p.2)*p.1^2) (by fun_prop)
  have hl := (Real.continuousAt_log hx.ne').comp continuousAt_fst
  have hlc := Complex.continuous_ofReal.continuousAt.comp hl
  have hphase : ContinuousAt (fun p : ℝ × ℝ => ((p.2*delta/u)/p.1:ℝ) : ℝ × ℝ → ℂ) p :=
    Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
  apply ContinuousAt.continuousWithinAt
  unfold integrand weight
  fun_prop

theorem positive_continuous (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((Ioi (0:ℝ)).prod (Icc T (2*T))) := by
  intro p hp
  have hx : 0 < p.1 := hp.1
  have ht : 0 < p.2 := hT.trans_le hp.2.1
  have hx0 := hx.ne'
  have ht0 := ht.ne'
  have hu0 := hu.ne'
  have hT0 := hT.ne'
  have hw := (PRZZSourceWDerivatives.source_hasDerivAt sigma hs
    ((2*Real.pi*u/p.2)*p.1^2) (by positivity)).continuousAt
  have hW := hw.comp (f := fun p : ℝ × ℝ => (2*Real.pi*u/p.2)*p.1^2) (by fun_prop)
  have hl := (Real.continuousAt_log hx.ne').comp continuousAt_fst
  have hlc := Complex.continuous_ofReal.continuousAt.comp hl
  have hphase : ContinuousAt (fun p : ℝ × ℝ => ((p.2*delta/u)/p.1:ℝ) : ℝ × ℝ → ℂ) p :=
    Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
  apply ContinuousAt.continuousWithinAt
  unfold integrand weight
  fun_prop

theorem finite_time_exchange (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u a b : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b) (hs : sigma ≠ 0) :
    (∫ x in a..b, row Phi T u sigma delta x) =
      ∫ t in Icc T (2*T), ∫ x in a..b, integrand Phi T u sigma delta x t := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((Icc a b).prod (Icc T (2*T))) (volume.prod volume) :=
    (joint_continuous Phi hPhi T u a b sigma delta hT hu ha hs).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Icc T (2*T)))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (fun p hp => ⟨⟨hp.1.1.le,hp.1.2⟩,hp.2⟩)
  simp_rw [time_window Phi hsPhi T u sigma delta _ hT]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact integral_integral_swap hi'

theorem finite_joint_integrable (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (T u a b : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (ha : 0 < a) (hs : sigma ≠ 0) :
    Integrable (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Icc T (2*T)))) := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((Icc a b).prod (Icc T (2*T))) (volume.prod volume) :=
    (joint_continuous Phi hPhi T u a b sigma delta hT hu ha hs).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.prod_restrict]
  exact hi.mono_set (fun p hp => ⟨⟨hp.1.1.le,hp.1.2⟩,hp.2⟩)

/-- Actual time-first row, with no supplied decomposition equality. -/
theorem finite_row (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u a b : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b)
    (hs : sigma ≠ 0) (hd : 0 < delta) :
    (∫ x in a..b, row Phi T u sigma delta x) =
      ∫ t in Icc T (2*T), transformed Phi T u sigma delta a b t := by
  rw [finite_time_exchange Phi hPhi hsPhi T u a b sigma delta hT hu ha hab hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 < t := hT.trans_le ht.1
  unfold integrand transformed
  rw [intervalIntegral.integral_const_mul,
    finite_substitution sigma hs (2*Real.pi*u/t) (t*delta/u) a b (by positivity) (by positivity) ha hab]
  ring

theorem actual_pair (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u x : ℝ) (sigma : ℂ) (n : ℕ) (hT : 0 < T) (hu : 0 < u)
    (hx : 0 < x) (hs : sigma ≠ 0) :
    PRZZZeroCutoffLimit.corePair Phi T u sigma n x = 2*row Phi T u sigma ((n+1:ℕ):ℝ) x := by
  simpa only [PRZZZeroCutoffLimit.corePair,row,mul_assoc] using
    PRZZZeroCosine.core_cosine Phi hPhi hsPhi T u ((n+1:ℕ):ℝ) x sigma hT hu hx hs

#print axioms integrand_eq
#print axioms time_window
#print axioms joint_continuous
#print axioms positive_continuous
#print axioms finite_time_exchange
#print axioms finite_joint_integrable
#print axioms finite_row
#print axioms actual_pair
end XiPrime8845.PRZZZeroReciprocalRows
