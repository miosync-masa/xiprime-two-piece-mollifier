import PRZZSpatialFreezeBudget

/-! Empty retained positive-frequency ranges have a large spatial scale,
not a vanishing original AFE row. Supply a genuine Gaussian-weight tail
envelope, uniform in the number of spatial scales. Arithmetic coefficients
and the freezing error are not silently identified with this envelope. -/
noncomputable section
open scoped BigOperators
open Set Complex MeasureTheory
namespace XiPrime8845.PRZZEmptyFrequencyDecay
set_option maxHeartbeats 4000000

theorem frequencies_empty (d : ℕ) (D H : ℝ) (hH : H ≤ 1) :
    PRZZPrefactorMass.frequencies d D H = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hh := Finset.mem_filter.mp (Finset.mem_product.mp hw).2
  have h1 : (1:ℝ) ≤ w.2 := by exact_mod_cast (Finset.mem_Icc.mp hh.1).1
  linarith [hh.2]

theorem scale_lower (d : ℕ) (T M V eH : ℝ) (hd : 0 < d) (hM : 0 < M)
    (hH : PRZZSourceCutoffs.poissonCutoff d T M V eH ≤ 1) :
    V*T^eH/d ≤ M := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hh := (div_le_iff₀ (mul_pos hd0 hM)).mp hH
  apply (div_le_iff₀ hd0).mpr
  simpa only [one_mul,mul_one,mul_comm] using hh

/-- No conclusion about the original sharp AFE row is made by this
empty-set identity. Its missing frequencies require a separate tail. -/
theorem active_empty (N d j l : ℕ) (D H : ℝ) (F1 F2 : ℝ → ℂ) (hH : H ≤ 1) :
    PRZZActiveFreezeBudget.active N d j l D H F1 F2 = ∅ := by
  simp [PRZZActiveFreezeBudget.active,PRZZPrefactorMass.localIndices,
    frequencies_empty d D H hH]

def constant (sigma : ℂ) : ℝ :=
  Real.exp 4/(4*Real.sqrt Real.pi)+6*Real.exp 4/(Real.sqrt Real.pi*‖sigma‖^2)

theorem source_quadratic (sigma : ℂ) (hs : sigma ≠ 0) (k m : ℝ)
    (hk : 0 < k) (hm : 0 < m) :
    ‖PRZZDyadicEnvelope.sourceW sigma (k*m^2)‖ ≤ constant sigma/(k^2*m^4) := by
  have hh := PRZZSourceDecay.sourceW_decay sigma hs 2 (k*m^2) (by norm_num) (by positivity)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  convert hh using 1 <;>
    simp [constant,Real.rpow_neg,Real.rpow_natCast] <;> ring

theorem source_inverse_square (sigma : ℂ) (hs : sigma ≠ 0) (x : ℝ) (hx : 0 < x) :
    ‖PRZZDyadicEnvelope.sourceW sigma x‖ ≤ constant sigma/x^2 := by
  simpa using source_quadratic sigma hs x 1 hx (by norm_num)

/-- Supply the decay denominator for the unfrozen actual mk argument,
using the original gap equation and the retained spatial support. -/
theorem actual_weight_decay (sigma : ℂ) (hs : sigma ≠ 0)
    (M T t m k u v delta : ℝ) (hM : 0 < M) (hT : 0 < T)
    (ht : 0 < t) (htT : t ≤ 2*T) (hu : 0 < u) (hv : 0 < v)
    (hm : M/2 ≤ m) (hgap : m*u-k*v = -delta) (hdelta : |delta| ≤ M*u/4) :
    ‖PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*m*k/t)‖ ≤
      constant sigma/(Real.pi*M^2*u/(8*T*v))^2 := by
  have hm0 : 0 < m := by linarith
  have hdu := (abs_le.mp hdelta).1
  have hmk : m*u/2 ≤ k*v := by nlinarith
  have hk : 0 < k := by nlinarith [mul_pos hm0 hu]
  have hx : 0 < 2*Real.pi*m*k/t := by positivity
  have hf : 0 < Real.pi*M^2*u/(8*T*v) := by positivity
  have hb : Real.pi*M^2*u/(8*T*v) ≤ 2*Real.pi*m*k/t := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8*T*v) ht).mpr
    have hm2 : M^2 ≤ 4*m^2 := by nlinarith
    have ha1 := mul_le_mul_of_nonneg_left hmk hm0.le
    have ha2 := mul_le_mul_of_nonneg_right hm2 hu.le
    have ha : M^2*u ≤ 8*m*k*v := by nlinarith [ha1,ha2]
    have hb' := mul_le_mul_of_nonneg_right ha ht.le
    have hc := mul_le_mul_of_nonneg_left htT (show 0 ≤ 8*m*k*v by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (hb'.trans hc) Real.pi_pos.le]
  apply (source_inverse_square sigma hs _ hx).trans
  apply div_le_div_of_nonneg_left (by unfold constant; positivity) (by positivity)
  nlinarith

/-- Apply the supplied actual-weight envelope under the original time
cutoff, retaining its L1 mass rather than assuming a time-uniform error. -/
theorem actual_weight_time (sigma : ℂ) (hs : sigma ≠ 0)
    (M T m k u v delta : ℝ) (hM : 0 < M) (hT : 0 < T)
    (hu : 0 < u) (hv : 0 < v) (hm : M/2 ≤ m)
    (hgap : m*u-k*v = -delta) (hdelta : |delta| ≤ M*u/4)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    ‖∫ t in Icc T (2*T), phi t*PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*m*k/t)‖ ≤
      (constant sigma/(Real.pi*M^2*u/(8*T*v))^2)*
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  let C := constant sigma/(Real.pi*M^2*u/(8*T*v))^2
  have hc : 0 ≤ C := by dsimp [C,constant]; positivity
  have hphiI : IntegrableOn (fun t : ℝ => ‖phi t‖) (Icc T (2*T)) :=
    hphi.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hg := hphiI.const_mul C
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t in Icc T (2*T), C*‖phi t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left
        (actual_weight_decay sigma hs M T t m k u v delta hM hT (hT.trans_le ht.1) ht.2
          hu hv hm hgap hdelta) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]

/-- In an h-empty source box, substitute the actual cutoff threshold
into the unfrozen W time-integral bound. All scale factors are retained. -/
theorem empty_actual_weight_time (sigma : ℂ) (hs : sigma ≠ 0) (d : ℕ)
    (M T V eH m k u v delta : ℝ) (hd : 0 < d) (hM : 0 < M) (hT : 0 < T)
    (hV : 0 < V) (hu : 0 < u) (hv : 0 < v) (hm : M/2 ≤ m)
    (hgap : m*u-k*v = -delta) (hdelta : |delta| ≤ M*u/4)
    (hH : PRZZSourceCutoffs.poissonCutoff d T M V eH ≤ 1)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    ‖∫ t in Icc T (2*T), phi t*PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*m*k/t)‖ ≤
      (constant sigma/(Real.pi*(V*T^eH/d)^2*u/(8*T*v))^2)*
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hM0 : 0 < V*T^eH/d := by positivity
  have hml := scale_lower d T M V eH hd hM hH
  have hc : 0 ≤ constant sigma := by unfold constant; positivity
  apply (actual_weight_time sigma hs M T m k u v delta hM hT hu hv hm hgap hdelta phi hphi).trans
  gcongr

/-- The actual W weight on each growing spatial scale has a summable
majorant even after paying one spatial-width factor. -/
theorem dyadic_decay (sigma : ℂ) (hs : sigma ≠ 0) (k M : ℝ)
    (hk : 0 < k) (hM : 0 < M) (n : ℕ) :
    ((2:ℝ)^n*M)*‖PRZZDyadicEnvelope.sourceW sigma (k*(((2:ℝ)^n*M)^2))‖ ≤
      (constant sigma/(k^2*M^3))*(1/8:ℝ)^n := by
  have hb := mul_le_mul_of_nonneg_left (source_quadratic sigma hs k ((2:ℝ)^n*M) hk (by positivity))
    (show 0 ≤ (2:ℝ)^n*M by positivity)
  apply hb.trans_eq
  have h2 : (2:ℝ)^n ≠ 0 := by positivity
  have hk0 := hk.ne'
  have hM0 := hM.ne'
  rw [div_pow]
  norm_num only [one_pow]
  have he : (8:ℝ)^n = ((2:ℝ)^n)^3 := by
    calc
      _ = ((2:ℝ)^3)^n := by norm_num
      _ = _ := by rw [← pow_mul,← pow_mul]; congr 1; omega
  rw [he]
  field_simp <;> ring

theorem geometric_bound (K : ℕ) : (∑ n ∈ Finset.range K, (1/8:ℝ)^n) ≤ 8/7 := by
  have he : (∑ n ∈ Finset.range K, (1/8:ℝ)^n) = (8/7:ℝ)*(1-(1/8:ℝ)^K) := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [he]
  have hh : 0 ≤ (1/8:ℝ)^K := by positivity
  nlinarith

theorem spatial_tail (sigma : ℂ) (hs : sigma ≠ 0) (k M : ℝ)
    (hk : 0 < k) (hM : 0 < M) (K : ℕ) :
    (∑ n ∈ Finset.range K, ((2:ℝ)^n*M)*
      ‖PRZZDyadicEnvelope.sourceW sigma (k*(((2:ℝ)^n*M)^2))‖) ≤
        (constant sigma/(k^2*M^3))*(8/7) := by
  have hc : 0 ≤ constant sigma/(k^2*M^3) := by unfold constant; positivity
  calc
    _ ≤ ∑ n ∈ Finset.range K, (constant sigma/(k^2*M^3))*(1/8:ℝ)^n := by
      apply Finset.sum_le_sum
      intro n hn
      exact dyadic_decay sigma hs k M hk hM n
    _ = (constant sigma/(k^2*M^3))*(∑ n ∈ Finset.range K, (1/8:ℝ)^n) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (geometric_bound K) hc

#print axioms frequencies_empty
#print axioms scale_lower
#print axioms active_empty
#print axioms source_quadratic
#print axioms source_inverse_square
#print axioms actual_weight_decay
#print axioms actual_weight_time
#print axioms empty_actual_weight_time
#print axioms dyadic_decay
#print axioms geometric_bound
#print axioms spatial_tail
end XiPrime8845.PRZZEmptyFrequencyDecay
