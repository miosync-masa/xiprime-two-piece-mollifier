import PRZZOriginalDiagonal
import PRZZOptimalOuter

/-! Absolute arithmetic mass of the actual diagonal. The original product
restrictions supply a summable d^(-5/4) majorant. The bound has the sharp
N^(1/4) T^(-1/8) powers for this fixed scalar contour, with explicit logs;
it is not the optimized error estimate for the full PRZZ moment. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Finset Set Filter Topology
namespace XiPrime8845.PRZZDiagonalMass
open PRZZDiagonalAssembly PRZZPowerJets
set_option maxHeartbeats 5000000

theorem power_shift (z : ℂ) (S T x : ℝ) (hS : 0 ≤ S) (hT : 1 < T)
    (hx : 1 ≤ x) (hxT : x ≤ T) (hz : |z.re| ≤ S/Real.log T) :
    ‖power (1+z) x‖ ≤ Real.exp S/x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlt := Real.log_le_log hx0 hxT
  have he : -z.re*Real.log x ≤ S := by
    calc
      _ ≤ (S/Real.log T)*Real.log x := by gcongr; linarith [(abs_le.mp hz).1]
      _ ≤ (S/Real.log T)*Real.log T := by gcongr
      _ = S := by field_simp
  have hh := Real.exp_le_exp.mpr he
  have hn : ‖power (1+z) x‖ = Real.exp (-z.re*Real.log x)/x := by
    simp only [power,Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.add_re,
      Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [show -(1+z.re)*Real.log x = -z.re*Real.log x-Real.log x by ring,
      Real.exp_sub,Real.exp_log hx0]
  rw [hn]
  exact div_le_div_of_nonneg_right hh hx0.le

theorem coefficient_envelope (N d u v : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta : ℂ) (B U1 U2 S T : ℝ)
    (hB : 0 ≤ B) (hU1 : 0 ≤ U1) (hU2 : 0 ≤ U2) (hS : 0 ≤ S)
    (hT : 1 < T) (hNT : (N:ℝ) ≤ T) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ B)
    (hF1 : ∀ x, ‖F1 x‖ ≤ U1) (hF2 : ∀ x, ‖F2 x‖ ≤ U2)
    (halpha : |alpha.re| ≤ S/Real.log T) (hbeta : |beta.re| ≤ S/Real.log T)
    (hdu : d*u ≤ N) (hdv : d*v ≤ N) :
    ‖coefficient a F1 F2 alpha beta d u v‖ ≤
      (U1*U2*B^2*Real.exp (2*S))/((d:ℝ)*u*v) := by
  have huN : u ≤ N := (Nat.le_mul_of_pos_left u hd).trans hdu
  have hvN : v ≤ N := (Nat.le_mul_of_pos_left v hd).trans hdv
  have hpu := power_shift beta S T u hS hT (by exact_mod_cast hu)
    ((by exact_mod_cast huN : (u:ℝ) ≤ N).trans hNT) hbeta
  have hpv := power_shift alpha S T v hS hT (by exact_mod_cast hv)
    ((by exact_mod_cast hvN : (v:ℝ) ≤ N).trans hNT) halpha
  have hpd : ‖power 1 (d:ℝ)‖ = 1/(d:ℝ) := by
    simp only [power,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,one_mul,neg_mul]
    rw [Real.exp_neg,Real.exp_log (show (0:ℝ)<d by exact_mod_cast hd)]
    simp only [one_div]
  unfold coefficient
  simp only [norm_mul,norm_star]
  rw [hpd]
  have hdu1 : 1 ≤ d*u := Nat.mul_pos hd hu
  have hdv1 : 1 ≤ d*v := Nat.mul_pos hd hv
  calc
    _ ≤ U1*U2*B*B*(1/(d:ℝ))*(Real.exp S/u)*(Real.exp S/v) := by
      gcongr
      · exact hF1 _
      · exact hF2 _
      · exact ha _ (Finset.mem_Icc.mpr ⟨hdu1,hdu⟩)
      · exact ha _ (Finset.mem_Icc.mpr ⟨hdv1,hdv⟩)
    _ = _ := by rw [show 2*S = S+S by ring,Real.exp_add]; ring

theorem row_geometry (N T d u v : ℝ) (hN : 0 < N) (hT : 0 < T)
    (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hdu : d*u ≤ N) (hdv : d*v ≤ N) :
    (T/(2*Real.pi*u*v))^(-(1/8:ℝ)) ≤
      (2*Real.pi)^(1/8:ℝ)*T^(-(1/8:ℝ))*N^(1/4:ℝ)*d^(-(1/4:ℝ)) := by
  have he : (T/(2*Real.pi*u*v))^(-(1/8:ℝ)) =
      (2*Real.pi)^(1/8:ℝ)*T^(-(1/8:ℝ))*d^(-(1/4:ℝ))*
        ((d*u)^(1/8:ℝ)*(d*v)^(1/8:ℝ)) := by
    rw [Real.rpow_def_of_pos (show 0 < T/(2*Real.pi*u*v) by positivity)]
    simp only [Real.rpow_def_of_pos (show 0 < 2*Real.pi by positivity),Real.rpow_def_of_pos hT,
      Real.rpow_def_of_pos hd,Real.rpow_def_of_pos (mul_pos hd hu),
      Real.rpow_def_of_pos (mul_pos hd hv),Real.log_div hT.ne' (by positivity : 2*Real.pi*u*v ≠ 0),
      Real.log_mul (by positivity : 2*Real.pi*u ≠ 0) hv.ne',
      Real.log_mul (by positivity : 2*Real.pi ≠ 0) hu.ne',
      Real.log_mul hd.ne' hu.ne',Real.log_mul hd.ne' hv.ne',← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ (2*Real.pi)^(1/8:ℝ)*T^(-(1/8:ℝ))*d^(-(1/4:ℝ))*
        (N^(1/8:ℝ)*N^(1/8:ℝ)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hN]; norm_num; ring

/-- The abstract pointwise coefficient cap is an intermediate adapter,
not a hypothesis of the actual PRZZ coefficient theorem below. -/
theorem mass_envelope : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T B : ℝ)
    (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ),
    1 ≤ N → 0 < T → 0 ≤ B →
    (∀ d ∈ Finset.Icc 1 N, ∀ u ∈ Finset.Icc 1 N, ∀ v ∈ Finset.Icc 1 N,
      admissible N d u v → ‖coefficient a F1 F2 alpha beta d u v‖ ≤ B/((d:ℝ)*u*v)) →
    errorMass N a F1 F2 alpha beta T ≤
      C*B*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^2 := by
  classical
  have hp : Summable (fun n : ℕ => (n:ℝ)^(-(5/4:ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let Z := ∑' n : ℕ, (n:ℝ)^(-(5/4:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => by positivity)
  refine ⟨(2*Real.pi)^(1/8:ℝ)*(Z+1),by positivity,?_⟩
  intro N T B a F1 F2 alpha beta hN hT hB hc
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let K := B*(2*Real.pi)^(1/8:ℝ)*T^(-(1/8:ℝ))*(N:ℝ)^(1/4:ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmass : errorMass N a F1 F2 alpha beta T ≤
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        K*(d:ℝ)^(-(5/4:ℝ))*(1/(u:ℝ))*(1/(v:ℝ)) := by
    unfold errorMass
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    by_cases ha : admissible N d u v
    · rw [if_pos ha]
      have hd0 : (0:ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hu0 : (0:ℝ) < u := by exact_mod_cast (Finset.mem_Icc.mp hu).1
      have hv0 : (0:ℝ) < v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
      have hg := row_geometry N T d u v hN0 hT hd0 hu0 hv0
        (by exact_mod_cast ha.2.1) (by exact_mod_cast ha.2.2)
      have hh := mul_le_mul (hc d hd u hu v hv ha) hg (by positivity) (by positivity)
      apply hh.trans_eq
      have he : (d:ℝ)^(-(1/4:ℝ))/(d:ℝ) = (d:ℝ)^(-(5/4:ℝ)) := by
        rw [← Real.rpow_sub_one hd0.ne']
        norm_num
      calc
        _ = K*((d:ℝ)^(-(1/4:ℝ))/(d:ℝ))*(1/(u:ℝ))*(1/(v:ℝ)) := by dsimp [K]; ring
        _ = _ := by rw [he]
    · rw [if_neg ha]; positivity
  have he : (∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      K*(d:ℝ)^(-(5/4:ℝ))*(1/(u:ℝ))*(1/(v:ℝ))) =
      K*(∑ d ∈ Finset.Icc 1 N, (d:ℝ)^(-(5/4:ℝ)))*(SupportTail.harmonic N)^2 := by
    simp only [SupportTail.harmonic,pow_two,← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hz : (∑ d ∈ Finset.Icc 1 N, (d:ℝ)^(-(5/4:ℝ))) ≤ Z :=
    hp.sum_le_tsum _ (fun _ _ => by positivity)
  have hh : SupportTail.harmonic N ≤ 1+Real.log N := by
    simpa [SupportTail.harmonic,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using harmonic_le_one_add_log N
  have hh0 : 0 ≤ SupportTail.harmonic N := Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ K*(∑ d ∈ Finset.Icc 1 N, (d:ℝ)^(-(5/4:ℝ)))*(SupportTail.harmonic N)^2 := hmass.trans_eq he
    _ ≤ K*(Z+1)*(1+Real.log N)^2 := by gcongr; linarith
    _ = _ := by dsimp [K]; ring

#print axioms power_shift
#print axioms coefficient_envelope
#print axioms row_geometry
#print axioms mass_envelope

/-- Actual PRZZ arithmetic coefficients and valued compact cutoffs.
The constant is selected before N,T and both shifts. -/
theorem actual_mass_with_caps (js : List ℕ) (U1 U2 S : ℝ)
    (hU1 : 0 ≤ U1) (hU2 : 0 ≤ U2) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ F1 F2 : ℝ → ℂ,
      (∀ x, ‖F1 x‖ ≤ U1) → (∀ x, ‖F2 x‖ ≤ U2) →
      ∀ (N : ℕ) (T : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
  obtain ⟨D,hD,hm⟩ := mass_envelope
  refine ⟨D*U1*U2*Real.exp (2*S)+1,by positivity,?_⟩
  intro F1 F2 hu1 hu2 N T alpha beta hN hT hNT halpha hbeta
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  let B := (Real.log N)^PRZZGCoefficient.degree js
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha : ∀ n ∈ Finset.Icc 1 N, ‖(PRZZGCoefficient.coefficient js n:ℂ)‖ ≤ B := by
    intro n hn
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      PRZZGCoefficient.coefficient_bound js N hN n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  have hh := hm N T (U1*U2*B^2*Real.exp (2*S)) _ F1 F2 alpha beta hN (by linarith)
    (by positivity) (by
      intro d hd u hu v hv had
      exact coefficient_envelope N d u v _ F1 F2 alpha beta B U1 U2 S T hB hU1 hU2 hS hT hNT
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1
        ha hu1 hu2 halpha hbeta had.2.1 had.2.2)
  have hp : B^2*(1+Real.log N)^2 ≤ (1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
    calc
      _ ≤ ((1+Real.log N)^PRZZGCoefficient.degree js)^2*(1+Real.log N)^2 := by
        dsimp [B]
        gcongr
        linarith
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  calc
    _ ≤ (D*U1*U2*Real.exp (2*S))*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (B^2*(1+Real.log N)^2) := hh.trans_eq (by ring)
    _ ≤ (D*U1*U2*Real.exp (2*S))*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by gcongr
    _ ≤ _ := by gcongr; linarith

theorem actual_mass (js : List ℕ) (F1 F2 : ℝ → ℂ)
    (hF1 : Continuous F1) (hc1 : HasCompactSupport F1)
    (hF2 : Continuous F2) (hc2 : HasCompactSupport F2) (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
  obtain ⟨U1,hu1⟩ := hc1.exists_bound_of_continuous hF1
  obtain ⟨U2,hu2⟩ := hc2.exists_bound_of_continuous hF2
  obtain ⟨C,hC,h⟩ := actual_mass_with_caps js U1 U2 S
    ((norm_nonneg _).trans (hu1 0)) ((norm_nonneg _).trans (hu2 0)) hS
  exact ⟨C,hC,h F1 F2 hu1 hu2⟩

/-- The same constant works for the whole original scaled cutoff family,
including arbitrary dilation parameters, before N and T are selected. -/
theorem actual_scaled_mass (js : List ℕ) (F1 F2 : ℝ → ℂ)
    (hF1 : Continuous F1) (hc1 : HasCompactSupport F1)
    (hF2 : Continuous F2) (hc2 : HasCompactSupport F2) (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q1 Q2 : ℝ) (N : ℕ) (T : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F1 Q1) (PRZZMellinSeparation.scaledCutoff F2 Q2) alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
  obtain ⟨U1,hu1⟩ := hc1.exists_bound_of_continuous hF1
  obtain ⟨U2,hu2⟩ := hc2.exists_bound_of_continuous hF2
  obtain ⟨C,hC,h⟩ := actual_mass_with_caps js U1 U2 S
    ((norm_nonneg _).trans (hu1 0)) ((norm_nonneg _).trans (hu2 0)) hS
  refine ⟨C,hC,?_⟩
  intro Q1 Q2
  exact h _ _ (fun x => hu1 _) (fun x => hu2 _)

/-- Substitute the computed mass into the original diagonal time limit.
No coefficient-mass premise survives in this theorem. -/
theorem original_time_error (js : List ℕ) (F1 F2 : ℝ → ℂ)
    (hF1 : Continuous F1) (hc1 : HasCompactSupport F1)
    (hF2 : Continuous F2) (hc2 : HasCompactSupport F2) (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (P : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → alpha+beta ≠ 0 → ‖alpha+beta‖ ≤ 1/8 →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∀ y ≤ (1/2:ℝ), P y = 1) → (∀ y, 1 ≤ y → P y = 0) →
      ∀ phi : ℝ → ℂ, Continuous phi → ∃ E : ℂ,
        Tendsto (fun L : ℕ => (∫ t in Set.Icc T (2*T), phi t*
          PRZZWRowLimit.diagonal L N P
            (PRZZWRowReindex.leftCoefficient (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1)
            (PRZZWRowReindex.rightCoefficient (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F2)
            alpha beta t)-
          (∫ t in Set.Icc T (2*T), phi t)*
            main N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta) atTop (𝓝 E) ∧
        ‖E‖ ≤ C*(1+16/‖alpha+beta‖^2)*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
          (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
          (∫ t in Set.Icc T (2*T), ‖phi t‖) := by
  obtain ⟨D,hD,hm⟩ := actual_mass js F1 F2 hF1 hc1 hF2 hc2 S hS
  obtain ⟨C,hC,he⟩ := PRZZOriginalDiagonal.labelled_time_main_error
  refine ⟨C*D,by positivity,?_⟩
  intro N P alpha beta T hN hT hNT hs hn halpha hbeta hlo hhi phi hphi
  obtain ⟨E,hE,hb⟩ := he N P F1 F2 (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    alpha beta T hs hn (by linarith) hlo hhi phi hphi
  refine ⟨E,hE,hb.trans ?_⟩
  have hh := hm N T alpha beta hN hT hNT halpha hbeta
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh
    (show 0 ≤ C*(1+16/‖alpha+beta‖^2) by positivity)) (integral_nonneg (fun _ => norm_nonneg _))).trans_eq (by ring)

#print axioms actual_mass
#print axioms actual_mass_with_caps
#print axioms actual_scaled_mass
#print axioms original_time_error

theorem logarithms_absorbed (p : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 1 ≤ Real.log T →
      (1+Real.log N)^p ≤ C*T^delta := by
  obtain ⟨D,hD,hd⟩ := PRZZOptimalOuter.power_log_absorbed p 0 delta hdelta
  refine ⟨(2:ℝ)^p*D,by positivity,?_⟩
  intro N T hN hT hNT hlog
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlt : Real.log N ≤ Real.log T := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNT
  have hh := hd T hT.le
  simp only [Real.rpow_zero,one_mul] at hh
  calc
    _ ≤ (2*Real.log T)^p := by gcongr; linarith
    _ = (2:ℝ)^p*(Real.log T)^p := mul_pow _ _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_left hh (show 0 ≤ (2:ℝ)^p by positivity)).trans_eq (by ring)

/-- All logarithmic coefficient and harmonic losses can be spent in any
strictly positive height margin, without worsening the N^(1/4) power. -/
theorem actual_mass_absorbed (js : List ℕ) (F1 F2 : ℝ → ℂ)
    (hF1 : Continuous F1) (hc1 : HasCompactSupport F1)
    (hF2 : Continuous F2) (hc2 : HasCompactSupport F2) (S delta : ℝ)
    (hS : 0 ≤ S) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 1 ≤ Real.log T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      errorMass N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F1 F2 alpha beta T ≤
        C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ)+delta) := by
  obtain ⟨C,hC,hm⟩ := actual_mass js F1 F2 hF1 hc1 hF2 hc2 S hS
  obtain ⟨D,hD,hl⟩ := logarithms_absorbed (2*PRZZGCoefficient.degree js+2) delta hdelta
  refine ⟨C*D,by positivity,?_⟩
  intro N T alpha beta hN hT hNT hlog halpha hbeta
  calc
    _ ≤ C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := hm N T alpha beta hN hT hNT halpha hbeta
    _ ≤ C*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(D*T^delta) := by gcongr; exact hl N T hN hT hNT hlog
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < T)]; ring

#print axioms logarithms_absorbed
#print axioms actual_mass_absorbed
end XiPrime8845.PRZZDiagonalMass
