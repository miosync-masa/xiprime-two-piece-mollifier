import PRZZEmptyFrequencyDecay

/-! Arithmetic mass of the original congruence rows when the retained
positive Fourier range is empty. The h=1 label below is only a bijective
counting device: no Fourier mode is inserted into the original sum.
The starting spatial scale is retained in the uniform finite-scale bound. -/
noncomputable section
open scoped BigOperators
open Set Complex
namespace XiPrime8845.PRZZEmptyArithmeticMass
open PRZZPrefactorMass PRZZActiveFreezeBudget PRZZUnfrozenPoisson
set_option maxHeartbeats 5000000

def gaps (d : ℕ) (D : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈D/d⌉) ⌈D/d⌉).filter
    (fun delta : ℤ => 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d)

def rowMass (N d j l : ℕ) (D : ℝ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ pairs N d j l, ∑ delta ∈ gaps d D,
    ‖arithmetic a F1 F2 d alpha beta (p,(delta,0))/((p.1:ℂ)*(p.2:ℂ))‖

theorem frequencies_two (d : ℕ) (D : ℝ) : frequencies d D 2 = gaps d D ×ˢ {1} := by
  classical
  have he : ((Finset.Icc 1 ⌊(2:ℝ)⌋₊).filter (fun h : ℕ => (h:ℝ) < 2)) = {1} := by
    ext h
    norm_num only [Nat.floor_ofNat,Finset.mem_filter,Finset.mem_Icc,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hbound⟩
      have hh : h < 2 := by exact_mod_cast hbound
      omega
    · intro hh; subst hh; norm_num
  rw [frequencies,he]
  rfl

/-- Exact arithmetic mass, independent of a Fourier-frequency phase.
The original phase-free coefficient is not postulated equal to a mode. -/
theorem row_mass_eq (N d j l : ℕ) (D : ℝ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) :
    rowMass N d j l D a F1 F2 alpha beta = mass N d j l D 2 a F1 F2 alpha beta := by
  unfold rowMass mass localIndices
  rw [frequencies_two]
  simp only [Finset.sum_product,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro delta hd
  rw [← arithmetic_mass_eq]
  rfl

theorem frequency_two_count (d : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ((frequencies d D 2).card:ℝ) ≤ 10*(D/d) := by
  classical
  by_cases hh : 1 ≤ D/(d:ℝ)
  · exact (frequency_count d D 2 hh (by norm_num)).trans_eq (by ring)
  · have he : gaps d D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro delta hd
      have hg := (Finset.mem_filter.mp hd).2
      have hn : delta ≠ 0 := by intro he; simp [he] at hg
      have h1 : (1:ℝ) ≤ |(delta:ℝ)| := by exact_mod_cast Int.one_le_abs hn
      linarith
    rw [frequencies_two,he]
    simp only [Finset.empty_product,Finset.card_empty,Nat.cast_zero]
    positivity

/-- Coefficient values, conjugation and complex powers are all supplied
by the existing literal pair-mass theorem. Both signed gaps are counted. -/
theorem coefficient_row (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l : ℕ) (D T Q V S : ℝ)
      (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ D → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      rowMass N d j l D (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta ≤
      (C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js))*10*D/(d:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := local_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N d j l D T Q V S alpha beta hN hd hNT hL hD hS ha hb
  rw [row_mass_eq]
  have hh := h js N d j l T Q V S D 2 alpha beta hN hd hNT hL hS ha hb
  apply hh.trans
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hp := mul_le_mul_of_nonneg_right (frequency_two_count d D hD)
    (show 0 ≤ C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d by positivity)
  exact hp.trans_eq (by ring)

theorem cost_gap_double (T M Q eps : ℝ) (j l : ℕ) :
    sourceCost T (2*M) eps j l*PRZZSourceCutoffs.deltaCutoff T (2*M) Q eps =
      (sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps)/8 := by
  rw [cost_double]
  unfold PRZZSourceCutoffs.deltaCutoff
  ring

/-- Delta grows linearly with M, but the analytic cost decays quartically.
Thus the full signed-gap charge pays a geometric moment, not K. -/
theorem spatial_gap_sum (T M Q eps : ℝ) (j l K : ℕ) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 ≤ Q) :
    (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
      PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) ≤
      (8/7:ℝ)*(sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps) := by
  have he (k : ℕ) : sourceCost T ((2:ℝ)^k*M) eps j l*
      PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps =
      (sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps)*(1/8:ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,show (2:ℝ)^k*2*M = 2*((2:ℝ)^k*M) by ring,cost_gap_double,ih,pow_succ]
      ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hc : 0 ≤ sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps := by
    unfold sourceCost PRZZFreezeScales.ratioCap PRZZSourceCutoffs.deltaCutoff
    positivity
  exact (mul_le_mul_of_nonneg_left (PRZZEmptyFrequencyDecay.geometric_bound K) hc).trans_eq (by ring)

/-- Genuine arithmetic rows summed over every spatial scale, uniformly
in K. The remaining starting-scale factor is displayed, not assumed small. -/
theorem coefficient_spatial (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l K : ℕ) (T M Q V S eps : ℝ)
      (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T →
      0 < M → 0 ≤ Q → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta) ≤
        C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
          sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps/(d:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := coefficient_row F G hF hG hcF hcG
  refine ⟨C*10*(8/7),by positivity,?_⟩
  intro js N d j l K T M Q V S eps alpha beta hN hd hNT hT hL hM hQ hS ha hb
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  let A := C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*10/(d:ℝ)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ k ∈ Finset.range K, A*(sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := mul_le_mul_of_nonneg_left
        (h js N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) T Q V S alpha beta hN hd hNT hL
          (by unfold PRZZSourceCutoffs.deltaCutoff; positivity) hS ha hb)
        (show 0 ≤ sourceCost T ((2:ℝ)^k*M) eps j l by
          unfold sourceCost PRZZFreezeScales.ratioCap; positivity)
      exact hh.trans_eq (by dsimp [A]; ring)
    _ = A*(∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*
        PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((8/7)*(sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps)) :=
      mul_le_mul_of_nonneg_left (spatial_gap_sum T M Q eps j l K hT hM hQ) hA
    _ = _ := by dsimp [A]; ring

def outerMass (js : List ℕ) (N K : ℕ) (T M Q V eps : ℝ)
    (F G : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      sourceCost T ((2:ℝ)^k*M) eps j l*
        rowMass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta

/-- All actual arithmetic coefficients, signed gaps, gcd divisors, and
dyadic coordinates are summed. No coefficient-mass premise is supplied;
only the explicit scalar starting-scale budget remains to be optimized. -/
theorem coefficient_outer (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N K : ℕ) (T M Q V S eps : ℝ) (alpha beta : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T → 0 < M → 0 ≤ Q → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      outerMass js N K T M Q V eps F G alpha beta ≤
        (C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js))*
          (∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
            ∑ l ∈ Finset.range (Nat.log 2 N+1),
              sourceCost T M eps j l*PRZZSourceCutoffs.deltaCutoff T M Q eps/(d:ℝ)^2) := by
  obtain ⟨C,hC,h⟩ := coefficient_spatial F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N K T M Q V S eps alpha beta hN hNT hT hL hM hQ hS ha hb
  unfold outerMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  exact (h js N d j l K T M Q V S eps alpha beta hN (Finset.mem_Icc.mp hd).1 hNT hT hL hM hQ hS ha hb).trans_eq (by ring)

/-- The eventual empty-row fifth-power contribution fits the published
target. This power comparison alone is not a bound on the unevaluated mass. -/
theorem fifth_power_target (N T : ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T) (hscale : N ≤ T^(4/7:ℝ)) :
    N^5/T^2 ≤ PRZZOptimalPowers.target N T := by
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hp : N^(13/4:ℝ) ≤ T^2 := by
    calc
      _ ≤ (T^(4/7:ℝ))^(13/4:ℝ) := Real.rpow_le_rpow hn.le hscale (by norm_num)
      _ = T^(13/7:ℝ) := by rw [← Real.rpow_mul ht.le]; norm_num
      _ ≤ T^2 := by
        rw [← Real.rpow_natCast T 2]
        exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have he : N^5 = N^(7/4:ℝ)*N^(13/4:ℝ) := by
    rw [← Real.rpow_add hn]; norm_num [Real.rpow_natCast]
  apply (div_le_iff₀ (by positivity : 0 < T^2)).mpr
  rw [he]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)

#print axioms frequencies_two
#print axioms row_mass_eq
#print axioms frequency_two_count
#print axioms coefficient_row
#print axioms cost_gap_double
#print axioms spatial_gap_sum
#print axioms coefficient_spatial
#print axioms coefficient_outer
#print axioms fifth_power_target
end XiPrime8845.PRZZEmptyArithmeticMass
