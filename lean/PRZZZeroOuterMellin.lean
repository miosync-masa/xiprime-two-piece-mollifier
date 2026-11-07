import PRZZZeroRowMellin
import PRZZDiagonalAssembly

/-! Sum the identified actual cosine rows over all positive gaps and
over the finite gcd arithmetic grid. The original coefficient and the
admissibility mask remain literal. No identification with the full AFE
off-diagonal decomposition or two-branch cancellation is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroOuterMellin
open PRZZZeroRowMellin PRZZZeroReciprocalRows PRZZZeroCutoffLimit
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem pair_integrable (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (n : ℕ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    IntegrableOn (corePair Phi T u sigma n) (Ioi (0:ℝ)) := by
  have hi : IntegrableOn (fun x : ℝ => (2:ℂ)*row Phi T u sigma ((n+1:ℕ):ℝ) x) (Set.Ioi (0:ℝ)) :=
    (row_integrable Phi hPhi hcPhi hsPhi T u sigma ((n+1:ℕ):ℝ) hT hu hs hn (by positivity)).const_mul (2:ℂ)
  exact hi.congr_fun (fun x hx => (actual_pair Phi hPhi hsPhi T u x sigma n hT hu hx hs).symm)
    measurableSet_Ioi

theorem pair_mass_summable (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ), ‖corePair Phi T u sigma n x‖) := by
  obtain ⟨B,hB,hb⟩ := core_pair_bound Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn
  have hp : Summable (fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let J := ∫ x in Ioi (0:ℝ), PRZZZeroGap.envelope x
  apply (hp.mul_left (2*B*J)).of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
  intro n
  have hi := (pair_integrable Phi hPhi hcPhi hsPhi T u sigma n hT hu hs hn).norm
  have hh := integral_mono_ae hi ((PRZZZeroGap.envelope_integrable.const_mul (2*B)).mul_const
    (1/(((n+1:ℕ):ℝ)^2))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb n x hx)
  simpa only [integral_mul_const,integral_const_mul,J,mul_assoc,mul_left_comm,mul_comm] using hh

/-- The original time-first zero field, with all positive gaps included. -/
theorem actual_field (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∫ x in Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T u sigma x) =
      ∑' n : ℕ, 2*(∫ t in Icc T (2*T), value Phi T u sigma ((n+1:ℕ):ℝ) t) := by
  have he : (∫ x in Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T u sigma x) =
      ∫ x in Ioi (0:ℝ), ∑' n : ℕ, corePair Phi T u sigma n x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (PRZZZeroCosine.core_series_cosine Phi hPhi hsPhi T u x sigma hT hu hx hs).symm
  rw [he,← integral_tsum_of_summable_integral_norm
    (fun n => pair_integrable Phi hPhi hcPhi hsPhi T u sigma n hT hu hs hn)
    (pair_mass_summable Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn)]
  apply tsum_congr
  intro n
  have he' : (∫ x in Ioi (0:ℝ), corePair Phi T u sigma n x) =
      2*(∫ x in Ioi (0:ℝ), row Phi T u sigma ((n+1:ℕ):ℝ) x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact actual_pair Phi hPhi hsPhi T u x sigma n hT hu hx hs
  rw [he',actual_row Phi hPhi hcPhi hsPhi T u sigma ((n+1:ℕ):ℝ) hT hu hs hn (by positivity)]

def arithmeticZero (N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) : ℂ := by
  classical
  exact ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
        (∫ x in Set.Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T ((u:ℝ)*v) (alpha+beta) x) else 0

theorem actual_exhaustion (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => ∑ k ∈ range (2*L), ∑ n ∈ range L,
      ∫ x in Set.Ioi (0:ℝ), PRZZZeroGapExchange.pair (PRZZPartitionMass.profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x) atTop
      (𝓝 (∑' n : ℕ, 2*(∫ t in Set.Icc T (2*T), value Phi T u sigma ((n+1:ℕ):ℝ) t))) := by
  rw [← actual_field Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn]
  exact PRZZZeroCosine.actual_cosine_limit S hS hm hlo hhi hleft hright
    Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn

def finiteArithmeticZero (S : ℝ → ℝ) (L N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) : ℂ := by
  classical
  exact ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
        (∑ k ∈ range (2*L), ∑ n ∈ range L,
          ∫ x in Set.Ioi (0:ℝ), PRZZZeroGapExchange.pair (PRZZPartitionMass.profile S) Phi
            ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T ((u:ℝ)*v) (alpha+beta) n x) else 0

/-- Every gcd coefficient, cutoff value, and admissibility condition is
retained in the finite outer sum. No arithmetic mass estimate is assumed. -/
theorem arithmetic_zero_mellin (N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    arithmeticZero N a F1 F2 Phi alpha beta T =
      ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
            (∑' n : ℕ, 2*(∫ t in Set.Icc T (2*T), value Phi T ((u:ℝ)*v) (alpha+beta) ((n+1:ℕ):ℝ) t)) else 0 := by
  classical
  unfold arithmeticZero
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
  have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · rw [if_pos had,if_pos had,actual_field Phi hPhi hcPhi hsPhi T ((u:ℝ)*v) (alpha+beta)
      hT (mul_pos hu0 hv0) hs hn]
  · rw [if_neg had,if_neg had]

/-- Simultaneous spatial/gap cutoff removal commutes with every finite
outer gcd row, with actual coefficient values and no multiplicity loss. -/
theorem arithmetic_exhaustion (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => finiteArithmeticZero S L N a F1 F2 Phi alpha beta T) atTop
      (𝓝 (arithmeticZero N a F1 F2 Phi alpha beta T)) := by
  classical
  unfold finiteArithmeticZero arithmeticZero
  apply tendsto_finsetSum
  intro d hd
  apply tendsto_finsetSum
  intro u hu
  apply tendsto_finsetSum
  intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    have hu0 : (0:ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have hv0 : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    exact (PRZZZeroCosine.actual_cosine_limit S hS hm hlo hhi hleft hright Phi hPhi hcPhi hsPhi
      T ((u:ℝ)*v) (alpha+beta) hT (mul_pos hu0 hv0) hs hn).const_mul _
  · simp only [if_neg had]
    exact tendsto_const_nhds

theorem arithmetic_mellin_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (N : ℕ) (a : ℕ → ℂ) (F1 F2 Phi : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => finiteArithmeticZero S L N a F1 F2 Phi alpha beta T) atTop
      (𝓝 (∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
            (∑' n : ℕ, 2*(∫ t in Set.Icc T (2*T), value Phi T ((u:ℝ)*v) (alpha+beta) ((n+1:ℕ):ℝ) t)) else 0)) := by
  rw [← arithmetic_zero_mellin N a F1 F2 Phi alpha beta T hPhi hcPhi hsPhi hT hs hn]
  exact arithmetic_exhaustion S hS hm hlo hhi hleft hright N a F1 F2 Phi alpha beta T
    hPhi hcPhi hsPhi hT hs hn

#print axioms pair_integrable
#print axioms pair_mass_summable
#print axioms actual_field
#print axioms arithmetic_zero_mellin
#print axioms actual_exhaustion
#print axioms arithmetic_exhaustion
#print axioms arithmetic_mellin_limit
end XiPrime8845.PRZZZeroOuterMellin
