import PRZZZeroCutoffLimit

/-! The original M >= 1 partition is not the two-sided zero-mode
exhaustion. Their low-scale correction is explicit, even in the limit.
It vanishes on the positive integer lattice, not on all positive reals. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.PRZZPartitionDiscrepancy
open PRZZAFEProgression PRZZPartitionMass PRZZZeroSpatialLimit
set_option maxHeartbeats 3000000

def original (S : ℝ → ℝ) (K : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range K, profile S (((2:ℝ)^j)⁻¹*x)

theorem original_eq (S : ℝ → ℝ) (K : ℕ) (x : ℝ) :
    original S K x = (S (x/(2:ℝ)^K):ℂ)-(S x:ℂ) := by
  unfold original
  simp_rw [profile_scaled]
  simpa only [mul_one,div_one] using piece_telescope (fun y => (S y:ℂ)) 1 x K

/-- Both upper endpoints and the missing lower endpoint are retained. -/
theorem cutoff_difference (S : ℝ → ℝ) (L : ℕ) (x : ℝ) :
    cutoff S L x-original S (L+2) x =
      ((S (x/(2:ℝ)^L):ℂ)-(S (x/(2:ℝ)^(L+2)):ℂ))+
        ((S x:ℂ)-(S ((2:ℝ)^L*x):ℂ)) := by
  rw [original_eq,cutoff]
  ring

theorem original_eventually (S : ℝ → ℝ)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1) (x : ℝ) :
    ∀ᶠ L : ℕ in atTop, original S (L+2) x = 1-(S x:ℂ) := by
  have hg : Tendsto (fun L : ℕ => (2:ℝ)^L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hg.eventually (eventually_ge_atTop (2*x))] with L hL
  have hh : x/(2:ℝ)^(L+2) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp : (0:ℝ) < 2^L := by positivity
    rw [pow_add]
    norm_num
    linarith
  rw [original_eq,hleft _ hh,Complex.ofReal_one]

/-- The limiting discrepancy is the seed, not zero. No pointwise-to-
integral inference is made here. -/
theorem difference_eventually (S : ℝ → ℝ)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1)
    (hright : ∀ y, 1 ≤ y → S y = 0) (x : ℝ) (hx : 0 < x) :
    ∀ᶠ L : ℕ in atTop, cutoff S L x-original S (L+2) x = (S x:ℂ) := by
  filter_upwards [cutoff_eventually S hleft hright x hx,
    original_eventually S hleft x] with L h1 h2
  rw [h1,h2]
  ring

theorem integer_correction_zero (S : ℝ → ℝ)
    (hright : ∀ y, 1 ≤ y → S y = 0) (m : ℕ) (hm : 0 < m) :
    (S (m:ℝ):ℂ) = 0 := by
  rw [hright _ (by exact_mod_cast hm),Complex.ofReal_zero]

/-- After x=m/v the correction is zero only when the ratio reaches
the upper plateau. A positive numerator alone is not used as a premise. -/
theorem quotient_correction_zero (S : ℝ → ℝ)
    (hright : ∀ y, 1 ≤ y → S y = 0) (m v : ℕ) (hv : 0 < v) (hvm : v ≤ m) :
    (S ((m:ℝ)/v):ℂ) = 0 := by
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  rw [hright _ ((le_div_iff₀ hvR).mpr (by simpa only [one_mul] using
    (show (v:ℝ) ≤ m by exact_mod_cast hvm))),Complex.ofReal_zero]

/-- On the lower plateau the transformed correction is actually one. -/
theorem quotient_correction_one (S : ℝ → ℝ)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1) (m v : ℕ) (hv : 0 < v) (hmv : 2*m ≤ v) :
    (S ((m:ℝ)/v):ℂ) = 1 := by
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have hmvR : 2*(m:ℝ) ≤ v := by exact_mod_cast hmv
  rw [hleft _ ((div_le_iff₀ hvR).mpr (by linarith)),Complex.ofReal_one]

/-- Transport the original scales themselves under y=v*x. The seed
argument is v*x; keeping the old lower scale 1 would change the weight. -/
theorem transformed_partition (S : ℝ → ℝ) (K : ℕ) (v x : ℝ) (hv : v ≠ 0) :
    (∑ j ∈ range K, profile S (((2:ℝ)^j/v)⁻¹*x)) = original S K (v*x) := by
  unfold original
  apply sum_congr rfl
  intro j hj
  congr 1
  field_simp

theorem transformed_difference_eventually (S : ℝ → ℝ)
    (hleft : ∀ y ≤ (1/2:ℝ), S y = 1)
    (hright : ∀ y, 1 ≤ y → S y = 0) (v x : ℝ) (hx : 0 < x) :
    ∀ᶠ L : ℕ in atTop, cutoff S L x-original S (L+2) (v*x) = (S (v*x):ℂ) := by
  filter_upwards [cutoff_eventually S hleft hright x hx,
    original_eventually S hleft (v*x)] with L h1 h2
  rw [h1,h2]
  ring

/-- At the transported source lattice x=m/v the correctly transported
low-scale correction vanishes. This does not remove a continuum integral. -/
theorem transformed_lattice_correction (S : ℝ → ℝ)
    (hright : ∀ y, 1 ≤ y → S y = 0) (m v : ℕ) (hm : 0 < m) (hv : 0 < v) :
    (S ((v:ℝ)*((m:ℝ)/v)):ℂ) = 0 := by
  have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [mul_div_cancel₀ _ hvR]
  exact integer_correction_zero S hright m hm

#print axioms original_eq
#print axioms cutoff_difference
#print axioms original_eventually
#print axioms difference_eventually
#print axioms integer_correction_zero
#print axioms quotient_correction_zero
#print axioms quotient_correction_one
#print axioms transformed_partition
#print axioms transformed_difference_eventually
#print axioms transformed_lattice_correction
end XiPrime8845.PRZZPartitionDiscrepancy
