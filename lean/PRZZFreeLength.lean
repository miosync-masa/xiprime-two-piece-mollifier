import PRZZModulusBudget

/-! Shorten the Weil interval without changing the original analytic row.
Both the free dyadic endpoint and the original product cutoff are retained.
This supplies the effective Type I length, not a seven-term comparison. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeLength
open PRZZTypeI PRZZTypeICoprime PRZZFreeSource PRZZFreeDyadic
set_option maxHeartbeats 2000000

def endpoint (N d h e r : ℕ) : ℕ :=
  min N (min (2^(r+1)-1) (N/(d*(h*e))))

theorem vanishes (N d j h e r m : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ)
    (hd : 0 < d) (hh : 0 < h) (he : 0 < e) (n : ℕ)
    (hn : endpoint N d h e r < n) : freeWeight N d j h e r m F0 Q t alpha n = 0 := by
  by_cases hc : n ∈ PRZZDyadic.cell N r
  · have hnN := (mem_Icc.mp (mem_filter.mp hc).1).2
    have hnr := hc
    rw [PRZZDyadic.mem_cell] at hnr
    have hp : ¬ d*((h*e)*n) ≤ N := by
      intro hp
      have hdiv : n ≤ N/(d*(h*e)) := (Nat.le_div_iff_mul_le (by positivity)).mpr
        (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hp)
      unfold endpoint at hn
      omega
    simp [freeWeight,hc,PRZZFreeLogCoprime.row,PRZZResidualRow.weight,hp]
  · simp [freeWeight,hc]

theorem restrict_eq (d q N M : ℕ) (hMN : M ≤ N) (a : ℤ) (w : ℕ → ℂ)
    (hw : ∀ n, M < n → w n = 0) :
    restrictedSum d q N a w = restrictedSum d q M a w := by
  unfold restrictedSum
  symm
  apply sum_subset (fun n hn => mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hMN⟩)
  intro n hn hnM
  have hnm : M < n := by have := mem_Icc.mp hn; simp only [mem_Icc] at hnM; omega
  simp [hw n hnm]

/-- Prefix cancellation pays only the effective endpoint. The original
full-row variation is unchanged, so neither support jump is lost. -/
theorem supported_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q N M : ℕ, d ≠ 0 → 1 ≤ q → M ≤ N →
      ∀ a : ℤ, ∀ w : ℕ → ℂ, (∀ n, M < n → w n = 0) →
      ‖restrictedSum d q N a w‖ ≤
        C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.natAbs.gcd q:ℝ)*
          (1+(M:ℝ)/q)*variation (fun j => w (j+1)) N := by
  obtain ⟨C,hC,h⟩ := PRZZTypeICost.weighted_bound hWeil eps heps
  refine ⟨C,hC,?_⟩
  intro d q N M hd hq hMN a w hw
  rw [restrict_eq d q N M hMN a w hw]
  by_cases hM : M=0
  · subst M
    simp only [restrictedSum,Icc_eq_empty_of_lt (by omega : 0 < (1:ℕ)),sum_empty,norm_zero]
    have hv : 0 ≤ variation (fun j => w (j+1)) N := by unfold variation; positivity
    have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
    positivity
  · have hv := PRZZZeroExtension.zero_tail (fun j => w (j+1)) M N
      (Nat.pos_of_ne_zero hM) hMN (fun j hj => hw (j+1) (by omega))
    rw [hv]
    exact h d q M hd hq a w

theorem transformed_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h e r m q : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ, ∀ k : ℤ,
      0 < d → 0 < h → 0 < e → m ≤ J → 1 ≤ q → (h*e).Coprime q →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖restrictedSum d q N
        ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
        (freeWeight N d j h e r m F0 Q t alpha)‖ ≤
      C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(k.natAbs.gcd q:ℝ)*
        (1+(endpoint N d h e r:ℝ)/q)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := supported_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := variation_bound F0 hf hc J eta S Z heta hS hZ
  refine ⟨Cw*Cv,by positivity,?_⟩
  intro N d j h e r m q T Q t alpha k hd hh he hm hq hcop hT hNT ha hz
  have hb := hw d q N (endpoint N d h e r) hd.ne' hq (min_le_left _ _)
    ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
    (freeWeight N d j h e r m F0 Q t alpha)
    (vanishes N d j h e r m F0 Q t alpha hd hh he)
  rw [slice_frequency_gcd q h e (by omega) hcop k] at hb
  apply hb.trans
  have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
  exact (mul_le_mul_of_nonneg_left
    (hv N d j h e r m T Q t alpha hd hh he hm hT hNT ha hz)
    (by positivity)).trans_eq (by ring)

#print axioms vanishes
#print axioms restrict_eq
#print axioms supported_bound
#print axioms transformed_bound
end XiPrime8845.PRZZFreeLength
