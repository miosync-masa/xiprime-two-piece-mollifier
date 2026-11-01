import PRZZResidualRow
import PRZZMaskedVariation
import PRZZSourceCoefficients

/-! The literal dyadic/product mask in the source row is one integer
interval. Thus its sharp edges cost two jumps, not one jump per summand. -/
noncomputable section
namespace XiPrime8845.PRZZRowWindow
open PRZZResidualRow PRZZMaskedVariation PRZZMellinSeparation
set_option maxHeartbeats 2000000

def lo (h j : ℕ) : ℕ := (2^j-1)/h+1
def hi (N d h j : ℕ) : ℕ := min (N/h) (min ((2^(j+1)-1)/h) (N/(d*h)))

theorem test (N d h j n : ℕ) (hd : 0 < d) (hh : 0 < h) :
    (h*n ∈ PRZZDyadic.cell N j ∧ d*(h*n) ≤ N) ↔
      lo h j ≤ n ∧ n ≤ hi N d h j := by
  have hl : lo h j ≤ n ↔ 2^j ≤ h*n := by
    unfold lo
    rw [Nat.succ_le_iff,Nat.div_lt_iff_lt_mul hh]
    have hp : 0 < (2:ℕ)^j := by positivity
    rw [Nat.mul_comm n h]
    omega
  have hu : n ≤ hi N d h j ↔ h*n ≤ N ∧ h*n < 2^(j+1) ∧ d*(h*n) ≤ N := by
    simp only [hi,le_min_iff,Nat.le_div_iff_mul_le hh,Nat.le_div_iff_mul_le (Nat.mul_pos hd hh)]
    have hp : 0 < (2:ℕ)^(j+1) := by positivity
    simp only [Nat.mul_comm n h,show n*(d*h)=d*(h*n) by ring]
    omega
  rw [hl,hu,PRZZDyadic.mem_cell]
  simp only [Finset.mem_Icc]
  have hp : 1 ≤ (2:ℕ)^j := Nat.succ_le_of_lt (by positivity)
  omega

theorem weight_eq (N d h j : ℕ) (hd : 0 < d) (hh : 0 < h)
    (F1 : ℝ → ℂ) (α : ℂ) (t : ℝ) :
    weight N d j h F1 α t = mask (lo h j) (hi N d h j)
      (fun n => F1 (d*(h*n))/((h*n:ℕ):ℂ)^α*twist (h*n) t) := by
  funext n
  simp only [weight,mask,test N d h j n hd hh]

/-- A single cutoff norm controls the actual row amplitude at every
height and Mellin frequency. Only the small real shift enters the bound. -/
theorem weight_bound (F1 : ℝ → ℂ) (hf : Continuous F1) (hs : HasCompactSupport F1)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d j h : ℕ, ∀ T t : ℝ, ∀ α : ℂ,
      1 < T → (N:ℝ) ≤ T → |α.re| ≤ S/Real.log T → ∀ n : ℕ,
      ‖weight N d j h F1 α t n‖ ≤ C*Real.exp S := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hf
  have hc : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hc,?_⟩
  intro N d j h T t α hT hNT hα n
  unfold weight
  split_ifs with hm
  · have hn := (PRZZDyadic.mem_cell N j (h*n)).mp hm.1
    have hp : 0 < (h*n:ℕ) := (Finset.mem_Icc.mp hn.1).1
    have hx : (h*n:ℝ) ∈ Set.Icc 1 T := ⟨by exact_mod_cast hp,
      (by exact_mod_cast (Finset.mem_Icc.mp hn.1).2 : (h*n:ℝ) ≤ N).trans hNT⟩
    have hb := PRZZSourceCoefficients.inverse_shift T S (h*n) α hT hS hx hα
    rw [div_eq_mul_inv,norm_mul,norm_mul,twist_norm _ _ (by exact_mod_cast hp),mul_one]
    exact mul_le_mul (hC _) (by simpa only [Nat.cast_mul,Complex.ofReal_mul,Complex.ofReal_natCast] using hb) (norm_nonneg _) hc
  · simp only [norm_zero]; positivity

#print axioms weight_bound
#print axioms test
#print axioms weight_eq
end XiPrime8845.PRZZRowWindow
