import PRZZFreeSource

/-! Uniform variation for the extra free-factor dyadic mask. No arbitrary
subset cancellation is used. The inverse-product gcd is unchanged. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeDyadic
open PRZZTypeI PRZZFreeSource
set_option maxHeartbeats 2000000

theorem point_le (w : ℕ → ℂ) (H k : ℕ) (hk : k < H) : ‖w k‖ ≤ variation w H := by
  induction H generalizing w k with
  | zero => omega
  | succ H ih =>
    cases k with
    | zero => exact PRZZZeroExtension.head_le w _ (by omega)
    | succ k =>
      rw [PRZZZeroExtension.prepend w H (by omega)]
      exact (ih (fun n => w (n+1)) k (by omega)).trans
        (le_add_of_nonneg_right (norm_nonneg _))

theorem dyadic_mask (N d j h e r m : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ)
    (hN : 0 < N) :
    (fun k => freeWeight N d j h e r m F0 Q t alpha (k+1)) =
      PRZZMaskedVariation.mask (2^r-1) (min (N-1) (2^(r+1)-2))
        (fun k => PRZZFreeLogCoprime.row N d j (h*e) m F0 Q t alpha (k+1)) := by
  funext k
  have hp : 0 < 2^r := pow_pos (by norm_num) _
  have hp' : 2 ≤ 2^(r+1) := by rw [pow_succ]; omega
  unfold freeWeight PRZZMaskedVariation.mask
  apply if_congr _ rfl rfl
  rw [PRZZDyadic.mem_cell,mem_Icc]
  omega

theorem variation_bound (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J : ℕ) (eta S Z : ℝ)
    (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h e r m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 0 < e → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => freeWeight N d j h e r m F0 Q t alpha (k+1)) N ≤
        C*(1+|t|)*T^eta := by
  obtain ⟨C,hC,hv⟩ := PRZZFreeLogCoprime.full_variation F0 hf hc J eta S Z heta hS hZ
  refine ⟨3*C,by positivity,?_⟩
  intro N d j h e r m T Q t alpha hd hh he hm hT hNT ha hz
  by_cases hN : N=0
  · subst N
    simp [variation,freeWeight,PRZZDyadic.cell]
    positivity
  have hN : 0 < N := Nat.pos_of_ne_zero hN
  let w := fun k => PRZZFreeLogCoprime.row N d j (h*e) m F0 Q t alpha (k+1)
  have hv' : variation w N ≤ C*(1+|t|)*T^eta :=
    hv N d j (h*e) m T Q t alpha hd (Nat.mul_pos hh he) hm hT hNT ha hz
  have hwN : w N = 0 := by
    have hp : N < (h*e)*(N+1) := by nlinarith [Nat.mul_pos hh he]
    have hn : (h*e)*(N+1) ∉ PRZZDyadic.cell N j := by
      intro hn
      exact (not_le.mpr hp) (mem_Icc.mp (mem_filter.mp hn).1).2
    simp [w,PRZZFreeLogCoprime.row,PRZZResidualRow.weight,hn]
  have hw : ∀ k ≤ N, ‖w k‖ ≤ C*(1+|t|)*T^eta := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact (point_le w N k hk).trans hv'
    · rw [hwN,norm_zero]; positivity
  rw [dyadic_mask N d j h e r m F0 Q t alpha hN]
  exact (PRZZMaskedVariation.mask_of_variation _ _ N w _ _
    (by positivity) hw hv').trans_eq (by ring)

theorem transformed_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h e r m q : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ, ∀ k : ℤ,
      0 < d → 0 < h → 0 < e → m ≤ J → 1 ≤ q → (h*e).Coprime q →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖PRZZTypeICoprime.restrictedSum d q N
        ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
        (freeWeight N d j h e r m F0 Q t alpha)‖ ≤
      C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(k.natAbs.gcd q:ℝ)*
        (1+(N:ℝ)/q)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZTypeICost.weighted_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := variation_bound F0 hf hc J eta S Z heta hS hZ
  refine ⟨Cw*Cv,by positivity,?_⟩
  intro N d j h e r m q T Q t alpha k hd hh he hm hq hcop hT hNT ha hz
  have hb := hw d q N hd.ne' hq
    ((-k)*(PRZZKloostermanInputs.inverseResidue q (h*e):ℤ))
    (freeWeight N d j h e r m F0 Q t alpha)
  rw [slice_frequency_gcd q h e (by omega) hcop k] at hb
  apply hb.trans
  exact (mul_le_mul_of_nonneg_left
    (hv N d j h e r m T Q t alpha hd hh he hm hT hNT ha hz)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCw.le
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (by positivity))).trans_eq (by simp only [Real.rpow_eq_pow]; ring)

#print axioms point_le
#print axioms dyadic_mask
#print axioms variation_bound
#print axioms transformed_bound
/-- A literal source slice, including its unchanged right coefficients.
The right-index sum is explicit: it has not been replaced by a uniform
coefficient envelope or by the final seven-term budget. -/
theorem slice_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j l h e r m : ℕ, ∀ b : ℕ → ℂ,
      ∀ F2 FM : ℝ → ℂ, ∀ T Q x t : ℝ, ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖∑ n ∈ Icc 1 N, if d.Coprime (e*n) ∧ d*(h*(e*n)) ≤ N then
        (if n ∈ PRZZDyadic.cell N r then (Real.log n:ℂ)^m else 0) *
          PRZZSupportedBranches.row N d j l (fun _ => 1) b
            (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t k (h*(e*n))
        else 0‖ ≤
      ∑ q ∈ PRZZDyadic.cell N l,
        ‖star (b (d*q))*F2 (d*q)*FM (x*q)/(q:ℂ)^beta*PRZZMellinSeparation.twist q t‖ *
        (C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(k.natAbs.gcd q:ℝ)*
          (1+(N:ℝ)/q)*(1+|t|)*T^eta) := by
  obtain ⟨C,hC,hb⟩ := transformed_bound hWeil F0 hf hc J eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro N d j l h e r m b F2 FM T Q x t alpha beta k hd hh he hm hT hNT ha hz
  rw [slice_eq]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  by_cases hg : d.Coprime e ∧ (h*e).Coprime q ∧ d*q ≤ N
  · rw [if_pos hg,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hb N d j h e r m q T Q t alpha k hd hh he hm
        (mem_Icc.mp (mem_filter.mp hq).1).1 hg.2.1 hT hNT ha hz) (norm_nonneg _)
  · rw [if_neg hg,norm_zero]
    have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
    positivity

#print axioms slice_bound

end XiPrime8845.PRZZFreeDyadic
