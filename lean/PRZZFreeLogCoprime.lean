import PRZZFreeLogRow
import PRZZTypeICost

/-! Logarithmic free rows with both coprimality conditions retained.
The whole-row variation includes both jumps of the sharp support.
Weil remains an explicit hypothesis; no all-branch assignment is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeLogCoprime
open PRZZTypeI PRZZFreeLogRow
set_option maxHeartbeats 2000000

def row (N d j h m : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ) (n : ℕ) : ℂ :=
  (Real.log n:ℂ)^m*PRZZResidualRow.weight N d j h
    (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t n

theorem shift_eq (N d j h a m : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ) :
    (fun k => row N d j h m F0 Q t alpha (a+k)) =
      sample N d j h a m F0 Q t alpha := by
  funext k
  simp [row,sample,Nat.cast_add]

theorem full_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j h m : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 < T → (N:ℝ)+1 ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => row N d j h m F0 Q t alpha (k+1)) N ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := retained_variation F0 hf hc J eps S Z heps hS hZ
  refine ⟨2*C,by positivity,?_⟩
  intro N d j h m T Q t alpha hd hh hm hT hNT ha hz
  by_cases hne : PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j
  · have hl : 1 ≤ PRZZRowWindow.lo h j := Nat.succ_le_succ (Nat.zero_le _)
    have hu := PRZZRowPlacement.upper_le N d h j hh
    have hs : 0 < PRZZRowPlacement.span N d h j := by unfold PRZZRowPlacement.span; omega
    have hb := PRZZZeroExtension.supported (fun k => row N d j h m F0 Q t alpha (k+1))
      (PRZZRowWindow.lo h j-1) (PRZZRowPlacement.span N d h j) N hs
      (by unfold PRZZRowPlacement.span; omega)
      (by intro k hk; unfold row; rw [PRZZRowWindow.weight_eq N d h j hd hh]
          simp [PRZZMaskedVariation.mask,show ¬PRZZRowWindow.lo h j ≤ k+1 by omega])
      (by intro k hk; unfold row; rw [PRZZRowWindow.weight_eq N d h j hd hh]
          have hn : PRZZRowWindow.hi N d h j < k+1 := by unfold PRZZRowPlacement.span at hk; omega
          simp [PRZZMaskedVariation.mask,not_le.mpr hn])
    have he (k : ℕ) : PRZZRowWindow.lo h j-1+k+1=PRZZRowWindow.lo h j+k := by omega
    simp only [he,Nat.sub_add_cancel hl] at hb
    have hh' := PRZZZeroExtension.head_le
      (fun k => row N d j h m F0 Q t alpha (PRZZRowWindow.lo h j+k)) _ hs
    simp only [Nat.add_zero] at hh'
    have hv' := hv N d j h m T Q t alpha hd hh hm hT hNT hne ha hz
    rw [← shift_eq] at hv'
    nlinarith
  · have he := PRZZRowPlacement.empty_row N d h j hd hh (lt_of_not_ge hne)
    simp only [row,he,Pi.zero_apply,mul_zero,variation,sub_self,norm_zero,sum_const_zero,add_zero]
    positivity

#print axioms shift_eq
#print axioms full_variation
theorem frequency_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete) (F0 : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (J : ℕ) (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j m q A : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 ≤ q → 1 < T → (N:ℝ)+1 ≤ T →
      (d:ℝ) ≤ T → (q:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ∀ sign : ℤ, sign.natAbs = 1 →
      (∑ a ∈ Icc 1 A, ‖PRZZTypeICoprime.restrictedSum d q N (sign*(a:ℤ))
        (row N d j h m F0 Q t alpha)‖) ≤
        C*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZTypeICost.frequency_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := full_variation F0 hf hcF J (eta/2) S Z (by positivity) hS hZ
  obtain ⟨Cd,hCd,hdv⟩ := PRZZTypeICost.divisor_pair_absorbed (eta/2) (by positivity)
  refine ⟨Cw*Cd*Cv,by positivity,?_⟩
  intro N d h j m q A T Q t alpha hd hh hm hq hT hNT hdT hqT ha hz sign hs
  let w := row N d j h m F0 Q t alpha
  let B := Cw*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg
    (mul_nonneg hCw.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (by positivity)) (Nat.cast_nonneg _)
  have hv0 : 0 ≤ variation (fun n => w (n+1)) N := by unfold variation; positivity
  have hv' := hv N d j h m T Q t alpha hd hh hm hT hNT ha hz
  have hd' := hdv d q hd (by omega) T hdT hqT
  have he : T^(eta/2)*T^(eta/2) = T^eta := by
    rw [← Real.rpow_add (by linarith : 0 < T)]; congr 1; ring
  calc
    _ ≤ B*((d.divisors.card:ℝ)*q.divisors.card)*variation (fun n => w (n+1)) N :=
      (hw d q N A hd.ne' hq sign hs w).trans_eq (by dsimp [B]; ring)
    _ ≤ B*(Cd*T^(eta/2))*(Cv*(1+|t|)*T^(eta/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd' hB) hv' hv0 (mul_nonneg hB (by positivity))
    _ = _ := by
      calc
        _ = (Cw*Cd*Cv)*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)*(1+|t|)*
            (T^(eta/2)*T^(eta/2)) := by dsimp [B]; ring
        _ = _ := by rw [he]

#print axioms frequency_bound

/-- On a bounded local support all logarithmic degrees have a fixed finite
envelope. The constant is independent of height, cutoff scale and frequency. -/
theorem small_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J M : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d j h m H : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → m ≤ J → 1 < T → (N:ℝ) ≤ T →
      PRZZRowWindow.hi N d h j ≤ M → |alpha.re| ≤ S/Real.log T →
      variation (fun k => row N d j h m F0 Q t alpha (k+1)) H ≤ C := by
  obtain ⟨C0,C1,h0,h1,hb⟩ := PRZZSmoothWeights.cutoff_bounds F0 hf hc
  let L : ℝ := ∑ n ∈ range (M+1), ∑ m ∈ range (J+1), ‖(Real.log n:ℂ)^m‖
  have hL : 0 ≤ L := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨(1+2*(M:ℝ))*(L*(C0*Real.exp S)),by positivity,?_⟩
  intro N d j h m H T Q t alpha hd hh hm hT hNT hi ha
  have hzrow (n : ℕ) (hn : M < n) : row N d j h m F0 Q t alpha n = 0 := by
    unfold row
    rw [PRZZRowWindow.weight_eq N d h j hd hh]
    simp [PRZZMaskedVariation.mask,not_le.mpr (hi.trans_lt hn)]
  apply PRZZSmallRowVariation.supported_variation _ M H _ (by positivity) _ hzrow
  intro n
  by_cases hn : n ≤ M
  · have hl1 : ‖(Real.log n:ℂ)^m‖ ≤ ∑ k ∈ range (J+1), ‖(Real.log n:ℂ)^k‖ :=
      single_le_sum (fun k _ => norm_nonneg _) (mem_range.mpr (by omega))
    have hl2 : (∑ k ∈ range (J+1), ‖(Real.log n:ℂ)^k‖) ≤ L := by
      unfold L
      exact single_le_sum (f := fun n : ℕ => ∑ k ∈ range (J+1), ‖(Real.log n:ℂ)^k‖)
        (fun k _ => sum_nonneg (fun _ _ => norm_nonneg _)) (mem_range.mpr (by omega))
    have hl := hl1.trans hl2
    unfold row
    rw [norm_mul]
    apply mul_le_mul hl _ (norm_nonneg _) hL
    unfold PRZZResidualRow.weight
    split_ifs with hmask
    · have hs := (PRZZDyadic.mem_cell N j (h*n)).mp hmask.1
      have hp : 0 < h*n := (mem_Icc.mp hs.1).1
      have hx : (h*n:ℝ) ∈ Set.Icc 1 T := ⟨by exact_mod_cast hp,
        (by exact_mod_cast (mem_Icc.mp hs.1).2 : (h*n:ℝ) ≤ N).trans hNT⟩
      have hz := PRZZSourceCoefficients.inverse_shift T S (h*n) alpha hT hS hx ha
      rw [div_eq_mul_inv,norm_mul,norm_mul,
        PRZZMellinSeparation.twist_norm _ _ (by exact_mod_cast hp),mul_one]
      exact mul_le_mul (hb Q _).1
        (by simpa only [Nat.cast_mul,Complex.ofReal_mul,Complex.ofReal_natCast] using hz)
        (norm_nonneg _) h0
    · simp only [norm_zero]; positivity
  · rw [hzrow n (lt_of_not_ge hn),norm_zero]; positivity

#print axioms small_variation

end XiPrime8845.PRZZFreeLogCoprime
