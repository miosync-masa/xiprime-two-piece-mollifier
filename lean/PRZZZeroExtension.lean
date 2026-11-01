import PRZZRowPlacement

/-! Zero extension of a retained interval. The left jump is charged once;
the right jump replaces the terminal norm already in the variation. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZZeroExtension
open PRZZTypeI
set_option maxHeartbeats 2000000

theorem prepend (w : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    variation w (n+1) = variation (fun k => w (k+1)) n + ‖w 1-w 0‖ := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [variation, Nat.add_sub_cancel, Nat.succ_sub_one]
  rw [sum_range_succ']
  simp only [Nat.zero_add]
  ring

theorem zero_tail (w : ℕ → ℂ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hw : ∀ k, m ≤ k → w k = 0) : variation w n = variation w m := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn : 0 < n := hm.trans_le hmn
    have he : n-1+1=n := by omega
    simp only [variation, Nat.add_sub_cancel] at *
    rw [← he, sum_range_succ]
    simp only [he, hw n hmn, zero_sub, norm_neg, norm_zero, zero_add]
    linarith [ih]

theorem zero_prefix (w : ℕ → ℂ) (a m : ℕ) (hm : 0 < m)
    (hw : ∀ k < a, w k = 0) :
    variation w (a+m) ≤ variation (fun k => w (a+k)) m + ‖w a‖ := by
  induction a generalizing w with
  | zero => simp only [zero_add]; exact le_add_of_nonneg_right (norm_nonneg _)
  | succ a ih =>
    rw [show a+1+m=(a+m)+1 by omega, prepend w (a+m) (by omega)]
    by_cases ha : a=0
    · subst a
      simp only [zero_add, hw 0 (by omega), sub_zero, Nat.add_comm 1]
      exact le_rfl
    · have h0 := hw 0 (by omega)
      have h1 := hw 1 (by omega)
      have hb := ih (fun k => w (k+1)) (fun k hk => hw (k+1) (by omega))
      simpa only [h0,h1,sub_self,norm_zero,add_zero,Nat.add_assoc,Nat.add_comm 1] using hb

/-- No factor proportional to the ambient interval length is lost. -/
theorem supported (w : ℕ → ℂ) (a m n : ℕ) (hm : 0 < m)
    (hn : a+m ≤ n) (hleft : ∀ k < a, w k = 0)
    (hright : ∀ k, a+m ≤ k → w k = 0) :
    variation w n ≤ variation (fun k => w (a+k)) m + ‖w a‖ := by
  rw [zero_tail w (a+m) n (by omega) hn hright]
  exact zero_prefix w a m hm hleft

#print axioms prepend
#print axioms zero_tail
#print axioms zero_prefix
#print axioms supported

theorem head_le (w : ℕ → ℂ) (m : ℕ) (hm : 0 < m) : ‖w 0‖ ≤ variation w m := by
  induction m generalizing w with
  | zero => omega
  | succ m ih =>
    by_cases hz : m=0
    · subst m; simp [variation]
    · rw [prepend w m (by omega)]
      have hh := ih (fun k => w (k+1)) (by omega)
      have ht := norm_sub_le (w 1) (w 1-w 0)
      rw [sub_sub_cancel] at ht
      have he : ‖w 1-w 0‖ = ‖w 0-w 1‖ := norm_sub_rev _ _
      linarith

theorem actual (N d h j : ℕ) (F : ℝ → ℂ) (alpha : ℂ) (t : ℝ)
    (hd : 0 < d) (hh : 0 < h) (hne : PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j) :
    variation (fun k => PRZZResidualRow.weight N d j h F alpha t (k+1)) N ≤
      2*variation (fun k => PRZZResidualRow.weight N d j h F alpha t (PRZZRowWindow.lo h j+k))
        (PRZZRowPlacement.span N d h j) := by
  have hl : 1 ≤ PRZZRowWindow.lo h j := Nat.succ_le_succ (Nat.zero_le _)
  have hu := PRZZRowPlacement.upper_le N d h j hh
  have hm : 0 < PRZZRowPlacement.span N d h j := by unfold PRZZRowPlacement.span; omega
  have hb := supported (fun k => PRZZResidualRow.weight N d j h F alpha t (k+1))
    (PRZZRowWindow.lo h j-1) (PRZZRowPlacement.span N d h j) N hm
    (by unfold PRZZRowPlacement.span; omega)
    (by intro k hk; rw [PRZZRowWindow.weight_eq N d h j hd hh];
        simp [PRZZMaskedVariation.mask,show ¬PRZZRowWindow.lo h j ≤ k+1 by omega])
    (by intro k hk; rw [PRZZRowWindow.weight_eq N d h j hd hh];
        have hn : PRZZRowWindow.hi N d h j < k+1 := by unfold PRZZRowPlacement.span at hk; omega
        simp [PRZZMaskedVariation.mask,not_le.mpr hn])
  have he (k : ℕ) : PRZZRowWindow.lo h j-1+k+1=PRZZRowWindow.lo h j+k := by omega
  simp only [he, Nat.sub_add_cancel hl] at hb
  have hh := head_le (fun k => PRZZResidualRow.weight N d j h F alpha t (PRZZRowWindow.lo h j+k)) _ hm
  simp only [Nat.add_zero] at hh
  linarith

#print axioms head_le
#print axioms actual

/-- Uniform in the original ambient N, including both sharp cutoffs and
empty rows. This is the whole-row variation required by weighted DI. -/
theorem full_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      variation (fun k => PRZZResidualRow.weight N d j h
        (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (k+1)) N ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := PRZZRowPlacement.retained_variation F0 hf hc eps S Z heps hS hZ
  refine ⟨2*C,by positivity,?_⟩
  intro N d h j T Q t alpha hd hh hT hNT hhT ha hz
  by_cases hne : PRZZRowWindow.lo h j ≤ PRZZRowWindow.hi N d h j
  · exact (actual N d h j _ alpha t hd hh hne).trans
      ((mul_le_mul_of_nonneg_left (hv N d h j T Q t alpha hd hh hT hNT hhT ha hz hne)
        (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
  · rw [PRZZRowPlacement.empty_row N d h j hd hh (lt_of_not_ge hne)]
    simp only [Pi.zero_apply,sub_self,norm_zero,sum_const_zero,add_zero,variation]
    positivity

#print axioms full_variation

/-- The smooth actual row can now be inserted into the incomplete Weil
adapter. This does not assert the extra arithmetic masks of every Type I
branch have already been reduced to this literal inverse-phase sum. -/
theorem weil_row (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j q : ℕ, ∀ a : ℤ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ q → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖weightedSum q a 0 N (fun k => PRZZResidualRow.weight N d j h
        (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (k+1))‖ ≤
      C*Real.rpow q (1/2+eta)*(a.natAbs.gcd q)*(1+(N:ℝ)/q)*(1+|t|)*T^eps := by
  obtain ⟨Cw,hCw,hw⟩ := weighted_bound hWeil eta heta
  obtain ⟨Cv,hCv,hv⟩ := full_variation F0 hf hc eps S Z heps hS hZ
  refine ⟨Cw*Cv,by positivity,?_⟩
  intro N d h j q a T Q t alpha hd hh hq hT hNT hhT ha hz
  apply (hw q hq a 0 N _).trans
  exact (mul_le_mul_of_nonneg_left (hv N d h j T Q t alpha hd hh hT hNT hhT ha hz)
    (mul_nonneg (mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (Nat.cast_nonneg _)) (by positivity))).trans_eq (by simp only [Real.rpow_eq_pow]; ring)

#print axioms weil_row
end XiPrime8845.PRZZZeroExtension
