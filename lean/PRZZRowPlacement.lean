import PRZZActualRowSmooth

/-! The original dyadic and product restrictions supply the sampling
interval; no interval placement is assumed. Empty rows are kept separate.
The modest height room N+1<=T is explicit. -/
noncomputable section
open scoped ContDiff
namespace XiPrime8845.PRZZRowPlacement
open PRZZRowWindow PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem upper_le (N d h j : ℕ) (_hh : 0 < h) : hi N d h j ≤ N :=
  (min_le_left _ _).trans (Nat.div_le_self _ _)

theorem narrow (N d h j : ℕ) (hh : 0 < h) : hi N d h j < 2*lo h j := by
  have hlow : 2^j-1 < h*lo h j := by
    have hl : (2^j-1)/h < lo h j := by unfold lo; omega
    have hx := (Nat.div_lt_iff_lt_mul hh).mp hl
    nlinarith
  have hu : hi N d h j ≤ (2^(j+1)-1)/h := (min_le_right _ _).trans (min_le_left _ _)
  have hu' := (Nat.le_div_iff_mul_le hh).mp hu
  have hp : 0 < (2:ℕ)^j := by positivity
  have hp2 : 0 < (2:ℕ)^(j+1) := by positivity
  have he : (2:ℕ)^(j+1) = 2*2^j := by ring
  have hs : 2^j-1+1 = (2:ℕ)^j := Nat.sub_add_cancel (by omega)
  have hs2 : 2^(j+1)-1+1 = (2:ℕ)^(j+1) := Nat.sub_add_cancel (by omega)
  nlinarith

def span (N d h j : ℕ) := hi N d h j-lo h j+1

theorem placement (N d h j : ℕ) (T : ℝ) (hh : 0 < h)
    (hne : lo h j ≤ hi N d h j) (hNT : (N:ℝ)+1 ≤ T) :
    1 ≤ lo h j ∧ (0:ℝ) < lo h j ∧
    (lo h j:ℝ)+span N d h j ≤ T ∧ (span N d h j:ℝ) ≤ 2*lo h j := by
  have hl : (1:ℕ) ≤ lo h j := Nat.succ_le_succ (Nat.zero_le _)
  have he : lo h j+span N d h j = hi N d h j+1 := by unfold span; omega
  have hu := upper_le N d h j hh
  have hn := narrow N d h j hh
  refine ⟨hl,by exact_mod_cast hl,?_,?_⟩
  · have hcast : (lo h j:ℝ)+span N d h j ≤ (N:ℝ)+1 := by exact_mod_cast (show lo h j+span N d h j ≤ N+1 by omega)
    exact hcast.trans hNT
  · exact_mod_cast (show span N d h j ≤ 2*lo h j by omega)

theorem empty_row (N d h j : ℕ) (hd : 0 < d) (hh : 0 < h)
    (he : hi N d h j < lo h j) (F1 : ℝ → ℂ) (alpha : ℂ) (t : ℝ) :
    PRZZResidualRow.weight N d j h F1 alpha t = 0 := by
  rw [weight_eq N d h j hd hh]
  funext n
  have hn : ¬ (lo h j ≤ n ∧ n ≤ hi N d h j) := by omega
  simp [PRZZMaskedVariation.mask,hn]

/-- Every nonempty original row supplies the large-interval hypotheses.
The returned bound is for its whole retained interval, not an arbitrary sample. -/
theorem retained_variation (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      lo h j ≤ hi N d h j →
      PRZZTypeI.variation (fun k => PRZZResidualRow.weight N d j h
        (scaledCutoff F0 Q) alpha t (lo h j+k)) (span N d h j) ≤ C*(1+|t|)*T^eps := by
  obtain ⟨C,hC,hv⟩ := PRZZActualRowSmooth.sampled_variation F0 hf hc eps S Z heps hS hZ
  refine ⟨C,hC,?_⟩
  intro N d h j T Q t alpha hd hh hT hNT hhT ha hz hne
  have hp := placement N d h j T hh hne hNT
  exact hv N d j h (lo h j) (span N d h j) T Q (lo h j) t alpha hd hh hp.1 hne
    hT hhT hp.2.1 le_rfl hp.2.2.1 hp.2.2.2 ha hz

#print axioms upper_le
#print axioms narrow
#print axioms placement
#print axioms empty_row
#print axioms retained_variation
end XiPrime8845.PRZZRowPlacement
