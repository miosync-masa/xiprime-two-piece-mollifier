import PRZZSourceScales
import PRZZActualSupportBoxes
import PRZZInflatedSeven

/-! Effective Type II boxes retain balance after clipping to N. A literal
nonzero cell below N supplies the missing U<=N premise. No Type I cell
is silently classified as Type II. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZEffectiveBalance
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZBranchGrouping
set_option maxHeartbeats 2000000

theorem scale_le (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ) (U : ℝ)
    (hp : ∏ i, (2:ℝ)^(k i) = U) (n : ℕ) (hn : n ≤ N)
    (hz : group N b k univ n ≠ 0) : U ≤ N := by
  have hs := (group_support N b k univ n hz).1
  have hs' : (∏ i, (2:ℝ)^(k i)) ≤ n := by exact_mod_cast hs
  rw [hp] at hs'
  exact hs'.trans (by exact_mod_cast hn)

/-- These are the exact E,Y premises consumed by the seven-term h average. -/
theorem clipped (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (U c : ℝ) (hU : 1 ≤ U) (hUN : U ≤ N)
    (hl : U^(1/4:ℝ) ≤ ∏ i ∈ s, (2:ℝ)^(k i))
    (he : (∏ i ∈ s, (2:ℝ)^(k i+1)) ≤ c*U^(1/2:ℝ))
    (hy : (∏ i ∈ s, (2:ℝ)^(k i+1))*(∏ i ∈ univ \ s, (2:ℝ)^(k i+1)) ≤ c*U) :
    0 ≤ (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ∧
      U^(1/4:ℝ) ≤ (upper N b k s:ℝ) ∧
      (upper N b k s:ℝ) ≤ c*U^(1/2:ℝ) ∧
      (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ≤ c*U := by
  have hupper (t : Finset (Fin b.2.length)) :
      (upper N b k t:ℝ) ≤ ∏ i ∈ t, (2:ℝ)^(k i+1) := by
    exact_mod_cast (min_le_right N (∏ i ∈ t, 2^(k i+1)))
  have hlower : (∏ i ∈ s, (2:ℝ)^(k i)) ≤ ∏ i ∈ s, (2:ℝ)^(k i+1) := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro i hi
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  have hWU : U^(1/4:ℝ) ≤ U := by
    simpa using Real.rpow_le_rpow_of_exponent_le hU (show (1/4:ℝ) ≤ 1 by norm_num)
  have hWN : U^(1/4:ℝ) ≤ N := hWU.trans hUN
  refine ⟨by positivity,?_,(hupper s).trans he,?_⟩
  · change U^(1/4:ℝ) ≤ (min N (∏ i ∈ s, 2^(k i+1)):ℕ)
    push_cast
    exact le_min hWN (hl.trans hlower)
  · exact (mul_le_mul (hupper s) (hupper (univ \ s)) (by positivity) (by positivity)).trans hy

#print axioms scale_le
#print axioms clipped

/-- All nonzero local configurations: a genuine free Type I factor or
effective balanced boxes ready for the seven-term average. -/
theorem local_layout (N K : ℕ) (js : List ℕ) (U : ℝ) (hK : 4 ≤ K)
    (hU : 1 < U) (hlarge : (2:ℝ)^((js.length+1)*(2*K)) ≤ U)
    (b : Branch)
    (hb : b ∈ branches ⌊((2:ℝ)^((js.length+1)*(2*K))*U)^((K:ℝ)⁻¹)⌋₊ K js)
    (k : Fin b.2.length → ℕ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hn : n ≤ N) (hz : group N b k univ n ≠ 0) :
    (∃ i, (∃ J a, PRZZTypedClassification.Free a ∧
      factor b i = PRZZWeightedHeathBrown.weight J (PRZZGroupBounds.atom a)) ∧
      U/U^(1/4:ℝ) < (2:ℝ)^(k i) ∧
      (∏ j ∈ univ.erase i, (2:ℝ)^(k j)) < U^(1/4:ℝ)) ∨
    (∃ s : Finset (Fin b.2.length),
      0 ≤ (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ∧
      U^(1/4:ℝ) ≤ (upper N b k s:ℝ) ∧
      (upper N b k s:ℝ) ≤ (2:ℝ)^((js.length+1)*(2*K))*U^(1/2:ℝ) ∧
      (upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ) ≤ (2:ℝ)^((js.length+1)*(2*K))*U ∧
      group N b k univ = group N b k s*group N b k (univ \ s)) := by
  rcases PRZZSourceScales.local_layout N K js U hK hU hlarge b hb k hp with
    hzero | hi | ⟨s,hl,_,he,hy,hs⟩
  · exact (hz (by rw [hzero]; rfl)).elim
  · exact Or.inl hi
  · obtain ⟨h0,h1,h2,h3⟩ := clipped N b k s U _ hU.le
      (scale_le N b k U hp n hn hz) hl he hy
    exact Or.inr ⟨s,h0,h1,h2,h3,hs⟩

#print axioms local_layout

/-- The clipped actual boxes feed the existing h-decaying seven-term
bound without a new balanced-box hypothesis. -/
theorem seven_decay (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (X h A V c : ℝ)
    (hh : 1 ≤ h) (hX : 0 < X) (hU : 1 ≤ X/h) (hUN : X/h ≤ N)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hc : 1 ≤ c)
    (hl : (X/h)^(1/4:ℝ) ≤ ∏ i ∈ s, (2:ℝ)^(k i))
    (he : (∏ i ∈ s, (2:ℝ)^(k i+1)) ≤ c*(X/h)^(1/2:ℝ))
    (hy : (∏ i ∈ s, (2:ℝ)^(k i+1))*(∏ i ∈ univ \ s, (2:ℝ)^(k i+1)) ≤ c*(X/h)) :
    PRZZDISeven.seven h (upper N b k s) A
        ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V ≤
      c^2*(PRZZDISeven.envelope X A V/h^(3/8:ℝ)) := by
  obtain ⟨h0,h1,h2,h3⟩ := clipped N b k s (X/h) c hU hUN hl he hy
  exact PRZZInflatedSeven.seven_h_bound h _ X _ A V c hh hX h0 hA hV hc h1 h2 h3

#print axioms seven_decay
end XiPrime8845.PRZZEffectiveBalance
