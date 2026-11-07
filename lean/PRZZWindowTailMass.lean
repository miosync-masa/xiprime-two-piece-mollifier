import PRZZWindowGrids
import PRZZNativeFamily

/-! The actual Fourier tail mass on the complete polynomial spatial
window, summed over gcd, both dyadic grids and source gaps. Native label
filters are retained. All bounds are uniform in the exhaustion L. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZWindowTailMass
open PRZZResolvedTailMass PRZZWindowGrids
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def nativePairs (L N d j l k : ℕ) (delta : ℤ) : Finset (ℕ × ℕ) :=
  (PRZZPrefactorMass.pairs N d j l).filter (fun p =>
    -delta ∈ PRZZNativeFamily.gaps L N (d*p.1) (d*p.2) ∧ delta ≠ 0 ∧
      |(delta:ℝ)| ≤ (2:ℝ)^k*p.1/4)

def term (F G W : ℝ → ℂ) (js : List ℕ) (L N d j l k : ℕ)
    (dual : Bool) (T Q V eD eH t : ℝ) (A B : ℂ) (delta : ℤ) : ℝ :=
  if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
    ∑ p ∈ nativePairs L N d j l k delta,
      ‖branch dual A B T t * coeff F G js d Q V T A B (p,(delta,1)) *
        PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B delta 1
          (PRZZCentralTail.residue (p,(delta,1))/p.2) p‖
  else 0

def mass (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ delta ∈ gaps T b eD, term F G W js L N d j l k dual T Q V eD eH t A B delta

theorem outer_card (L N : ℕ) (T b eD : ℝ)
    (hN : 1 ≤ N) (hNT : (N:ℝ) ≤ T) (hb : 0 ≤ b) (he : 0 ≤ eD) :
    ((spatial L T b).card:ℝ) * ((Finset.Icc 1 N).card:ℝ) *
      ((range (Nat.log 2 N+1)).card:ℝ)^2 * ((gaps T b eD).card:ℝ) ≤
        56*T^(2*b+eD+3) := by
  have hT : 1 ≤ T := (by exact_mod_cast hN : (1:ℝ) ≤ N).trans hNT
  have hT0 : 0 < T := by linarith
  have hd : ((Finset.Icc 1 N).card:ℝ) ≤ T := by simpa using hNT
  calc
    _ ≤ (2*T^b)*T*(2*T)^2*(7*T^(b+eD)) := by
      gcongr
      · exact spatial_card L T b hT hb
      · exact dyadic_card N T hN hNT
      · exact gaps_card T b eD hT hb he
    _ = _ := by
      rw [show 2*b+eD+3 = b+(b+eD)+3 by ring]
      simp only [Real.rpow_add hT0]
      norm_num [Real.rpow_natCast]
      ring

theorem absorbed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → Q ≤ 2*T → t ∈ Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Function.support (PRZZMellinSeparation.scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) →
      mass F G W js L N dual T Q V b eD eH t A B ≤ C*T^(-power) := by
  let loss := 2*b+eD+3
  obtain ⟨K,hK,h⟩ := tails_absorbed F G W hF hG hcF hcG hW hsW
    js a b S r eD eH (power+loss) ha hb hS hr heD he
  refine ⟨56*K,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro L N dual Q V t A B hN hNT hQ hQT ht hA hB hsep hsF
  have hT0 : 0 < T := by linarith
  have hterm (k : ℕ) (hk : k ∈ spatial L T b) (d : ℕ) (hd : d ∈ Finset.Icc 1 N)
      (j l : ℕ) (delta : ℤ) :
      term F G W js L N d j l k dual T Q V eD eH t A B delta ≤ K*T^(-(power+loss)) := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
    unfold term
    split_ifs with hg
    · have hp : nativePairs L N d j l k delta ⊆ PRZZPrefactorMass.pairs N d j l :=
        filter_subset _ _
      have hh := h dual N d j l ((2:ℝ)^k) Q V Q t A B (delta,1)
        (nativePairs L N d j l k delta) hN hd1 hNT
        (by have := one_le_pow₀ (n:=k) (show (1:ℝ) ≤ 2 by norm_num); linarith)
        (mem_filter.mp hk).2 hQ ht hA hB hsep hp hsF hg
      exact hh.trans (div_le_self (by positivity) hdR)
    · positivity
  have hs : mass F G W js L N dual T Q V b eD eH t A B ≤
      ((spatial L T b).card:ℝ)*((Finset.Icc 1 N).card:ℝ)*
        ((range (Nat.log 2 N+1)).card:ℝ)^2*((gaps T b eD).card:ℝ)*
          (K*T^(-(power+loss))) := by
    unfold mass
    calc
      _ ≤ ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
          ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
            ∑ delta ∈ gaps T b eD, K*T^(-(power+loss)) := by
        apply sum_le_sum; intro k hk
        apply sum_le_sum; intro d hd
        apply sum_le_sum; intro j hj
        apply sum_le_sum; intro l hl
        apply sum_le_sum; intro delta hg
        exact hterm k hk d hd j l delta
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hc := mul_le_mul_of_nonneg_right (outer_card L N T b eD hN hNT hb heD)
    (show 0 ≤ K*T^(-(power+loss)) by positivity)
  apply hs.trans (hc.trans_eq _)
  dsimp only [loss]
  rw [show 56*T^(2*b+eD+3)*(K*T^(-(power+(2*b+eD+3)))) =
    56*K*(T^(2*b+eD+3)*T^(-(power+(2*b+eD+3)))) by ring]
  rw [← Real.rpow_add hT0]
  congr 2
  ring

#print axioms outer_card
#print axioms absorbed
end XiPrime8845.PRZZWindowTailMass
