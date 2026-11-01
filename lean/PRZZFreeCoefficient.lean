import PRZZFreeDyadic
import PRZZSourceCoefficients

/-! Literal right coefficients in the free Type I slice. The d*q cutoff
is used before applying the coefficient envelope. The signed frequency
coefficient is bounded uniformly; the modulus/gcd budget remains explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZFreeCoefficient
open PRZZFreeSource PRZZMellinSeparation PRZZKloostermanInputs
set_option maxHeartbeats 2000000

def slice (N d j l h e r m : ℕ) (js : List ℕ) (F0 F2 FM : ℝ → ℂ)
    (Q x t : ℝ) (alpha beta : ℂ) (k : ℤ) : ℂ :=
  ∑ n ∈ Icc 1 N, if d.Coprime (e*n) ∧ d*(h*(e*n)) ≤ N then
    (if n ∈ PRZZDyadic.cell N r then (Real.log n:ℂ)^m else 0) *
      PRZZSupportedBranches.row N d j l (fun _ => 1)
        (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
        (scaledCutoff F0 Q) F2 FM alpha beta x t k (h*(e*n))
    else 0

def modulusBudget (eps : ℝ) (N d l : ℕ) (k : ℤ) : ℝ :=
  ∑ q ∈ PRZZDyadic.cell N l,
    Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(k.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q)

theorem modulusBudget_nonneg (eps : ℝ) (N d l : ℕ) (k : ℤ) :
    0 ≤ modulusBudget eps N d l k := by
  apply sum_nonneg
  intro q hq
  have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
  positivity

theorem slice_bound (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j l h e r m : ℕ, ∀ T Q x t : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*modulusBudget eps N d l k := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZFreeDyadic.transformed_bound hWeil F0 hf hc J eps eta S Z
    heps heta hS hZ
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient js eta S heta hS
    F2 FM hF hcF hM hcM
  refine ⟨Cr*Cw,mul_pos hCr hCw,?_⟩
  intro N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb
  rw [slice,PRZZFreeSource.slice_eq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ PRZZDyadic.cell N l,
        (Cr*T^eta)*(Cw*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*
          (k.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q)*(1+|t|)*T^eta) := by
      apply sum_le_sum
      intro q hq
      by_cases hg : d.Coprime e ∧ (h*e).Coprime q ∧ d*q ≤ N
      · rw [if_pos hg,norm_mul]
        have hrq := hr N d l hN hd T x t hT (by linarith) beta hb q
        rw [PRZZAStarRectangles.secondCoeff,if_pos (And.intro hq hg.2.2)] at hrq
        exact mul_le_mul hrq
          (hw N d j h e r m q T Q t alpha k hd hh he hm
            (mem_Icc.mp (mem_filter.mp hq).1).1 hg.2.1 hT hNT ha hz)
          (norm_nonneg _) (by positivity)
      · rw [if_neg hg,norm_zero]
        have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
        positivity
    _ = _ := by
      unfold modulusBudget
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring

/-- Both signs and the original frequency set are covered. This is an
actual coefficient supplier, not a hypothesis on nu or on the right side. -/
theorem nu_slice_bound (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T → k ≠ 0 →
      ‖PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
        slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(k.natAbs:ℝ)^eta*(1+|t|)*(T^eta*T^eta)*modulusBudget eps N d l k := by
  obtain ⟨C,hC,hbound⟩ := slice_bound hWeil F0 F2 FM hf hc hF hcF hM hcM js J eps eta S Z
    heps heta hS hZ
  obtain ⟨D,hD,hn⟩ := PRZZNuBounds.nu_subpower eta heta
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro N d j l h e r m T Q x y t D0 H alpha beta k hN hd hh he hm hT hNT ha hz hb hk
  rw [norm_mul]
  exact (mul_le_mul
    (hn _ (PRZZAStarNu.frequency_positive_h d D0 H) x y k hk)
    (hbound N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Aggregate the complete original signed frequency image; no frequency
is dropped and repeated source pairs remain in nu. -/
theorem signed_slice_bound (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
          slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*
          ∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (k.natAbs:ℝ)^eta*modulusBudget eps N d l k := by
  obtain ⟨C,hC,hbound⟩ := nu_slice_bound hWeil F0 F2 FM hf hc hF hcF hM hcM
    js J eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro N d j l h e r m T Q x y t D H alpha beta hN hd hh he hm hT hNT ha hz hb
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  exact (hbound N d j l h e r m T Q x y t D H alpha beta k hN hd hh he hm
    hT hNT ha hz hb (PRZZAStarNu.frequency_ne_zero d D H k hk)).trans_eq (by ring)

#print axioms signed_slice_bound
#print axioms modulusBudget_nonneg
#print axioms slice_bound
#print axioms nu_slice_bound
end XiPrime8845.PRZZFreeCoefficient
