import PRZZBranchSeven
import PRZZSourceAbsorption
import PRZZAStarRectangles

/-! Envelopes for the literal source nu and second coordinate r.
The arithmetic coefficient, strict frequency cutoffs, conjugation,
dyadic mask and d*n cutoff are retained. Constants precede T,x,y,t. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZSourceCoefficients
open PRZZAStarNu PRZZNuCoefficient PRZZAStarRectangles PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem signed_nu (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ D H x y A : ℝ, 1 ≤ A →
      ∀ k ∈ Icc 1 ⌊A⌋₊,
        ‖nu (frequencies d D H) x y (k:ℤ)‖ ≤ C*A^eta ∧
        ‖nu (frequencies d D H) x y (-(k:ℤ))‖ ≤ C*A^eta := by
  obtain ⟨C,hC,h⟩ := PRZZNuBounds.nu_subpower eta heta
  refine ⟨C,hC,?_⟩
  intro d D H x y A hA k hk
  have hk0 : (k:ℤ) ≠ 0 := by exact_mod_cast (show 0 < k from (mem_Icc.mp hk).1).ne'
  have hkA : (k:ℝ) ≤ A := (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans (Nat.floor_le (by linarith))
  have hu := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg k) hkA heta.le) hC.le
  constructor
  · have hp := h (frequencies d D H) (frequency_positive_h d D H) x y k hk0
    simp only [Int.natAbs_natCast] at hp
    exact hp.trans hu
  · have hp := h (frequencies d D H) (frequency_positive_h d D H) x y (-(k:ℤ)) (neg_ne_zero.mpr hk0)
    simp only [Int.natAbs_neg,Int.natAbs_natCast] at hp
    exact hp.trans hu

theorem inverse_shift (T S x : ℝ) (beta : ℂ) (hT : 1 < T) (hS : 0 ≤ S)
    (hx : x ∈ Set.Icc 1 T) (hb : |beta.re| ≤ S/Real.log T) :
    ‖((x:ℂ)^beta)⁻¹‖ ≤ Real.exp S := by
  have h := (PRZZSourceEnvelope.power_log T S x (-beta) hT hS hx
    (by simp only [Complex.neg_re]; linarith [(abs_le.mp hb).1])).1
  simpa only [Complex.cpow_neg] using h

/-- This is the original secondCoeff, not an arbitrary sequence carrying
an assumed envelope. The fixed smooth cutoffs supply their own sup norms. -/
theorem second_coefficient (js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d l : ℕ, 1 ≤ N → 1 ≤ d →
      ∀ T x t : ℝ, 1 < T → (N:ℝ) ≤ T → ∀ beta : ℂ,
      |beta.re| ≤ S/Real.log T → ∀ n : ℕ,
      ‖secondCoeff N d l (fun m => (PRZZGCoefficient.coefficient js m:ℂ))
        F2 FM beta x t n‖ ≤ C*T^eta := by
  obtain ⟨C0,h0⟩ := hcF.exists_bound_of_continuous hF
  obtain ⟨C1,h1⟩ := hcM.exists_bound_of_continuous hM
  have hC0 : 0 ≤ C0 := (norm_nonneg _).trans (h0 0)
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  obtain ⟨D,hD,hd⟩ := PRZZGAbsorption.log_pow_bound (PRZZGCoefficient.degree js) eta heta
  refine ⟨D*C0*C1*Real.exp S+1,by positivity,?_⟩
  intro N d l hN hd0 T x t hT hNT beta hb n
  unfold secondCoeff
  split_ifs with hn
  · have hnN := (PRZZDyadic.mem_cell N l n).mp hn.1
    have hn1 := (mem_Icc.mp hnN.1).1
    have hnT : (n:ℝ) ≤ T := (by exact_mod_cast (mem_Icc.mp hnN.1).2 : (n:ℝ) ≤ N).trans hNT
    have hc := PRZZGCoefficient.coefficient_bound js N hN (d*n) (by nlinarith) hn.2
    have hl : (Real.log N)^PRZZGCoefficient.degree js ≤ (Real.log T)^PRZZGCoefficient.degree js :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hN))
        (Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNT) _
    have ha : ‖star (PRZZGCoefficient.coefficient js (d*n):ℂ)‖ ≤ D*T^eta := by
      simpa only [norm_star,Complex.norm_real,Real.norm_eq_abs] using hc.trans (hl.trans (hd T hT.le))
    rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul,norm_mul,
      twist_norm _ _ (by exact_mod_cast (show 0 < n by omega)),mul_one]
    have hp := inverse_shift T S n beta hT hS ⟨by exact_mod_cast hn1,hnT⟩ hb
    calc
      _ ≤ (D*T^eta)*C0*C1*Real.exp S := by gcongr <;> first | exact ha | exact h0 _ | exact h1 _ | exact hp
      _ ≤ _ := by
        have ht : 0 ≤ T^eta := Real.rpow_nonneg (by linarith) _
        nlinarith
  · simp only [norm_zero]
    positivity

/-- Substitute the literal r and both literal nu signs into the sharp
seven-term bound. The equality identifying a source branch with this
block is separate; this theorem does not assume that equality. -/
theorem source_branch_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (js : List ℕ) (eps eta S : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ C D Cnu Cr : ℝ, 0 < C ∧ 0 < D ∧ 0 < Cnu ∧ 0 < Cr ∧
      ∀ y b, b ∈ PRZZHBBranches.branches y K js →
      ∀ left right : List (ArithmeticFunction ℝ × Set ℕ),
      (left.map Prod.fst).Sublist b.2 → (right.map Prod.fst).Sublist b.2 →
      ∀ sl sr : Set ℕ, ∀ wl wr : ℕ → ℂ, (∀ n, ‖wl n‖ ≤ 1) → (∀ n, ‖wr n‖ ≤ 1) →
      ∀ N d l : ℕ, 1 ≤ N → 1 ≤ d → ∀ T x z t D0 H0 A E F V : ℝ,
      1 < T → (N:ℝ) ≤ T → 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ beta : ℂ, |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h →
      let r := secondCoeff N d l (fun m => (PRZZGCoefficient.coefficient js m:ℂ)) F2 FM beta x t
      let np := fun k : ℕ => nu (frequencies d D0 H0) x z (k:ℤ)
      let nm := fun k : ℕ => nu (frequencies d D0 H0) x z (-(k:ℤ))
      let alpha := PRZZBranchEnvelope.coefficient left sl wl
      let beta' := PRZZBranchEnvelope.coefficient right sr wr
      ‖PRZZSharpDI.sharpNegativeBlock N V F A E h r beta' np alpha+
        PRZZSharpDI.sharpBlock N V F A E h r beta' nm alpha‖ ≤
      2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*((Cr*T^eta)*(C*F^eta)*((Cnu*A^eta)*(C*E^eta))*D*
        ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V))) := by
  obtain ⟨C,D,hC,hD,hd⟩ := PRZZBranchSeven.signed_branch_seven hDI K js eps eta heps heta
  obtain ⟨Cnu,hCnu,hn⟩ := signed_nu eta heta
  obtain ⟨Cr,hCr,hr⟩ := second_coefficient js eta S heta hS F2 FM hF hcF hM hcM
  refine ⟨C,D,Cnu,Cr,hC,hD,hCnu,hCr,?_⟩
  intro y b hb left right hl hr' sl sr wl wr hwl hwr N d l hN hd0 T x z t D0 H0 A E F V
    hT hNT hA hE hF hV beta hbeta h hh
  dsimp only
  apply hd y b hb left right hl hr' sl sr wl wr hwl hwr N A E F V hA hE hF hV h hh
    (Cr*T^eta) (Cnu*A^eta) (by positivity) (by positivity)
  · intro n _
    exact hr N d l hN hd0 T x t hT hNT beta hbeta n
  · intro k hk
    exact (hn d D0 H0 x z A hA k hk).1
  · intro k hk
    exact (hn d D0 H0 x z A hA k hk).2

#print axioms source_branch_seven
#print axioms signed_nu
#print axioms inverse_shift
#print axioms second_coefficient
end XiPrime8845.PRZZSourceCoefficients
