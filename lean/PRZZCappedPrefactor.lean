import PRZZPrefactorMass
import PRZZEmptyArithmeticMass

/-! Common coefficient caps in the actual normalized A-star prefactor.
The dyadic denominators pay their own cardinalities. Dilated coefficients,
complex powers and residue phases remain literal, not proxy masses. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set Finset
namespace XiPrime8845.PRZZCappedPrefactor
open PRZZDyadicArithmeticMass PRZZDyadic PRZZPrefactorMass PRZZEmptyArithmeticMass
set_option maxHeartbeats 6000000

theorem dilated_weighted_pair_mass (a : ℕ → ℂ) (H : ℝ) (hH : 0 ≤ H) (N d j l : ℕ)
    (hN : 1 ≤ N) (hd : 1 ≤ d)
    (hcoef : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ H) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ (cell N j) ×ˢ (cell N l))
    (hlen : ∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N)
    (u : ℕ × ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ p ∈ s, ‖u p‖ ≤ B) :
    (∑ p ∈ s, ‖((a (d*p.1)*star (a (d*p.2)))*u p)/
      ((p.1:ℂ)*(p.2:ℂ))‖) ≤ H^2*B := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hcard : (s.card:ℝ) ≤ (2:ℝ)^j*(2:ℝ)^l := by
    exact_mod_cast (Finset.card_le_card hs).trans
      (by rw [card_product]; exact Nat.mul_le_mul (cell_card N j) (cell_card N l))
  calc
    _ ≤ ∑ _p ∈ s, (H^2*B)/((2:ℝ)^j*(2:ℝ)^l) := by
      apply sum_le_sum
      intro p hp
      have hc := mem_product.mp (hs hp)
      have h1 := (mem_cell N j p.1).mp hc.1
      have h2 := (mem_cell N l p.2).mp hc.2
      have hp1 := (mem_Icc.mp h1.1).1
      have hp2 := (mem_Icc.mp h2.1).1
      have ha := hcoef (d*p.1) (mem_Icc.mpr ⟨Nat.mul_le_mul hd hp1,(hlen p hp).1⟩)
      have hb := hcoef (d*p.2) (mem_Icc.mpr ⟨Nat.mul_le_mul hd hp2,(hlen p hp).2⟩)
      have hn : ‖a (d*p.1)‖ * ‖a (d*p.2)‖ * ‖u p‖ ≤
          H^2*B := by
        have hh := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hH)
          (hu p hp) (norm_nonneg _) (by positivity)
        simpa only [pow_two] using hh
      simp only [norm_div,norm_mul,norm_star,Complex.norm_natCast]
      apply div_le_div₀ (by positivity) hn (by positivity)
      exact mul_le_mul (by exact_mod_cast h1.2.1) (by exact_mod_cast h2.2.1)
        (by positivity) (by positivity)
    _ = (s.card:ℝ)*((H^2*B)/((2:ℝ)^j*(2:ℝ)^l)) := by simp
    _ ≤ ((2:ℝ)^j*(2:ℝ)^l)*((H^2*B)/((2:ℝ)^j*(2:ℝ)^l)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

theorem pair_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (H : ℝ) (N d j l : ℕ) (T Q V S : ℝ)
      (alpha beta : ℂ) (w : ℤ × ℕ),
      0 ≤ H → (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ H) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ p ∈ pairs N d j l,
        ‖PRZZAStar.prefactor a
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta (p,w)/((p.1:ℂ)*(p.2:ℂ))‖) ≤
        C*Real.exp (2*S)*H^2/d := by
  obtain ⟨B,hB,hcut⟩ := PRZZValuedCutoffs.cutoff_pair_uniform F G hF hG hcF hcG
  refine ⟨B+1,by positivity,?_⟩
  intro a H N d j l T Q V S alpha beta w hH hcoef hN hd hNT hL hS ha hb
  let f1 := PRZZMellinSeparation.scaledCutoff F Q
  let f2 := PRZZMellinSeparation.scaledCutoff G V
  let g := fun p : ℕ × ℕ =>
    f1 ((d:ℝ)*p.1)*f2 ((d:ℝ)*p.2)*((d:ℂ)*(p.1:ℂ)^alpha*(p.2:ℂ)^beta)⁻¹*
      PRZZKloostermanInputs.e (-((w.2:ℝ)*(w.1:ℝ))*
        PRZZKloostermanInputs.inverseResidue p.2 p.1/p.2)
  have hg (p : ℕ × ℕ) (hp : p ∈ pairs N d j l) : ‖g p‖ ≤ B*Real.exp (2*S)/d := by
    have hs := inverse_pair N d j l p T S alpha beta hd hNT hL hS hp ha hb
    have hn : ‖PRZZKloostermanInputs.e (-((w.2:ℝ)*(w.1:ℝ))*
        PRZZKloostermanInputs.inverseResidue p.2 p.1/p.2)‖ = 1 := by
      simp [PRZZKloostermanInputs.e,Complex.norm_exp]
    have hc := hcut Q V ((d:ℝ)*p.1) ((d:ℝ)*p.2)
    change ‖f1 ((d:ℝ)*p.1)*f2 ((d:ℝ)*p.2)‖ ≤ B at hc
    dsimp only [g]
    rw [norm_mul,hn,mul_one]
    simp only [norm_mul,norm_inv,Complex.norm_natCast,mul_inv_rev]
    have hd0 : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have h1 := hs.1; have h2 := hs.2
    rw [norm_inv] at h1 h2
    rw [norm_mul] at hc
    have hpow : ‖(p.2:ℂ)^beta‖⁻¹*‖(p.1:ℂ)^alpha‖⁻¹ ≤ Real.exp S*Real.exp S :=
      mul_le_mul h2 h1 (by positivity) (Real.exp_pos S).le
    calc
      _ = (‖f1 ((d:ℝ)*p.1)‖*‖f2 ((d:ℝ)*p.2)‖)*
          (‖(p.2:ℂ)^beta‖⁻¹*‖(p.1:ℂ)^alpha‖⁻¹)*(d:ℝ)⁻¹ := by ring
      _ ≤ (B*(Real.exp S*Real.exp S))*(d:ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc hpow (by positivity) hB) (by positivity)
      _ = _ := by
        have he : Real.exp S*Real.exp S = Real.exp (2*S) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he]
        ring
  have hm := dilated_weighted_pair_mass a H hH N d j l hN hd hcoef
    (pairs N d j l) (by intro p hp; exact (Finset.mem_filter.mp hp).1)
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.2)
    g (B*Real.exp (2*S)/d) (by positivity) hg
  have he : (∑ p ∈ pairs N d j l,
      ‖PRZZAStar.prefactor a f1 f2 d
        alpha beta (p,w)/((p.1:ℂ)*(p.2:ℂ))‖) =
      ∑ p ∈ pairs N d j l,
        ‖((a (d*p.1)*
          star (a (d*p.2)))*g p)/((p.1:ℂ)*(p.2:ℂ))‖ := by
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    unfold PRZZAStar.prefactor g
    push_cast
    ring
  rw [he]
  apply hm.trans
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ = B*Real.exp (2*S)*H^2/d := by ring
    _ ≤ _ := by gcongr; linarith

theorem local_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (Hcap : ℝ) (N d j l : ℕ) (T Q V S D H : ℝ)
      (alpha beta : ℂ),
      0 ≤ Hcap → (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ z ∈ localIndices N d j l D H,
        ‖PRZZAStar.prefactor a
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
        (frequencies d D H).card*(C*Real.exp (2*S)*Hcap^2/d) := by
  obtain ⟨C,hC,hh⟩ := pair_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro a Hcap N d j l T Q V S D H alpha beta hHcap hcoef hN hd hNT hL hS ha hb
  simp only [localIndices,Finset.sum_product]
  rw [Finset.sum_comm]
  exact (Finset.sum_le_sum (fun w hw => hh a Hcap N d j l T Q V S alpha beta w
    hHcap hcoef hN hd hNT hL hS ha hb)).trans_eq (by simp)

theorem coefficient_row (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (Hcap : ℝ) (N d j l : ℕ) (D T Q V S : ℝ)
      (alpha beta : ℂ),
      0 ≤ Hcap → (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ Hcap) → 1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ D → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      rowMass N d j l D a
        (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) alpha beta ≤
      (C*Real.exp (2*S)*Hcap^2)*10*D/(d:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := local_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro a Hcap N d j l D T Q V S alpha beta hHcap hcoef hN hd hNT hL hD hS ha hb
  rw [row_mass_eq]
  have hh := h a Hcap N d j l T Q V S D 2 alpha beta hHcap hcoef hN hd hNT hL hS ha hb
  apply hh.trans
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hp := mul_le_mul_of_nonneg_right (frequency_two_count d D hD)
    (show 0 ≤ C*Real.exp (2*S)*Hcap^2/d by positivity)
  exact hp.trans_eq (by ring)

#print axioms local_mass
#print axioms coefficient_row
#print axioms dilated_weighted_pair_mass
#print axioms pair_mass
end XiPrime8845.PRZZCappedPrefactor
