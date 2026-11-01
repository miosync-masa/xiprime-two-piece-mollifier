import PRZZActualTypeI

/-! Absolute small-cell bounds with the literal coefficients and masks.
No Weil or DI hypothesis is needed for this case. The modulus cost is
the actual dyadic box length, not the global cutoff N. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZActualSmall
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

theorem row_bound (N d j l n : ℕ) (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x t : ℝ) (v : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : n ∈ PRZZDyadic.cell N j →
      ‖F1 (d*n)/(n:ℂ)^alpha*PRZZMellinSeparation.twist n t‖ ≤ B)
    (hr : ∀ q, ‖PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t q‖ ≤ R) :
    ‖PRZZSupportedBranches.row N d j l (fun _ => 1) right F1 F2 FM alpha beta x t v n‖ ≤
      ((2:ℝ)^(l+1))*B*R := by
  unfold PRZZSupportedBranches.row
  split_ifs with hn
  · apply (norm_sum_le _ _).trans
    have hterm : ∀ q ∈ PRZZDyadic.cell N l,
        ‖(if n.Coprime q ∧ d*q ≤ N then
          (1*F1 (d*n)/(n:ℂ)^alpha*PRZZMellinSeparation.twist n t)*
          (star (right (d*q))*F2 (d*q)*FM (x*q)/(q:ℂ)^beta*PRZZMellinSeparation.twist q t)*
          PRZZKloostermanInputs.e (-(v:ℝ)*PRZZKloostermanInputs.inverseResidue q n/q)
          else 0 : ℂ)‖ ≤ B*R := by
      intro q hq
      split_ifs with hh
      · have h := hr q
        rw [PRZZAStarRectangles.secondCoeff,if_pos ⟨hq,hh.2⟩] at h
        have he : ∀ r : ℝ, ‖PRZZKloostermanInputs.e r‖ = 1 := by
          intro r; simp [PRZZKloostermanInputs.e,Complex.norm_exp]
        simp only [one_mul,norm_mul,he,mul_one]
        exact mul_le_mul (by simpa only [norm_mul] using hf hn)
          (by simpa only [norm_mul] using h) (by positivity) hB
      · simp only [norm_zero]; positivity
    have hcard : (PRZZDyadic.cell N l).card ≤ 2^(l+1) := by
      have hs : PRZZDyadic.cell N l ⊆ Icc 1 (2^(l+1)) := by
        intro q hq
        have h := (PRZZDyadic.mem_cell N l q).mp hq
        exact mem_Icc.mpr ⟨(mem_Icc.mp h.1).1,h.2.2.le⟩
      simpa using card_le_card hs
    calc
      _ ≤ ∑ q ∈ PRZZDyadic.cell N l, B*R := sum_le_sum hterm
      _ = ((PRZZDyadic.cell N l).card:ℝ)*(B*R) := by simp
      _ ≤ ((2:ℝ)^(l+1))*(B*R) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) (mul_nonneg hB hR)
      _ = _ := by ring
  · simp only [norm_zero]; positivity

theorem small_cell (F0 F2 FM : ℝ → ℂ)
    (hf : Continuous F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x t : ℝ, ∀ alpha beta : ℂ, ∀ v : ℤ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*T^eta*((2:ℝ)^(l+1)) := by
  obtain ⟨C0,h0⟩ := hc.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C0 := (norm_nonneg _).trans (h0 0)
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient js eta S heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  let L : ℝ := 2*(2^((ks.length+1)*(2*K)):ℝ)^2
  have hL : 1 ≤ L := by
    have : (1:ℝ) ≤ 2^((ks.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
    dsimp [L]; nlinarith
  refine ⟨Cg*L^eta*L*(C0*Real.exp S)*Cr+1,by positivity,?_⟩
  intro N y d j l h b hb k U T Q x t alpha beta v hp hs hN hd hT hNT ha hbeta
  have hsup := PRZZCellMass.small_support y K ks b hb k U hp hs
  let z := fun n => if d.Coprime n ∧ d*(h*n) ≤ N then
    PRZZSupportedBranches.row N d j l (fun _ => 1)
      (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
      (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t v (h*n) else 0
  have hz : ∀ n ∈ Icc 1 N, ‖z n‖ ≤ ((2:ℝ)^(l+1))*(C0*Real.exp S)*(Cr*T^eta) := by
    intro n hn
    dsimp [z]
    split_ifs with hcut
    · apply row_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) _
        (hr N d l hN hd T x t hT hNT beta hbeta)
      intro hm
      have hmem := (PRZZDyadic.mem_cell N j (h*n)).mp hm
      have hpos : 0 < h*n := (mem_Icc.mp hmem.1).1
      have hi := PRZZSourceCoefficients.inverse_shift T S (h*n) alpha hT hS
        ⟨by exact_mod_cast hpos,(by exact_mod_cast (mem_Icc.mp hmem.1).2 : (h*n:ℝ) ≤ N).trans hNT⟩ ha
      rw [div_eq_mul_inv,norm_mul,norm_mul,PRZZMellinSeparation.twist_norm _ _ (by exact_mod_cast hpos),mul_one]
      exact mul_le_mul (h0 _) (by simpa using hi) (norm_nonneg _) hC0
    · simp only [norm_zero]; positivity
  have he : PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v =
      ∑ n ∈ Icc 1 N, (group N b k univ n:ℂ)*z n := by
    unfold PRZZFreeCell.cell; apply sum_congr rfl; intro n hn
    dsimp [z]; split_ifs <;> simp
  rw [he]
  exact (hg N y b hb k univ L _ hL (by positivity) hsup z hz).trans (by
    have ht : 0 ≤ T^eta := Real.rpow_nonneg (by linarith) _
    dsimp [L] at *
    nlinarith [mul_nonneg ht (show 0 ≤ (2:ℝ)^(l+1) by positivity)])

#print axioms row_bound
#print axioms small_cell

/-- Both literal nu signs are supplied, uniformly in all physical and
Mellin coordinates. Smallness is the actual product of dyadic scales. -/
theorem small_source (F0 F2 FM : ℝ → ℂ)
    (hf : Continuous F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x y0 t D H A : ℝ, ∀ alpha beta : ℂ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*T^eta*A^eta*A*((2:ℝ)^(l+1)) := by
  obtain ⟨Cc,hCc,hcell⟩ := small_cell F0 F2 FM hf hc hF hcF hM hcM K ks js eta S heta hS
  obtain ⟨Cn,hCn,hnu⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨2*Cn*Cc,by positivity,?_⟩
  intro N y d j l h b hb k U T Q x y0 t D H A alpha beta hp hs hN hd hT hNT hA ha hbeta
  have hsum (sgn : ℕ → ℤ) (hh : ∀ a ∈ Icc 1 ⌊A⌋₊,
      ‖nu (frequencies d D H) x y0 (sgn a)‖ ≤ Cn*A^eta) :
      ‖∑ a ∈ Icc 1 ⌊A⌋₊, nu (frequencies d D H) x y0 (sgn a)*
        PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (sgn a)‖ ≤
        A*((Cn*A^eta)*(Cc*T^eta*((2:ℝ)^(l+1)))) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ a ∈ Icc 1 ⌊A⌋₊, (Cn*A^eta)*(Cc*T^eta*((2:ℝ)^(l+1))) := by
        apply sum_le_sum; intro a ha'
        rw [norm_mul]
        exact mul_le_mul (hh a ha')
          (hcell N y d j l h b hb k U T Q x t alpha beta (sgn a) hp hs hN hd hT hNT ha hbeta)
          (norm_nonneg _) (by positivity)
      _ = (⌊A⌋₊:ℝ)*((Cn*A^eta)*(Cc*T^eta*((2:ℝ)^(l+1)))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
  have hp' := hsum (fun a => (a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).1)
  have hm' := hsum (fun a => -(a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).2)
  change ‖(∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (a:ℤ)) +
    (∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (-(a:ℤ)))‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hp' hm').trans_eq (by ring))

#print axioms small_source
end XiPrime8845.PRZZActualSmall
