import PRZZUniformTypeI

/-! Uniform small and DI suppliers for the two actual scaled cutoff
families. No scale-indexed choice of arithmetic constants is needed. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZUniformCases
set_option maxHeartbeats 6000000

section
open PRZZActualSmall
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
theorem small_cell (F0 F2 FM : ℝ → ℂ)
    (hf : Continuous F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x t : ℝ, ∀ alpha beta : ℂ, ∀ v : ℤ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZFreeCell.cell N d j l h b k js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta v‖ ≤
        C*T^eta*((2:ℝ)^(l+1)) := by
  obtain ⟨C0,h0⟩ := hc.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C0 := (norm_nonneg _).trans (h0 0)
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient_scaled js eta S heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  let L : ℝ := 2*(2^((ks.length+1)*(2*K)):ℝ)^2
  have hL : 1 ≤ L := by
    have : (1:ℝ) ≤ 2^((ks.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
    dsimp [L]; nlinarith
  refine ⟨Cg*L^eta*L*(C0*Real.exp S)*Cr+1,by positivity,?_⟩
  intro Q2 QM N y d j l h b hb k U T Q x t alpha beta v hp hs hN hd hT hNT ha hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
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
        (hr Q2 QM N d l hN hd T x t hT hNT beta hbeta)
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

end

#print axioms small_cell

section
open PRZZActualSmall
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
theorem small_source (F0 F2 FM : ℝ → ℂ)
    (hf : Continuous F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x y0 t D H A : ℝ, ∀ alpha beta : ℂ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*T^eta*A^eta*A*((2:ℝ)^(l+1)) := by
  obtain ⟨Cc,hCc,hcell⟩ := small_cell F0 F2 FM hf hc hF hcF hM hcM K ks js eta S heta hS
  obtain ⟨Cn,hCn,hnu⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨2*Cn*Cc,by positivity,?_⟩
  intro Q2 QM N y d j l h b hb k U T Q x y0 t D H A alpha beta hp hs hN hd hT hNT hA ha hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
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
          (hcell Q2 QM N y d j l h b hb k U T Q x t alpha beta (sgn a) hp hs hN hd hT hNT ha hbeta)
          (norm_nonneg _) (by positivity)
      _ = (⌊A⌋₊:ℝ)*((Cn*A^eta)*(Cc*T^eta*((2:ℝ)^(l+1)))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
  have hp' := hsum (fun a => (a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).1)
  have hm' := hsum (fun a => -(a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).2)
  change ‖(∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (a:ℤ)) +
    (∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (-(a:ℤ)))‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hp' hm').trans_eq (by ring))

end

#print axioms small_source

section
open PRZZSourceGroupDI
open Finset
open PRZZActualBranchDI PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
theorem group_di (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ Q2 QM : ℝ, ∀ (N d y l : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → b ∈ branches y K ks →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ T D H x y0 t V A : ℝ, 1 < T → (N:ℝ) ≤ T → 1 ≤ V → 1 ≤ A →
      ∀ beta : ℂ, |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h → ∀ w : ℕ → ℂ,
      let E : ℝ := upper N b k s
      let F : ℝ := upper N b k (univ \ s)
      let r := PRZZAStarRectangles.secondCoeff N d l
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) beta x t
      let ap := coefficient N b k s {n | d.Coprime n} (fun _ => 1)
      let bf := coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)
      ‖PRZZWeightedDI.negative N V F A E h r bf
          (fun a => nu (frequencies d D H) x y0 (a:ℤ)) ap w +
        PRZZWeightedDI.weighted N V F A E h r bf
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ))) ap w‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*
          ((Cr*T^eta)*(Cg*F^eta)*((Cp*A^eta)*(Cg*E^eta))*Cd*
            ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V)))*
              PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨Cg,Cd,hCg,hCd,hg⟩ := signed_group_seven hDI K ks eps eta heps heta
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient_scaled js eta S heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cp,hCp,hp⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro Q2 QM N d y l b hN hd hb k s T D H x y0 t V A hT hNT hV hA beta hbeta h hh w
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  dsimp only
  apply hg N y b hb k s {n | d.Coprime n} {n | d.Coprime n}
    (fun _ => 1) (fun _ => 1) (by intro n; simp) (by intro n; simp)
    V (upper N b k (univ \ s)) A (upper N b k s) hV
    (by exact_mod_cast (bounds N hN b k (univ \ s)).1) hA
    (by exact_mod_cast (bounds N hN b k s).1) h hh (Cr*T^eta) (Cp*A^eta)
    (by positivity) (by positivity)
  · intro n hn
    exact hr Q2 QM N d l hN hd T x t hT hNT beta hbeta n
  · intro a ha
    exact (hp d D H x y0 A hA a ha).1
  · intro a ha
    exact (hp d D H x y0 A hA a ha).2

end

#print axioms group_di

section
open PRZZDyadicModulus
open Finset
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches
open PRZZAStarNu PRZZNuCoefficient PRZZSignedSourceCell
theorem dyadic_di (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ Q2 QM : ℝ, ∀ (N d y j l : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → b ∈ branches y K ks →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ T D H x y0 t A : ℝ, 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      ∀ (rightF : ℝ → ℂ) (alpha beta : ℂ), |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h →
      let E : ℝ := upper N b k s
      let F : ℝ := upper N b k (univ \ s)
      let V : ℝ := bound N l
      ‖source N d j l h A b k (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) rightF (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
          (fun a => nu (frequencies d D H) x y0 (a:ℤ))
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*
          ((Cr*T^eta)*(Cg*F^eta)*((Cp*A^eta)*(Cg*E^eta))*Cd*
            ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V)))*
              PRZZTypeI.variation (fun n => PRZZResidualRow.weight N d j h rightF alpha t (n+1)) N := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hbound⟩ :=
    group_di hDI K ks js eps eta S heps heta hS F2 FM hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro Q2 QM N d y j l b hN hd hb k s T D H x y0 t A hT hNT hA rightF alpha beta hbeta h hh
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  dsimp only
  rw [source_eq_dyadic N d j l h A b k s]
  exact hbound Q2 QM N d y l b hN hd hb k s T D H x y0 t (bound N l) A hT hNT
    (by exact_mod_cast bound_pos N l hN) hA beta hbeta h hh _

end

#print axioms dyadic_di

section
open PRZZDyadicCellBound
open Finset
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
open PRZZCommonCellBound (budget)
theorem di_source (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hF0 : ContDiff ℝ ∞ F0) (hc0 : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ Q2 QM : ℝ, ∀ (N d y j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches y K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ s : Finset (Fin b.2.length), ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      budget Cg Cd Cr Cp Cv eps eta N T A t *
        PRZZDISeven.seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) (PRZZDyadicModulus.bound N l) := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hb⟩ := dyadic_di
    hDI K ks js eps eta S heps heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cv,hCv,hv⟩ := PRZZZeroExtension.full_variation F0 hF0 hc0 eta S Z heta hS hZ
  refine ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro Q2 QM N d y j l h b hN hd hh hmem k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  have hv' := hv N d h j T Q t alpha (by omega) (by omega) hT hNT hhT ha hz
  have hv0 : 0 ≤ PRZZTypeI.variation
      (fun n => PRZZResidualRow.weight N d j h (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N := by
    unfold PRZZTypeI.variation; positivity
  have hlog0 : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hb' := hb Q2 QM N d y j l b hN hd hmem k s T D H x y0 t A hT
    (by linarith) hA (PRZZMellinSeparation.scaledCutoff F0 Q) alpha beta hbeta h hh
  dsimp only at hb'
  have he : (upper N b k s:ℝ) ≤ N := by exact_mod_cast (bounds N hN b k s).2
  have hf : (upper N b k (univ \ s):ℝ) ≤ N := by
    exact_mod_cast (bounds N hN b k (univ \ s)).2
  have hmod : (PRZZDyadicModulus.bound N l:ℝ) ≤ N := by
    exact_mod_cast min_le_left N (2^(l+1))
  have hseven : 0 ≤ PRZZDISeven.seven h (upper N b k s) A
      ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) (PRZZDyadicModulus.bound N l) := by
    unfold PRZZDISeven.seven; positivity
  have hlog : Real.log ((upper N b k (univ \ s):ℝ)+1) ≤ Real.log ((N:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  simp only [Nat.floor_natCast] at hb'
  apply hb'.trans
  unfold budget
  calc
    _ ≤ 2*((1+2*Real.log ((N:ℝ)+1))*
      ((Cr*T^eta)*(Cg*(N:ℝ)^eta)*((Cp*A^eta)*(Cg*(N:ℝ)^eta))*Cd*
        (((N:ℝ)*N*A*N)^eps*PRZZDISeven.seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) (PRZZDyadicModulus.bound N l))))*
            (Cv*(1+|t|)*T^eta) := by
      gcongr <;> positivity
    _ = _ := by ring

end

#print axioms di_source

section
open PRZZActualBudgetLayout
open Finset
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches
open PRZZCombinedBudget PRZZDISeven
theorem di_actual (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hF0 : ContDiff ℝ ∞ F0) (hc0 : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ Q2 QM : ℝ, ∀ (N d j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ U : ℝ, (∏ i, (2:ℝ)^(k i)) = U →
      ∀ n : ℕ, n ≤ N → PRZZRowWindow.lo h j ≤ n →
      n ≤ PRZZRowWindow.hi N d h j → group N b k univ n ≠ 0 → ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      let c : ℝ := 2^((ks.length+1)*(2*K))
      let X : ℝ := (2:ℝ)^j/c
      U ≤ 2*c ∨ freeCase b k U ∨
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (a:ℤ))
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,hbound⟩ :=
    di_source hDI K ks js eps eta S Z heps heta hS hZ
      F0 F2 FM hF0 hc0 hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,?_⟩
  intro Q2 QM N d j l h b hN hd hh hb k U hp n hn hl hu hnz T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  dsimp only
  rcases actual_budget_layout N d h j K ks (by omega) (by omega) hK b hb k U hp n hn hl hu hnz
    A (PRZZDyadicModulus.bound N l) (by linarith) (Nat.cast_nonneg _) with hs | hf | ⟨s,hs⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl hf)
  · apply Or.inr ∘ Or.inr
    have hbnd := hbound Q2 QM N d _ j l h b hN hd hh hb k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
    apply hbnd.trans
    have hU : 0 ≤ U := hp ▸ (by positivity)
    have ht : 0 ≤ typeI U A (PRZZDyadicModulus.bound N l) := by unfold typeI; positivity
    have hs' := (le_add_of_nonneg_left ht).trans hs
    apply mul_le_mul_of_nonneg_left hs'
    have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget
    positivity

end

#print axioms di_actual

end XiPrime8845.PRZZUniformCases
