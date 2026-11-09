import PRZZActualSmall
import PRZZProfileMellin

/-! Class-uniform suppliers for literal HB small sources and sharp DI branches.
The common sup caps precede all cutoff functions, height and HB data.
Original masks, signed nu, coprimality and sharp DI cutoffs are preserved.
This does not yet supply the free Type I case or full moment aggregation. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex
namespace XiPrime8845.PRZZClassSources
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
open PRZZAStarRectangles PRZZMellinSeparation PRZZSourceCoefficients
set_option maxHeartbeats 6000000

theorem second_coefficient (js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S)
    (C0 C1 : ℝ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F2 FM : ℝ → ℂ,
      (∀ x, ‖F2 x‖ ≤ C0) → (∀ x, ‖FM x‖ ≤ C1) → ∀ N d l : ℕ, 1 ≤ N → 1 ≤ d →
      ∀ T x t : ℝ, 1 < T → (N:ℝ) ≤ T → ∀ beta : ℂ,
      |beta.re| ≤ S/Real.log T → ∀ n : ℕ,
      ‖secondCoeff N d l (fun m => (PRZZGCoefficient.coefficient js m:ℂ))
        F2 FM beta x t n‖ ≤ C*T^eta := by
  obtain ⟨D,hD,hd⟩ := PRZZGAbsorption.log_pow_bound (PRZZGCoefficient.degree js) eta heta
  refine ⟨D*C0*C1*Real.exp S+1,by positivity,?_⟩
  intro F2 FM h0 h1 N d l hN hd0 T x t hT hNT beta hb n
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

theorem small_cell
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S)
    (C0 C2 CM : ℝ) (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hCM : 0 ≤ CM) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      (∀ x, ‖F0 x‖ ≤ C0) → (∀ x, ‖F2 x‖ ≤ C2) → (∀ x, ‖FM x‖ ≤ CM) →
      ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x t : ℝ, ∀ alpha beta : ℂ, ∀ v : ℤ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*T^eta*((2:ℝ)^(l+1)) := by
  obtain ⟨Cr,hCr,hr⟩ := second_coefficient js eta S heta hS C2 CM hC2 hCM
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  let L : ℝ := 2*(2^((ks.length+1)*(2*K)):ℝ)^2
  have hL : 1 ≤ L := by
    have : (1:ℝ) ≤ 2^((ks.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
    dsimp [L]; nlinarith
  refine ⟨Cg*L^eta*L*(C0*Real.exp S)*Cr+1,by positivity,?_⟩
  intro F0 F2 FM h0 h2 hM N y d j l h b hb k U T Q x t alpha beta v hp hs hN hd hT hNT ha hbeta
  have hsup := PRZZCellMass.small_support y K ks b hb k U hp hs
  let z := fun n => if d.Coprime n ∧ d*(h*n) ≤ N then
    PRZZSupportedBranches.row N d j l (fun _ => 1)
      (fun a => (PRZZGCoefficient.coefficient js a:ℂ))
      (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t v (h*n) else 0
  have hz : ∀ n ∈ Icc 1 N, ‖z n‖ ≤ ((2:ℝ)^(l+1))*(C0*Real.exp S)*(Cr*T^eta) := by
    intro n hn
    dsimp [z]
    split_ifs with hcut
    · apply PRZZActualSmall.row_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) _
        (hr F2 FM h2 hM N d l hN hd T x t hT hNT beta hbeta)
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


theorem small_source
    (K : ℕ) (ks js : List ℕ) (eta S : ℝ) (heta : 0 < eta) (hS : 0 ≤ S)
    (C0 C2 CM : ℝ) (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hCM : 0 ≤ CM) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      (∀ x, ‖F0 x‖ ≤ C0) → (∀ x, ‖F2 x‖ ≤ C2) → (∀ x, ‖FM x‖ ≤ CM) →
      ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
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
  obtain ⟨Cc,hCc,hcell⟩ := small_cell K ks js eta S heta hS C0 C2 CM hC0 hC2 hCM
  obtain ⟨Cn,hCn,hnu⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨2*Cn*Cc,by positivity,?_⟩
  intro F0 F2 FM h0 h2 hM N y d j l h b hb k U T Q x y0 t D H A alpha beta hp hs hN hd hT hNT hA ha hbeta
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
          (hcell F0 F2 FM h0 h2 hM N y d j l h b hb k U T Q x t alpha beta (sgn a) hp hs hN hd hT hNT ha hbeta)
          (norm_nonneg _) (by positivity)
      _ = (⌊A⌋₊:ℝ)*((Cn*A^eta)*(Cc*T^eta*((2:ℝ)^(l+1)))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
  have hp' := hsum (fun a => (a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).1)
  have hm' := hsum (fun a => -(a:ℤ)) (fun a ha => (hnu d D H x y0 A hA a ha).2)
  change ‖(∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (a:ℤ)) +
    (∑ a ∈ Icc 1 ⌊A⌋₊, _ * PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta (-(a:ℤ)))‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hp' hm').trans_eq (by ring))


theorem source_branch_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (js : List ℕ) (eps eta S : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (C2 CM : ℝ) (hC2 : 0 ≤ C2) (hCM : 0 ≤ CM) :
    ∃ C D Cnu Cr : ℝ, 0 < C ∧ 0 < D ∧ 0 < Cnu ∧ 0 < Cr ∧
      ∀ F2 FM : ℝ → ℂ, (∀ x, ‖F2 x‖ ≤ C2) → (∀ x, ‖FM x‖ ≤ CM) →
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
  obtain ⟨Cr,hCr,hr⟩ := second_coefficient js eta S heta hS C2 CM hC2 hCM
  refine ⟨C,D,Cnu,Cr,hC,hD,hCnu,hCr,?_⟩
  intro F2 FM h2 hM y b hb left right hl hr' sl sr wl wr hwl hwr N d l hN hd0 T x z t D0 H0 A E F V
    hT hNT hA hE hF hV beta hbeta h hh
  dsimp only
  apply hd y b hb left right hl hr' sl sr wl wr hwl hwr N A E F V hA hE hF hV h hh
    (Cr*T^eta) (Cnu*A^eta) (by positivity) (by positivity)
  · intro n _
    exact hr F2 FM h2 hM N d l hN hd0 T x t hT hNT beta hbeta n
  · intro k hk
    exact (hn d D0 H0 x z A hA k hk).1
  · intro k hk
    exact (hn d D0 H0 x z A hA k hk).2


theorem member_sup (width : ℝ) (jets : ℕ → ℝ) (f : ℝ → ℂ)
    (hf : PRZZProfileMellin.Member width jets f) (x : ℝ) : ‖f x‖ ≤ jets 0 := by
  simpa using hf.jet_bound 0 x

/-- All three cutoffs may vary in the quantitative class after C is fixed. -/
theorem small_source_class (K : ℕ) (ks js : List ℕ) (eta S width : ℝ)
    (heta : 0 < eta) (hS : 0 ≤ S) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      PRZZProfileMellin.Member width jets FM →
      ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x y0 t D H A : ℝ, ∀ alpha beta : ℂ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*T^eta*A^eta*A*((2:ℝ)^(l+1)) := by
  obtain ⟨C,hC,h⟩ := small_source K ks js eta S heta hS (jets 0) (jets 0) (jets 0)
    (hj 0) (hj 0) (hj 0)
  refine ⟨C,hC,?_⟩
  intro F0 F2 FM h0 h2 hm
  exact h F0 F2 FM (member_sup width jets F0 h0) (member_sup width jets F2 h2)
    (member_sup width jets FM hm)

#print axioms second_coefficient
#print axioms small_cell
#print axioms small_source
#print axioms source_branch_seven
#print axioms member_sup
#print axioms small_source_class
end XiPrime8845.PRZZClassSources
