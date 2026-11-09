import PRZZClassVariation

/-! Original HB signed-source DI estimate with class-uniform constants.
The original dyadic modulus, row cutoff, sharp products and both signs
are retained. The actual row variation is evaluated, not a premise.
The free Type I case and full moment assembly are still separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZClassDI
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches
open PRZZActualBranchDI PRZZAStarNu PRZZNuCoefficient PRZZDyadicModulus PRZZSignedSourceCell
open PRZZCommonCellBound (budget)
set_option maxHeartbeats 8000000

theorem source_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (C2 CM : ℝ) (hC2 : 0 ≤ C2) (hCM : 0 ≤ CM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ F2 FM : ℝ → ℂ, (∀ x, ‖F2 x‖ ≤ C2) → (∀ x, ‖FM x‖ ≤ CM) →
      ∀ (N d y l : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → b ∈ branches y K ks →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ T D H x y0 t V A : ℝ, 1 < T → (N:ℝ) ≤ T → 1 ≤ V → 1 ≤ A →
      ∀ beta : ℂ, |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h → ∀ w : ℕ → ℂ,
      let E : ℝ := upper N b k s
      let F : ℝ := upper N b k (univ \ s)
      let r := PRZZAStarRectangles.secondCoeff N d l
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F2 FM beta x t
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
  obtain ⟨Cr,hCr,hr⟩ := PRZZClassSources.second_coefficient js eta S heta hS C2 CM hC2 hCM
  obtain ⟨Cp,hCp,hp⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro F2 FM h2 hM N d y l b hN hd hb k s T D H x y0 t V A hT hNT hV hA beta hbeta h hh w
  dsimp only
  apply hg N y b hb k s {n | d.Coprime n} {n | d.Coprime n}
    (fun _ => 1) (fun _ => 1) (by intro n; simp) (by intro n; simp)
    V (upper N b k (univ \ s)) A (upper N b k s) hV
    (by exact_mod_cast (bounds N hN b k (univ \ s)).1) hA
    (by exact_mod_cast (bounds N hN b k s).1) h hh (Cr*T^eta) (Cp*A^eta)
    (by positivity) (by positivity)
  · intro n hn
    exact hr F2 FM h2 hM N d l hN hd T x t hT hNT beta hbeta n
  · intro a ha
    exact (hp d D H x y0 A hA a ha).1
  · intro a ha
    exact (hp d D H x y0 A hA a ha).2

theorem source_seven_dyadic (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (C2 CM : ℝ) (hC2 : 0 ≤ C2) (hCM : 0 ≤ CM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ F2 FM : ℝ → ℂ, (∀ x, ‖F2 x‖ ≤ C2) → (∀ x, ‖FM x‖ ≤ CM) →
      ∀ (N d y j l : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → b ∈ branches y K ks →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ T D H x y0 t A : ℝ, 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      ∀ (rightF : ℝ → ℂ) (alpha beta : ℂ), |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h →
      let E : ℝ := upper N b k s
      let F : ℝ := upper N b k (univ \ s)
      let V : ℝ := bound N l
      ‖source N d j l h A b k (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) rightF F2 FM alpha beta x t
          (fun a => nu (frequencies d D H) x y0 (a:ℤ))
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*
          ((Cr*T^eta)*(Cg*F^eta)*((Cp*A^eta)*(Cg*E^eta))*Cd*
            ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V)))*
              PRZZTypeI.variation (fun n => PRZZResidualRow.weight N d j h rightF alpha t (n+1)) N := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hbound⟩ :=
    source_seven hDI K ks js eps eta S heps heta hS C2 CM hC2 hCM
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro F2 FM h2 hM N d y j l b hN hd hb k s T D H x y0 t A hT hNT hA rightF alpha beta hbeta h hh
  dsimp only
  rw [PRZZDyadicModulus.source_eq_dyadic N d j l h A b k s]
  exact hbound F2 FM h2 hM N d y l b hN hd hb k s T D H x y0 t (bound N l) A hT hNT
    (by exact_mod_cast bound_pos N l hN) hA beta hbeta h hh _

theorem source_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ (N d y j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches y K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ s : Finset (Fin b.2.length), ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      budget Cg Cd Cr Cp Cv eps eta N T A t *
        PRZZDISeven.seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) (PRZZDyadicModulus.bound N l) := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hb⟩ := source_seven_dyadic
    hDI K ks js eps eta S heps heta hS (jets 0) (jets 0) (hj 0) (hj 0)
  obtain ⟨Cv,hCv,hv⟩ := PRZZClassVariation.full_variation width jets hj eta S Z heta hS hZ
  refine ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro F0 F2 FM hF0 hF2 hFM N d y j l h b hN hd hh hmem k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  have hv' := hv F0 hF0 N d h j T Q t alpha (by omega) (by omega) hT hNT hhT ha hz
  have hv0 : 0 ≤ PRZZTypeI.variation
      (fun n => PRZZResidualRow.weight N d j h (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N := by
    unfold PRZZTypeI.variation; positivity
  have hlog0 : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hb' := hb F2 FM (PRZZClassSources.member_sup width jets F2 hF2)
    (PRZZClassSources.member_sup width jets FM hFM) N d y j l b hN hd hmem k s T D H x y0 t A hT
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

#print axioms source_seven
#print axioms source_seven_dyadic
#print axioms source_bound
end XiPrime8845.PRZZClassDI
