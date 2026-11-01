import PRZZActualSupportBoxes
import PRZZActualBranchDI
import PRZZSourceCoefficients

/-! The source second coefficient and both frequency coefficients supply
the arithmetic envelopes for the actual HB group boxes. DI is explicit.
Identification of this weighted matrix with every original residual branch,
and the Type I alternative, are not asserted by this estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSourceGroupDI
open PRZZActualBranchDI PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 2000000

theorem source_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
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
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient js eta S heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cp,hCp,hp⟩ := PRZZSourceCoefficients.signed_nu eta heta
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro N d y l b hN hd hb k s T D H x y0 t V A hT hNT hV hA beta hbeta h hh w
  dsimp only
  apply hg N y b hb k s {n | d.Coprime n} {n | d.Coprime n}
    (fun _ => 1) (fun _ => 1) (by intro n; simp) (by intro n; simp)
    V (upper N b k (univ \ s)) A (upper N b k s) hV
    (by exact_mod_cast (bounds N hN b k (univ \ s)).1) hA
    (by exact_mod_cast (bounds N hN b k s).1) h hh (Cr*T^eta) (Cp*A^eta)
    (by positivity) (by positivity)
  · intro n hn
    exact hr N d l hN hd T x t hT hNT beta hbeta n
  · intro a ha
    exact (hp d D H x y0 A hA a ha).1
  · intro a ha
    exact (hp d D H x y0 A hA a ha).2

#print axioms source_seven
end XiPrime8845.PRZZSourceGroupDI
