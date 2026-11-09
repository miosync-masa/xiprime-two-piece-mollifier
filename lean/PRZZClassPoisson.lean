import PRZZClassLiteral
import PRZZMixedPoisson
import PRZZCentralArithmeticJoin

/-! A genuine Weil/DI estimate of the actual mixed positive Poisson cell.
The native beta/alpha swap and the original source-scale conditions are
retained. This does not bound negative modes or the complete collective
field, and does not assume a full mixed moment estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZClassPoisson
open PRZZCoefficientPolarization PRZZMellinSeparation
set_option maxHeartbeats 8000000

theorem member_mono (width width' : ℝ) (jets jets' : ℕ → ℝ)
    (hw : width ≤ width') (hj : ∀ n, jets n ≤ jets' n)
    (F : ℝ → ℂ) (hf : PRZZProfileMellin.Member width jets F) :
    PRZZProfileMellin.Member width' jets' F := by
  refine ⟨hf.smooth,?_,fun n x => (hf.jet_bound n x).trans (hj n)⟩
  obtain ⟨a,b,ha,hab,hs,hwidth⟩ := hf.supported
  exact ⟨a,b,ha,hab,hs,hwidth.trans hw⟩

/-- One actual spatial-profile jet sequence works before every scale M.
It may be enlarged with member_mono to the common arithmetic envelope. -/
theorem spatial_members (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ ∀ M : ℝ, 0 < M →
      PRZZProfileMellin.Member (Real.log 6) jets (scaledCutoff F M) := by
  have hc : HasCompactSupport F := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hh
    exact hx (hs hh)
  choose jets hj h using fun n => PRZZCutoffJets.scaled_uniform F hf hc n
  refine ⟨jets,hj,?_⟩
  intro M hM
  refine ⟨hf.comp (contDiff_const.mul contDiff_id),?_,fun n x => h n M x⟩
  refine ⟨M/2,3*M,by positivity,by linarith,?_,?_⟩
  · intro y hy
    have hh := hs hy
    have he : M*(M⁻¹*y)=y := by field_simp
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hM.le,
      mul_le_mul_of_nonneg_left hh.2 hM.le]
  · have he : 3*M/(M/2) = 6 := by field_simp; ring
    rw [he]

theorem partition_members (P : ℝ → ℂ) (hp : ContDiff ℝ ∞ P)
    (hlo : ∀ x ≤ (1/2:ℝ), P x = 1) (hhi : ∀ x, 1 ≤ x → P x = 0) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ ∀ M : ℝ, 0 < M →
      PRZZProfileMellin.Member (Real.log 6) jets
        (scaledCutoff (PRZZWRowLimit.profile P) M) := by
  have hh := PRZZWRowLimit.profile_regular P hp hlo hhi
  exact spatial_members _ hh.1 hh.2.2

theorem literal_square (N d : ℕ) (D H T : ℝ) (c : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (a b : ℂ) :
    PRZZAStar.literal N d D H T c F1 F2 FM W Phi a b =
      PRZZMixedLiteral.literal N d D H T c c F1 F2 FM W Phi a b := by
  unfold PRZZAStar.literal PRZZMixedLiteral.literal
  apply Finset.sum_congr rfl
  intro z hz
  simp only [PRZZAStar.prefactor,star_one,one_mul]
  ring

theorem literal_lift (N d : ℕ) (D H T : ℝ) (c e : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (a b : ℂ) :
    PRZZMixedPoisson.lift (fun f => PRZZAStar.literal N d D H T f F1 F2 FM W Phi a b) c e =
      PRZZMixedLiteral.literal N d D H T c e F1 F2 FM W Phi a b := by
  unfold PRZZMixedPoisson.lift
  simp_rw [literal_square]
  unfold PRZZMixedLiteral.literal
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [combine,star_add,star_mul,star_neg,star_one,Complex.star_def,conj_I]
  ring_nf
  simp only [I_sq]
  ring

def positiveCell (N d J : ℕ) (D T M : ℝ) (c e : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (a b : ℂ) : ℂ :=
  PRZZMixedPoisson.lift (fun f =>
    PRZZCentralArithmeticJoin.positiveCell N d J D T M f F G H Phi a b) c e

/-- The mixed cell is exactly the original positive literal integral,
not merely a supplied norm bound or an unidentified arithmetic proxy. -/
theorem positive_eq (N d J : ℕ) (D T M : ℝ) (c e : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (a b : ℂ) :
    positiveCell N d J D T M c e F G H Phi a b =
      PRZZMixedLiteral.literal N d D ((J:ℝ)+1) T c e G H (scaledCutoff F M)
        (PRZZDyadicEnvelope.sourceW (a+b)) Phi b a := by
  unfold positiveCell PRZZCentralArithmeticJoin.positiveCell
  exact literal_lift N d D ((J:ℝ)+1) T c e G H (scaledCutoff F M) _ Phi b a

theorem positive_absorbed
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta b rho delta gamma S Z L Souter r : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hrho : 0 ≤ rho)
    (hgamma : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hSo : 0 ≤ Souter) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F0 F2 F : ℝ → ℂ) (N d J : ℕ)
      (T Q D M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      PRZZProfileMellin.Member width jets (scaledCutoff F M) →
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) ≤ T^rho →
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) →
      1 ≤ lam → 0 < M → 0 ≤ Q1 → 0 ≤ Q2 →
      Function.support (scaledCutoff F0 Q) ⊆ Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Icc Q2 (2*Q2) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖B/(Real.log T:ℂ)‖ ≤ Z →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ Finset.range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d J D T M (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F (scaledCutoff F0 Q) F2 Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := PRZZClassLiteral.literal_uniform_mass hWeil hDI K hK js ks
    eps eta b rho delta gamma S Z L Souter r heps heta hb hrho hgamma hS hZ hL hSo hr
    hmargin width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨C,hC,?_⟩
  intro F0 F2 F N d J T Q D M lam Q1 Q2 A B Phi hf0 hf2 hfM
    hN hd hT hNT hdT hlog hfreq hfreqT hfreqS hlam hM hQ1 hQ2 hF1 hF2 hsF
    hb' hz ha hsep hshift hscale hPhi hsPhi
  have hsM : Function.support (scaledCutoff F M) ⊆ Icc (M/2) (3*M) := by
    intro y hy
    have hh := hsF hy
    have he : M*(M⁻¹*y)=y := by field_simp
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hM.le,
      mul_le_mul_of_nonneg_left hh.2 hM.le]
  rw [positive_eq]
  have hh := h F0 F2 (scaledCutoff F M) hf0 hf2 hfM N d T Q D ((J:ℝ)+1) M lam Q1 Q2
    B A Phi hN hd hT hNT hdT hlog hfreq hfreqT hfreqS hlam hM hQ1 hQ2 hF1 hF2 hsM
    hb' hz ha (by simpa only [add_comm] using hsep) (by simpa only [add_comm] using hshift)
    hscale hPhi hsPhi
  simpa only [add_comm,add_div] using hh

/-- The positive-cell exponent can be any prescribed tau>0; the loss
parameters are selected internally, before all cutoff and height data. -/
theorem positive_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (rho tau S Z L Souter r : ℝ)
    (hrho : 0 ≤ rho) (htau : 0 < tau) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hSo : 0 ≤ Souter) (hr : 0 < r)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F0 F2 F : ℝ → ℂ) (N d J : ℕ)
      (T Q D M lam Q1 Q2 : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      PRZZProfileMellin.Member width jets (scaledCutoff F M) →
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) ≤ T^rho →
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) →
      1 ≤ lam → 0 < M → 0 ≤ Q1 → 0 ≤ Q2 →
      Function.support (scaledCutoff F0 Q) ⊆ Icc Q1 (2*Q1) →
      Function.support F2 ⊆ Icc Q2 (2*Q2) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖B/(Real.log T:ℂ)‖ ≤ Z →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ Finset.range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d J D T M (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F (scaledCutoff F0 Q) F2 Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^tau*lam*PRZZOptimalPowers.target N T/d := by
  let e := tau/(16*(rho+10))
  have he : 0 < e := by dsimp [e]; positivity
  have hm : (6+rho)*e+(3+rho)*e+e < tau/2 := by
    have heq : e*(16*(rho+10)) = tau := by
      dsimp [e]; field_simp
    nlinarith [mul_nonneg he.le hrho]
  obtain ⟨C,hC,h⟩ := positive_absorbed hWeil hDI K hK js ks
    e e e rho (tau/2) (tau/2) S Z L Souter r he he he hrho (by linarith)
    hS hZ hL hSo hr hm width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨C,hC,?_⟩
  have hadd : tau/2+tau/2 = tau := by ring
  simpa only [hadd] using h

#print axioms positive_target
#print axioms literal_square
#print axioms member_mono
#print axioms spatial_members
#print axioms partition_members
#print axioms literal_lift
#print axioms positive_eq
#print axioms positive_absorbed
end XiPrime8845.PRZZClassPoisson
