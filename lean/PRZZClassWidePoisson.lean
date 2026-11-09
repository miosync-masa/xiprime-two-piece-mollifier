import PRZZClassWideLiteral
import PRZZClassPoisson
import PRZZArithmeticWindowCutoff
import PRZZWindowScaleSupply
import PRZZWindowCentralAssembly

/-! Class-uniform mixed estimates for actual width-six positive cells.
The original rounded arithmetic-window cutoff is retained. Raw cutoffs
below one, negative modes and the other collective errors are not dropped. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZClassWidePoisson
open PRZZCoefficientPolarization PRZZMellinSeparation PRZZClassPoisson
set_option maxHeartbeats 8000000

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
      Function.support (scaledCutoff F0 Q) ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T → 1+‖B/(Real.log T:ℂ)‖ ≤ Z →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T → r ≤ ‖A+B‖ →
      |((A+B)/(Real.log T:ℂ)).re| ≤ Souter/Real.log T →
      (∀ l ∈ Finset.range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d J D T M (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F (scaledCutoff F0 Q) F2 Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := PRZZClassWideLiteral.literal_uniform_mass hWeil hDI K hK js ks
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
      Function.support (scaledCutoff F0 Q) ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
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


/-- Actual rounded arithmetic-window cutoffs supply the frequency and
height envelopes. Empty strict index ranges are zero, not assumed active.
The only height loss beyond tau is the displayed eD+eH cutoff cost. -/
theorem window_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eD eH tau S r bM : ℝ)
    (heD : 0 ≤ eD) (heH : 0 ≤ eH) (htau : 0 < tau) (hS : 0 ≤ S)
    (hr : 0 < r) (hbM : 0 ≤ bM)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F0 F2 F : ℝ → ℂ) (N d s : ℕ)
      (T Q V : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s)) →
      0 < N → 0 < d → 72 ≤ T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T →
      1 ≤ Real.log T → S ≤ Real.log T →
      0 < Q → 0 < V → Q ≤ 2*T → V ≤ 2*T → (2:ℝ)^s ≤ T^bM →
      1 ≤ PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH →
      Function.support F0 ⊆ Icc (1/2:ℝ) 3 →
      Function.support F2 ⊆ Icc (V/2) (3*V) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH)
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) T ((2:ℝ)^s)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F (scaledCutoff F0 Q) F2 Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(tau+eD+eH)*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := positive_target hWeil hDI K hK js ks (eD+eH+2) tau S 2 (bM+1) (2*S) r
    (by linarith) htau hS (by norm_num) (by linarith) (by positivity) hr
    width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨18*C,by positivity,?_⟩
  intro F0 F2 F N d s T Q V A B Phi hf0 hf2 hfM hN hd hT hNT hdT hlog hST
    hQ hV hQT hVT hM hraw hs0 hs2 hsF hA hB hsep hPhi hsPhi
  have ht : 0 < T := by linarith
  have hL : 0 < Real.log T := by linarith
  have hshift (Z : ℂ) (hZ : ‖Z‖ ≤ S) : |(Z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    exact div_le_div_of_nonneg_right hZ hL.le
  have hnorm : 1+‖B/(Real.log T:ℂ)‖ ≤ 2 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    have hh : ‖B‖/Real.log T ≤ 1 := (div_le_one hL).mpr (hB.trans hST)
    linarith
  rcases PRZZWindowScaleSupply.empty_or_envelope N d T ((2:ℝ)^s) Q V eD eH hd hT
    (by positivity) hQ.le hV.le hQT hVT hraw with he | ⟨hfreq,hpow,hlocal⟩
  · rw [positive_eq]
    simp only [PRZZMixedLiteral.literal,he,Finset.sum_empty,norm_zero]
    unfold PRZZOptimalPowers.target
    positivity
  · have hscale (l : ℕ) (hl : l ∈ Finset.range (Nat.log 2 N+1)) :
        |Real.log ((2:ℝ)^s)|+|Real.log ((2:ℝ)^l)| ≤ (bM+1)*Real.log T := by
      have hl' : l ≤ Nat.log 2 N := by have := Finset.mem_range.mp hl; omega
      have hn : (2:ℝ)^l ≤ N := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hl').trans
          (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
      exact PRZZWindowScaleSupply.row_log_scale N s l T bM (by linarith) hM hn (by linarith)
    have hlam : 1 ≤ 18*T^(eD+eH) := by
      have hh := Real.one_le_rpow (show 1 ≤ T by linarith) (add_nonneg heD heH)
      linarith
    have hh := h F0 F2 F N d (PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH)
      T Q (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) ((2:ℝ)^s)
      (18*T^(eD+eH)) Q V A B Phi hf0 hf2 hfM hN hd (by linarith) hNT hdT hlog
      (by exact_mod_cast hfreq) hpow hlocal hlam (by positivity) hQ.le hV.le
      (PRZZWindowScaleSupply.scaled_support F0 Q hQ hs0) hs2 hsF (hshift B hB) hnorm
      (hshift A hA) hsep (PRZZWindowScaleSupply.sum_shift S T A B hL hA hB) hscale hPhi hsPhi
    apply hh.trans_eq
    simp only [Real.rpow_add ht]
    ring

theorem body_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eD eH tau S r bM : ℝ)
    (heD : 0 ≤ eD) (heH : 0 ≤ eH) (htau : 0 < tau) (hS : 0 ≤ S)
    (hr : 0 < r) (hbM : 0 ≤ bM)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F0 F2 F : ℝ → ℂ) (N d s : ℕ)
      (T Q V : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s)) →
      0 < N → 0 < d → 72 ≤ T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T →
      1 ≤ Real.log T → S ≤ Real.log T →
      0 < Q → 0 < V → Q ≤ 2*T → V ≤ 2*T → (2:ℝ)^s ≤ T^bM →
      Function.support F0 ⊆ Icc (1/2:ℝ) 3 →
      Function.support F2 ⊆ Icc (V/2) (3*V) → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d (PRZZWindowCentralAssembly.bodyCut T V eH s d 0 0 0)
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) T ((2:ℝ)^s)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient ks n:ℂ)) F (scaledCutoff F0 Q) F2 Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      C*T^(tau+eD+eH)*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := window_target hWeil hDI K hK js ks eD eH tau S r bM
    heD heH htau hS hr hbM width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨C,hC,?_⟩
  intro F0 F2 F N d s T Q V A B Phi hf0 hf2 hfM hN hd hT hNT hdT hlog hST
    hQ hV hQT hVT hM hs0 hs2 hsF hA hB hsep hPhi hsPhi
  by_cases hraw : PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1
  · have hz : PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) 1 = ∅ := by
      simp [PRZZAStar.indices]
    simp only [PRZZWindowCentralAssembly.bodyCut,if_pos hraw]
    rw [positive_eq]
    simp only [Nat.cast_zero,zero_add,PRZZMixedLiteral.literal,hz,Finset.sum_empty,norm_zero]
    unfold PRZZOptimalPowers.target
    positivity
  · have hh := h F0 F2 F N d s T Q V A B Phi hf0 hf2 hfM hN hd hT hNT hdT hlog hST
      hQ hV hQT hVT hM (le_of_not_ge hraw) hs0 hs2 hsF hA hB hsep hPhi hsPhi
    simpa only [PRZZWindowCentralAssembly.bodyCut,if_neg hraw,PRZZWindowCentralAssembly.windowCut] using hh

#print axioms body_target
#print axioms window_target
#print axioms positive_absorbed
#print axioms positive_target
end XiPrime8845.PRZZClassWidePoisson
