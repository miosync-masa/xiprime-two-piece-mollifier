import PRZZActualLoss
import PRZZActualCasePowers

/-! The actual small/Type I/common prefactors share one strict exponent
budget. The scale inflation c is fixed before height, not absorbed into
a height-dependent constant. Local frequency and outer-mass suppliers
remain separate from this scalar loss calculation. -/
noncomputable section
namespace XiPrime8845.PRZZThreeCaseLoss
open PRZZActualLoss
set_option maxHeartbeats 3000000

theorem typeI_absorbed (Ci c eps eta rho beta delta : ℝ)
    (hi : 0 ≤ Ci) (hc : 0 < c) (he : 0 ≤ eps) (hn : 0 ≤ eta)
    (hr : 0 ≤ rho) (hb : 0 ≤ beta)
    (hmargin : (6+rho)*eta+(3+rho)*eps+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T A d V : ℝ,
      0 ≤ N → N+1 ≤ T → 1 ≤ Real.log T → 0 ≤ A → A ≤ T^rho →
      0 ≤ d → d ≤ T → 0 ≤ V → V ≤ N →
      d^eta*N^beta*T^eta*(Real.log T)^2*
        (Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*(2*V)^eps) ≤ C*T^delta := by
  have hm : (6+rho)*eta+eps+beta < delta := by nlinarith
  obtain ⟨C,hC,h⟩ := PRZZOptimalOuter.power_log_absorbed 2
    ((6+rho)*eta+eps+beta) delta hm
  let b := Ci*c^eta*(2:ℝ)^eps
  have hbn : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨b*C+1,by positivity,?_⟩
  intro N T A d V hN hNT hL hA hAT hd hdT hV hVN
  have hT : 1 ≤ T := by linarith
  have ht : 0 < T := by linarith
  have hNN : N ≤ T := by linarith
  have hVT : V ≤ T := hVN.trans hNN
  have hp : d^eta*N^beta*T^eta*(Real.log T)^2*
      (Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*(2*V)^eps) ≤
      b*(T^((6+rho)*eta+eps+beta)*(Real.log T)^2) := by
    calc
      _ ≤ T^eta*T^beta*T^eta*(Real.log T)^2*
          (Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*(T^rho)^eta*(2*T)^eps) := by gcongr
      _ = _ := by
        rw [Real.mul_rpow hc.le ht.le,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht.le,
          ← Real.rpow_mul ht.le]
        rw [show (6+rho)*eta+eps+beta = eta+beta+eta+eta+eta+eta+eta+rho*eta+eps by ring]
        simp only [Real.rpow_add ht]
        dsimp [b]
        ring
  have hh := mul_le_mul_of_nonneg_left (h T hT) hbn
  have hz := Real.rpow_nonneg ht.le delta
  nlinarith

theorem small_absorbed (Cs eta rho beta delta : ℝ)
    (hs : 0 ≤ Cs) (hn : 0 ≤ eta) (hb : 0 ≤ beta)
    (hmargin : (3+rho)*eta+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T A d : ℝ,
      0 ≤ N → N+1 ≤ T → 1 ≤ Real.log T → 0 ≤ A → A ≤ T^rho →
      0 ≤ d → d ≤ T →
      d^eta*N^beta*T^eta*(Real.log T)^2*(2*Cs*T^eta*A^eta) ≤ C*T^delta := by
  obtain ⟨C,hC,h⟩ := PRZZOptimalOuter.power_log_absorbed 2 ((3+rho)*eta+beta) delta hmargin
  refine ⟨2*Cs*C+1,by positivity,?_⟩
  intro N T A d hN hNT hL hA hAT hd hdT
  have hT : 1 ≤ T := by linarith
  have ht : 0 < T := by linarith
  have hNN : N ≤ T := by linarith
  have hp : d^eta*N^beta*T^eta*(Real.log T)^2*(2*Cs*T^eta*A^eta) ≤
      2*Cs*(T^((3+rho)*eta+beta)*(Real.log T)^2) := by
    calc
      _ ≤ T^eta*T^beta*T^eta*(Real.log T)^2*(2*Cs*T^eta*(T^rho)^eta) := by gcongr
      _ = _ := by
        rw [← Real.rpow_mul ht.le,
          show (3+rho)*eta+beta = eta+beta+eta+eta+rho*eta by ring]
        simp only [Real.rpow_add ht]
        ring
  have hh := mul_le_mul_of_nonneg_left (h T hT) (show 0 ≤ 2*Cs by positivity)
  have hz := Real.rpow_nonneg ht.le delta
  nlinarith

/-- Precisely the three normalized prefactors in row_normalized, including
11 and 22 and the HB scale inflation. One delta covers all three cases. -/
theorem three_case_absorbed (Cs Ci Cg Cd Cr Cp Cv c eps eta rho beta delta : ℝ)
    (hs : 0 ≤ Cs) (hi : 0 ≤ Ci) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd)
    (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv) (hc : 0 < c)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ beta)
    (hmargin : (6+rho)*eta+(3+rho)*eps+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T A d V : ℝ,
      0 ≤ N → N+1 ≤ T → 1 ≤ Real.log T → 0 ≤ A → A ≤ T^rho →
      0 ≤ d → d ≤ T → 0 ≤ V → V ≤ N →
      d^eta*N^beta*T^eta*(Real.log T)^2*
        (2*Cs*T^eta*A^eta+
          11*(Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*(2*V)^eps)+
          22*(PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0*
            ((2*c)*(2*c^2)^2))) ≤ C*T^delta := by
  have hm : (3+rho)*eta+beta < delta := by nlinarith
  obtain ⟨Cs',hs',hsmall⟩ := small_absorbed Cs eta rho beta delta hs hn hb hm
  obtain ⟨Ci',hi',htype⟩ := typeI_absorbed Ci c eps eta rho beta delta hi hc he hn hrho hb hmargin
  obtain ⟨Cd',hd',hcommon⟩ := common_aggregation_absorbed Cg Cd Cr Cp Cv eps eta rho beta delta
    hg hd hr hp hv he hn hb hmargin
  let b := (2*c)*(2*c^2)^2
  have hbn : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨Cs'+11*Ci'+22*b*Cd',by positivity,?_⟩
  intro N T A d V hN hNT hL hA hAT hd0 hdT hV hVN
  have h1 := hsmall N T A d hN hNT hL hA hAT hd0 hdT
  have h2 := mul_le_mul_of_nonneg_left (htype N T A d V hN hNT hL hA hAT hd0 hdT hV hVN)
    (by norm_num : (0:ℝ) ≤ 11)
  have h3 := mul_le_mul_of_nonneg_left (hcommon N T A d hN hNT hL hA hAT hd0 hdT)
    (show 0 ≤ 22*b by positivity)
  have hh := add_le_add (add_le_add h1 h2) h3
  dsimp only [b] at hh ⊢
  nlinarith only [hh]

#print axioms typeI_absorbed
#print axioms small_absorbed
#print axioms three_case_absorbed

/-- Substitute the unified loss estimate into the literal three-case row
normalization. The local frequency condition is still explicit. -/
theorem normalized_row_absorbed (Cs Ci Cg Cd Cr Cp Cv eps eta rho beta delta : ℝ)
    (K : ℕ) (ks : List ℕ)
    (hs : 0 ≤ Cs) (hi : 0 ≤ Ci) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd)
    (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ beta)
    (hmargin : (6+rho)*eta+(3+rho)*eps+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N j l : ℕ, ∀ T A d lam : ℝ,
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → d ≤ T → 1 ≤ lam →
      (2:ℝ)^j ≤ N → (2:ℝ)^l ≤ N →
      A ≤ lam*(((2:ℝ)^j/2^((ks.length+1)*(2*K)))*(2:ℝ)^l/T) →
      d^eta*(N:ℝ)^beta*T^eta*(Real.log T)^2*
        (T/(d*((2:ℝ)^j/2^((ks.length+1)*(2*K)))*(2:ℝ)^l)*
          (PRZZActualCaseSum.smallBudget Cs T A eta l+
            PRZZActualCaseSum.largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks)) ≤
        C*T^delta*lam*PRZZOptimalPowers.target N T/d := by
  let c : ℝ := 2^((ks.length+1)*(2*K))
  obtain ⟨C,hC,h⟩ := three_case_absorbed Cs Ci Cg Cd Cr Cp Cv c eps eta rho beta delta
    hs hi hg hd hr hp hv (by dsimp [c]; positivity) he hn hrho hb hmargin
  refine ⟨C,hC,?_⟩
  intro N j l T A d lam hN hNT hL hA hAT hd0 hdT hl hj hlN hf
  have hT : 0 < T := by linarith
  have h1 := PRZZActualCasePowers.row_normalized Cs Ci Cg Cd Cr Cp Cv eps eta T A d lam
    N K j l ks hs hi hg hd hr hp hv hN (by linarith) hd0 hA hl hj hlN hf
  dsimp only at h1
  have h2 := h N T A d ((2:ℝ)^l) (by positivity) hNT hL hA hAT hd0.le hdT (by positivity) hlN
  have hfac : 0 ≤ d^eta*(N:ℝ)^beta*T^eta*(Real.log T)^2 := by positivity
  have htarg : 0 ≤ lam*PRZZOptimalPowers.target N T/d := by
    unfold PRZZOptimalPowers.target
    positivity
  have hh := mul_le_mul_of_nonneg_left h1 hfac
  have hb' := mul_le_mul_of_nonneg_right h2 htarg
  have heq : (2:ℝ)^(l+1) = 2*(2:ℝ)^l := by rw [pow_succ]; ring
  rw [heq] at hh
  apply hh.trans
  convert hb' using 1 <;> (try dsimp only [c]) <;> ring

#print axioms normalized_row_absorbed
end XiPrime8845.PRZZThreeCaseLoss
