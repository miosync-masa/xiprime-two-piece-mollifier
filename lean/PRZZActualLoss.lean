import PRZZCommonCellBound
import PRZZOptimalOuter

/-! Explicit loss exponents from the actual common cell budget.
The frequency envelope A <= T^rho is retained as a premise; it is not
silently supplied for every original cutoff configuration. -/
noncomputable section
namespace XiPrime8845.PRZZActualLoss
set_option maxHeartbeats 2000000

theorem common_power (Cg Cd Cr Cp Cv eps eta N T A rho : ℝ)
    (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hN : 0 ≤ N) (hNT : N+1 ≤ T)
    (hT : 1 ≤ T) (hA : 0 ≤ A) (hAT : A ≤ T^rho) :
    PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 ≤
      (2*Cr*Cg*Cp*Cg*Cd*Cv)*(1+2*Real.log T)*
        T^((4+rho)*eta+(3+rho)*eps) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog : Real.log (N+1) ≤ Real.log T := Real.log_le_log (by positivity) hNT
  have hlog0 : 0 ≤ Real.log (N+1) := Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hNN : N ≤ T := by linarith
  have hprod : N*N*A*N ≤ T^((3:ℝ)+rho) := by
    calc
      _ ≤ T*T*(T^rho)*T := by gcongr
      _ = _ := by
        rw [show (3:ℝ)+rho = rho+3 by ring,Real.rpow_add hT0]
        norm_num [Real.rpow_natCast]
        ring
  unfold PRZZCommonCellBound.budget
  simp only [abs_zero,add_zero,mul_one]
  calc
    _ ≤ 2*((1+2*Real.log T)*
        ((Cr*T^eta)*(Cg*T^eta)*((Cp*(T^rho)^eta)*(Cg*T^eta))*Cd*
          ((T^(3+rho))^eps)))*(Cv*T^eta) := by gcongr
    _ = _ := by
      rw [← Real.rpow_mul hT0.le,← Real.rpow_mul hT0.le]
      simp only [mul_assoc]
      rw [show (4+rho)*eta+(3+rho)*eps = eta+eta+rho*eta+eta+(3+rho)*eps+eta by ring]
      simp only [Real.rpow_add hT0]
      ring

/-- The explicit cell exponent consumes part of delta; only the remaining
strict margin is spent on logarithms. Constants precede N,T,A. -/
theorem common_absorbed (Cg Cd Cr Cp Cv eps eta rho delta : ℝ)
    (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta)
    (hmargin : (4+rho)*eta+(3+rho)*eps < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T A : ℝ,
      0 ≤ N → N+1 ≤ T → 1 ≤ Real.log T → 0 ≤ A → A ≤ T^rho →
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 ≤ C*T^delta := by
  obtain ⟨C,hC,h⟩ := PRZZOptimalOuter.power_log_absorbed 1
    ((4+rho)*eta+(3+rho)*eps) delta hmargin
  let c := 2*Cr*Cg*Cp*Cg*Cd*Cv
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨3*c*C+1,by positivity,?_⟩
  intro N T A hN hNT hL hA hAT
  have hT : 1 ≤ T := by linarith
  have hb := common_power Cg Cd Cr Cp Cv eps eta N T A rho hg hd hr hp hv he hn hN hNT hT hA hAT
  have hh := h T hT
  simp only [pow_one] at hh
  have hf := mul_le_mul_of_nonneg_left hh (show 0 ≤ 3*c by positivity)
  have ht := Real.rpow_nonneg (by linarith : 0 ≤ T) ((4+rho)*eta+(3+rho)*eps)
  have hz := Real.rpow_nonneg (by linarith : 0 ≤ T) delta
  change _ ≤ c*(1+2*Real.log T)*T^((4+rho)*eta+(3+rho)*eps) at hb
  nlinarith [mul_nonneg hc ht]

#print axioms common_power
#print axioms common_absorbed

/-- Add the actual d^eta N^beta h-average cost, the T^eta branch cost,
and the log^2 outer cost. This audits their combined exponent, not an
unproved bound on the remaining row sum or on its local mass. -/
theorem common_aggregation_absorbed (Cg Cd Cr Cp Cv eps eta rho beta delta : ℝ)
    (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) (hr : 0 ≤ Cr) (hp : 0 ≤ Cp) (hv : 0 ≤ Cv)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hb : 0 ≤ beta)
    (hmargin : (6+rho)*eta+(3+rho)*eps+beta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T A d : ℝ,
      0 ≤ N → N+1 ≤ T → 1 ≤ Real.log T → 0 ≤ A → A ≤ T^rho →
      0 ≤ d → d ≤ T →
      d^eta*N^beta*T^eta*(Real.log T)^2*
        PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 ≤ C*T^delta := by
  obtain ⟨C,hC,h⟩ := PRZZOptimalOuter.power_log_absorbed 3
    ((6+rho)*eta+(3+rho)*eps+beta) delta hmargin
  let c := 2*Cr*Cg*Cp*Cg*Cd*Cv
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨3*c*C+1,by positivity,?_⟩
  intro N T A d hN hNT hL hA hAT hd0 hdT
  have hT : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hln : 0 ≤ Real.log T := by linarith
  have hNN : N ≤ T := by linarith
  have hpw := common_power Cg Cd Cr Cp Cv eps eta N T A rho
    hg hd hr hp hv he hn hN hNT hT hA hAT
  have hlogN : 0 ≤ Real.log (N+1) := Real.log_nonneg (by linarith)
  have hbudget : 0 ≤ PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 := by
    unfold PRZZCommonCellBound.budget
    positivity
  have hbudget' : PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 ≤
      c*(3*Real.log T)*T^((4+rho)*eta+(3+rho)*eps) := by
    apply hpw.trans
    change c*(1+2*Real.log T)*_ ≤ _
    gcongr
    linarith
  have hbound : d^eta*N^beta*T^eta*(Real.log T)^2*
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 ≤
      3*c*(T^((6+rho)*eta+(3+rho)*eps+beta)*(Real.log T)^3) := by
    calc
      _ ≤ T^eta*T^beta*T^eta*(Real.log T)^2*
          (c*(3*Real.log T)*T^((4+rho)*eta+(3+rho)*eps)) := by
        gcongr
      _ = _ := by
        rw [show (6+rho)*eta+(3+rho)*eps+beta =
          eta+beta+eta+((4+rho)*eta+(3+rho)*eps) by ring]
        simp only [Real.rpow_add hT0]
        ring
  have hh := mul_le_mul_of_nonneg_left (h T hT) (show 0 ≤ 3*c by positivity)
  have hz := Real.rpow_nonneg hT0.le delta
  nlinarith

#print axioms common_aggregation_absorbed
end XiPrime8845.PRZZActualLoss
