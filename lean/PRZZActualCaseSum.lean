import PRZZActualCases

/-! Supported h aggregation of actual three-case cells. Each h may have
its own branch, root cutoff and dyadic grid. No analytic cell bound is
assumed. This is before the labelled branch and allocation sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualCaseSum
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

def smallBudget (Cs T A eta : ℝ) (l : ℕ) : ℝ :=
  Cs*T^eta*A^eta*A*((2:ℝ)^(l+1))

def largeBudget (Ci Cg Cd Cr Cp Cv eps eta T A t : ℝ)
    (N K j l : ℕ) (ks : List ℕ) : ℝ :=
  let c : ℝ := 2^((ks.length+1)*(2*K))
  let X : ℝ := (2:ℝ)^j/c
  Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps*
    PRZZCombinedBudget.typeI X A ((2:ℝ)^l) +
  PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
    (((2*c)*(2*c^2)^2)*PRZZCombinedBudget.total X A (PRZZDyadicModulus.bound N l))

/-- All Mellin-frequency loss is linear; the h average adds none. -/
theorem largeBudget_linear (Ci Cg Cd Cr Cp Cv eps eta T A t : ℝ)
    (N K j l : ℕ) (ks : List ℕ) :
    largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks =
      largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks*(1+|t|) := by
  simp only [largeBudget,PRZZCommonCellBound.budget,abs_zero,add_zero,mul_one]
  ring

theorem budget_linear_le (Cs Ci Cg Cd Cr Cp Cv eps eta T A t : ℝ)
    (N K j l : ℕ) (ks : List ℕ) (hsmall : 0 ≤ smallBudget Cs T A eta l) :
    smallBudget Cs T A eta l+largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks ≤
      (smallBudget Cs T A eta l+largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks)*(1+|t|) := by
  rw [largeBudget_linear]
  nlinarith [mul_nonneg hsmall (abs_nonneg t)]

#print axioms largeBudget_linear
#print axioms budget_linear_le

theorem supported_source_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js gs : List ℕ) (r : ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cs Ci Cg Cd Cr Cp Cv C : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧ 0 < C ∧
      ∀ N d j l : ℕ, ∀ T Q D H x y0 t sigma : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → sigma ≤ 0 →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ∀ hs : Finset ℕ,
      (∀ h ∈ hs, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ b : ℕ → Branch,
      (∀ h ∈ hs, b h ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks) →
      ∀ k : (h : ℕ) → Fin (b h).2.length → ℕ,
      let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
      ‖∑ h ∈ hs, (PRZZGCoefficient.sourceG gs r sigma d h:ℂ)*
        PRZZSignedSourceCell.source N d j l h A (b h) (k h)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift x t
          (fun a => nu (frequencies d D H) x y0 (a:ℤ))
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      C*(d:ℝ)^eta*(N:ℝ)^beta*
        (smallBudget Cs T A eta l+largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,hsource⟩ :=
    PRZZActualCases.source_bound hWeil hDI K hK ks js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨Ca,hCa,ha⟩ := PRZZSplitScaleSum.absolute_mass gs r eta beta heta hbeta
  obtain ⟨Cb,hCb,hb⟩ := PRZZGAbsorption.sourceG_average_power gs r (1/4) eta beta (by norm_num) heta hbeta
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,Ca+Cb,hCs,hCi,hCg,hCd,hCr,hCp,hCv,by positivity,?_⟩
  intro N d j l T Q D H x y0 t sigma alpha betaShift hN hd hT hNT hdT hsig hA hal hz hbet hs hhs b hbr k
  dsimp only
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  let Bs := smallBudget Cs T A eta l
  let Bl := largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks
  have hBs : 0 ≤ Bs := by dsimp [Bs,smallBudget,A]; positivity
  have hBl : 0 ≤ Bl := by
    have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    dsimp [Bl,largeBudget,A,PRZZCommonCellBound.budget,PRZZCombinedBudget.total,PRZZCombinedBudget.typeI,PRZZDISeven.envelope]
    positivity
  have hpoint (h : ℕ) (hh : h ∈ hs) :
      ‖PRZZSignedSourceCell.source N d j l h A (b h) (k h)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤ Bs+Bl/(h:ℝ)^(1/4:ℝ) := by
    have hn : h ≤ N := by nlinarith [(hhs h hh).2.1]
    have hhT : (h:ℝ) ≤ T := (by exact_mod_cast hn : (h:ℝ) ≤ N).trans (by linarith)
    exact (hsource N d j l h (b h) (hbr h hh) (k h) T Q D H x y0 t alpha betaShift
      hN hd (hhs h hh).1 hT hNT hdT hhT hA hal hz hbet).trans_eq (by dsimp [Bs,Bl,smallBudget,largeBudget,A]; ring)
  have ha' := ha sigma d N hsig hd hN hs hhs
  have hb' := hb sigma d N hsig hd hN hs hhs
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ h ∈ hs, |PRZZGCoefficient.sourceG gs r sigma d h| * (Bs+Bl/(h:ℝ)^(1/4:ℝ)) := by
      apply sum_le_sum; intro h hh
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hpoint h hh) (abs_nonneg _)
    _ = Bs*(∑ h ∈ hs, |PRZZGCoefficient.sourceG gs r sigma d h|)+
        Bl*(∑ h ∈ hs, |PRZZGCoefficient.sourceG gs r sigma d h|/(h:ℝ)^(1/4:ℝ)) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]; apply sum_congr rfl; intro h hh; ring
    _ ≤ Bs*(Ca*(d:ℝ)^eta*(N:ℝ)^beta)+Bl*(Cb*(d:ℝ)^eta*(N:ℝ)^beta) :=
      add_le_add (mul_le_mul_of_nonneg_left ha' hBs) (mul_le_mul_of_nonneg_left hb' hBl)
    _ ≤ _ := by
      change _ ≤ (Ca+Cb)*(d:ℝ)^eta*(N:ℝ)^beta*(Bs+Bl)
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg (Nat.cast_nonneg d) eta))
        (Real.rpow_nonneg (Nat.cast_nonneg N) beta)) hBl,
        mul_nonneg (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg (Nat.cast_nonneg d) eta))
        (Real.rpow_nonneg (Nat.cast_nonneg N) beta)) hBs]

#print axioms supported_source_bound
end XiPrime8845.PRZZActualCaseSum
