import PRZZInversePhase
import PRZZZeroExtension
import PRZZTypeIFrequency
import PRZZNuBounds

/-! Type I coprimality cost with the original row variation. First bound
unweighted prefixes, then apply Abel on the original index. No dilation
variation or arbitrary-subset Weil estimate is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ContDiff
open Finset
namespace XiPrime8845.PRZZTypeICost
open PRZZKloostermanInputs PRZZTypeI PRZZTypeICoprime
set_option maxHeartbeats 2000000

theorem inverse_coprime (q ell : ℕ) (hq : 0 < q) (he : ell.Coprime q) :
    (inverseResidue q ell).Coprime q := by
  letI : NeZero q := ⟨hq.ne'⟩
  apply (ZMod.isUnit_iff_coprime _ q).mp
  change IsUnit ((((ell:ZMod q)⁻¹).val:ℕ):ZMod q)
  rw [ZMod.natCast_zmod_val]
  exact ⟨⟨(ell:ZMod q)⁻¹,(ell:ZMod q),
    by rw [mul_comm,ZMod.coe_mul_inv_eq_one ell he],
    ZMod.coe_mul_inv_eq_one ell he⟩,rfl⟩

theorem frequency_gcd (q ell : ℕ) (hq : 0 < q) (he : ell.Coprime q) (a : ℤ) :
    (a*(inverseResidue q ell:ℤ)).natAbs.gcd q = a.natAbs.gcd q := by
  rw [Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.Coprime.gcd_mul_right_cancel a.natAbs (inverse_coprime q ell hq he)

theorem prefix_bound (hWeil : WeilIncomplete) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q N : ℕ, d ≠ 0 → 1 ≤ q → ∀ a : ℤ,
      ‖restrictedSum d q N a (fun _ => 1)‖ ≤
        C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q) := by
  obtain ⟨C,hC,h⟩ := PRZZInversePhase.restricted_bound hWeil eps heps
  refine ⟨C,hC,?_⟩
  intro d q N hd hq a
  have hb := h d q N hd hq a (fun _ => 1)
  simp only [variation,sub_self,norm_zero,sum_const_zero,add_zero,norm_one,mul_one] at hb
  apply hb.trans
  have hc : 0 ≤ C*Real.rpow (q:ℝ) (1/2+eps) :=
    mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hh : (∑ ell ∈ d.divisors.filter (fun ell => ell.Coprime q),
      ‖(μ ell:ℂ)‖*((a*(inverseResidue q ell:ℤ)).natAbs.gcd q:ℝ)*(1+(N/ell:ℕ)/(q:ℝ))) ≤
      (d.divisors.card:ℝ)*(a.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q) := by
    calc
      _ ≤ ∑ ell ∈ d.divisors.filter (fun ell => ell.Coprime q),
          (a.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q) := by
        apply sum_le_sum; intro ell hell
        rw [frequency_gcd q ell (by omega) (mem_filter.mp hell).2 a]
        have hm : ‖(μ ell:ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := ell))
        have hn : (N/ell:ℕ) ≤ N := Nat.div_le_self _ _
        have hr : 1+(N/ell:ℕ)/(q:ℝ) ≤ 1+(N:ℝ)/q := by gcongr
        exact (mul_le_mul
          (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)) hr
          (by positivity) (by positivity)).trans_eq (by ring)
      _ ≤ _ := by
        rw [sum_const,nsmul_eq_mul]
        have hn : ((d.divisors.filter (fun ell => ell.Coprime q)).card:ℝ) ≤ d.divisors.card := by
          exact_mod_cast card_filter_le d.divisors (fun ell => ell.Coprime q)
        exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hh hc).trans_eq (by ring)

/-- All divisor-row variation costs are replaced by one original-row
variation. The only extra arithmetic cost is the divisor count of d. -/
theorem weighted_bound (hWeil : WeilIncomplete) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q N : ℕ, d ≠ 0 → 1 ≤ q → ∀ a : ℤ, ∀ w : ℕ → ℂ,
      ‖restrictedSum d q N a w‖ ≤
        C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.natAbs.gcd q:ℝ)*(1+(N:ℝ)/q)*
          variation (fun j => w (j+1)) N := by
  classical
  obtain ⟨C,hC,h⟩ := prefix_bound hWeil eps heps
  refine ⟨C,hC,?_⟩
  intro d q N hd hq a w
  let z := fun j => if d.Coprime (j+1) ∧ (j+1).Coprime q then
    e ((a:ℝ)*inverseResidue q (j+1)/q) else 0
  have he (K : ℕ) (v : ℕ → ℂ) : restrictedSum d q K a v =
      ∑ j ∈ range K, v (j+1)*z j := by
    unfold restrictedSum
    rw [show Icc 1 K = Ico 1 (K+1) by ext n; simp,sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply sum_congr rfl; intro j hj
    simp only [z,show 1+j=j+1 by omega,mul_ite,mul_zero]
  rw [he]
  apply abel_bound
  intro K hK
  have hb := h d q K hd hq a
  rw [he] at hb
  simp only [one_mul] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  gcongr

#print axioms inverse_coprime
#print axioms frequency_gcd
#print axioms prefix_bound
#print axioms weighted_bound

/-- Actual sharp source rows: the whole-row smooth variation is supplied,
uniformly before d,h,j,q,a and the Mellin frequency are chosen. -/
theorem actual_bound (hWeil : WeilIncomplete) (F0 : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j q : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ, ∀ a : ℤ,
      0 < d → 0 < h → 1 ≤ q → 1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖restrictedSum d q N a (PRZZResidualRow.weight N d j h
        (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t)‖ ≤
      C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(a.natAbs.gcd q:ℝ)*
        (1+(N:ℝ)/q)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := weighted_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := PRZZZeroExtension.full_variation F0 hf hcF eta S Z heta hS hZ
  refine ⟨Cw*Cv,mul_pos hCw hCv,?_⟩
  intro N d h j q T Q t alpha a hd hh hq hT hNT hhT ha hz
  apply (hw d q N hd.ne' hq a _).trans
  exact (mul_le_mul_of_nonneg_left
    (hv N d h j T Q t alpha hd hh hT hNT hhT ha hz)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCw.le
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (by positivity))).trans_eq (by simp only [Real.rpow_eq_pow]; ring)

#print axioms actual_bound

/-- Both frequency signs, with the extra d-coprimality already accounted
for. Averaging gcd costs leaves exactly tau(d)*tau(q). -/
theorem frequency_bound (hWeil : WeilIncomplete) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q N A : ℕ, d ≠ 0 → 1 ≤ q →
      ∀ sign : ℤ, sign.natAbs = 1 → ∀ w : ℕ → ℂ,
      (∑ a ∈ Icc 1 A, ‖restrictedSum d q N (sign*(a:ℤ)) w‖) ≤
        C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(N:ℝ)/q)*
          variation (fun j => w (j+1)) N*(A:ℝ)*q.divisors.card := by
  obtain ⟨C,hC,h⟩ := weighted_bound hWeil eps heps
  refine ⟨C,hC,?_⟩
  intro d q N A hd hq sign hs w
  let B := C*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(N:ℝ)/q)*
    variation (fun j => w (j+1)) N
  have hv : 0 ≤ variation (fun j => w (j+1)) N := by unfold variation; positivity
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _))
      (by positivity)) hv
  calc
    _ ≤ ∑ a ∈ Icc 1 A, B*(a.gcd q:ℝ) := by
      apply sum_le_sum; intro a ha
      have hb := h d q N hd hq (sign*(a:ℤ)) w
      simp only [Int.natAbs_mul,hs,Int.natAbs_natCast,one_mul] at hb
      exact hb.trans_eq (by dsimp [B]; ring)
    _ = B*(∑ a ∈ Icc 1 A, (a.gcd q:ℝ)) := by rw [mul_sum]
    _ ≤ B*((A:ℝ)*q.divisors.card) := mul_le_mul_of_nonneg_left
      (PRZZTypeIFrequency.gcd_sum_real A q (by omega)) hB
    _ = _ := by dsimp [B]; ring

#print axioms frequency_bound

theorem divisor_pair_absorbed (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ d q : ℕ, 0 < d → 0 < q → ∀ T : ℝ,
      (d:ℝ) ≤ T → (q:ℝ) ≤ T →
      (d.divisors.card:ℝ)*(q.divisors.card:ℝ) ≤ C*T^eps := by
  obtain ⟨D,hD,h⟩ := PRZZNuBounds.divisors_subpower (eps/2) (by positivity)
  refine ⟨D*D,mul_pos hD hD,?_⟩
  intro d q hd hq T hdT hqT
  have hT : 0 < T := (by exact_mod_cast hd : (0:ℝ)<d).trans_le hdT
  have hb (n : ℕ) (hn : 0 < n) (hnT : (n:ℝ) ≤ T) :
      (n.divisors.card:ℝ) ≤ D*T^(eps/2) :=
    (h n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hnT (by positivity)) hD.le)
  have he : T^(eps/2)*T^(eps/2) = T^eps := by
    rw [← Real.rpow_add hT]; congr 1; ring
  apply (mul_le_mul (hb d hd hdT) (hb q hq hqT) (Nat.cast_nonneg _) (by positivity)).trans_eq
  calc
    _ = (D*D)*(T^(eps/2)*T^(eps/2)) := by ring
    _ = _ := by rw [he]

#print axioms divisor_pair_absorbed

theorem actual_frequency_bound (hWeil : WeilIncomplete) (F0 : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (eps eta S Z : ℝ) (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j q A : ℕ, ∀ T Q t : ℝ, ∀ alpha : ℂ,
      0 < d → 0 < h → 1 ≤ q → 1 < T → (N:ℝ)+1 ≤ T →
      (d:ℝ) ≤ T → (h:ℝ) ≤ T → (q:ℝ) ≤ T →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ∀ sign : ℤ, sign.natAbs = 1 →
      (∑ a ∈ Icc 1 A, ‖restrictedSum d q N (sign*(a:ℤ))
        (PRZZResidualRow.weight N d j h (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t)‖) ≤
        C*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)*(1+|t|)*T^eta := by
  obtain ⟨Cw,hCw,hw⟩ := frequency_bound hWeil eps heps
  obtain ⟨Cv,hCv,hv⟩ := PRZZZeroExtension.full_variation F0 hf hcF (eta/2) S Z (by positivity) hS hZ
  obtain ⟨Cd,hCd,hdv⟩ := divisor_pair_absorbed (eta/2) (by positivity)
  refine ⟨Cw*Cd*Cv,by positivity,?_⟩
  intro N d h j q A T Q t alpha hd hh hq hT hNT hdT hhT hqT ha hz sign hs
  let w := PRZZResidualRow.weight N d j h (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t
  let B := Cw*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg
    (mul_nonneg hCw.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (by positivity)) (Nat.cast_nonneg _)
  have hv0 : 0 ≤ variation (fun n => w (n+1)) N := by unfold variation; positivity
  have hv' := hv N d h j T Q t alpha hd hh hT hNT hhT ha hz
  have hd' := hdv d q hd (by omega) T hdT hqT
  have he : T^(eta/2)*T^(eta/2) = T^eta := by
    rw [← Real.rpow_add (by linarith : 0 < T)]; congr 1; ring
  calc
    _ ≤ B*((d.divisors.card:ℝ)*q.divisors.card)*variation (fun n => w (n+1)) N :=
      (hw d q N A hd.ne' hq sign hs w).trans_eq (by dsimp [B]; ring)
    _ ≤ B*(Cd*T^(eta/2))*(Cv*(1+|t|)*T^(eta/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd' hB) hv' hv0 (mul_nonneg hB (by positivity))
    _ = _ := by
      calc
        _ = (Cw*Cd*Cv)*Real.rpow q (1/2+eps)*(1+(N:ℝ)/q)*(A:ℝ)*(1+|t|)*
            (T^(eta/2)*T^(eta/2)) := by dsimp [B]; ring
        _ = _ := by rw [he]

#print axioms actual_frequency_bound
end XiPrime8845.PRZZTypeICost
