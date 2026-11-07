import PRZZPoissonActualWeight
import PRZZInversePhase
import PRZZAFEProgression
import PRZZGroupedTime
import PRZZPhaseError

/-! Signed AFE congruences and the residue phase in normalized Poisson.
AFE uses m*u-k*v=delta; the literal A* phase uses Delta=-delta.
Sharp quotient cutoffs are retained and are not declared smooth. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform
namespace XiPrime8845.PRZZCongruencePoisson
open PRZZKloostermanInputs
set_option maxHeartbeats 2000000

theorem congruence_iff (u v : ℕ) (hv : 0 < v) (hc : u.Coprime v)
    (m delta : ℤ) :
    (v:ℤ) ∣ m*u-delta ↔ (v:ℤ) ∣ m-delta*(inverseResidue v u:ℤ) := by
  let : NeZero v := ⟨hv.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [inverseResidue,ZMod.natCast_zmod_val,sub_eq_zero]
  have hi := ZMod.coe_mul_inv_eq_one u hc
  constructor
  · intro h
    calc
      (m:ZMod v) = ((m:ZMod v)*u)*(u:ZMod v)⁻¹ := by rw [mul_assoc,hi,mul_one]
      _ = _ := by rw [h]
  · intro h
    rw [h]
    calc
      _ = (delta:ZMod v)*((u:ZMod v)*(u:ZMod v)⁻¹) := by ring
      _ = _ := by rw [hi,mul_one]

theorem progression_iff (u v : ℕ) (hv : 0 < v) (hc : u.Coprime v)
    (m delta : ℤ) :
    (v:ℤ) ∣ m*u-delta ↔ ∃ j : ℤ, m=delta*(inverseResidue v u:ℤ)+v*j := by
  rw [congruence_iff u v hv hc]
  constructor
  · rintro ⟨j,hj⟩; exact ⟨j,by linarith⟩
  · rintro ⟨j,hj⟩; exact ⟨j,by linarith⟩

/-- The original k cutoff is retained alongside the explicit progression. -/
theorem truncated_progression (L u v : ℕ) (hv : 0 < v) (hc : u.Coprime v)
    (m delta : ℤ) :
    (∃ k ∈ Finset.Icc (1:ℤ) L, m*u-k*v=delta) ↔
      (∃ j : ℤ, m=delta*(inverseResidue v u:ℤ)+v*j) ∧
        1 ≤ (m*u-delta)/v ∧ (m*u-delta)/v ≤ L := by
  rw [PRZZAFEProgression.truncated_iff L u v m delta (by exact_mod_cast hv.ne'),
    progression_iff u v hv hc]

/-- The minus sign is supplied by delta=-Delta, not a Fourier convention change. -/
theorem astar_residue_phase (u v h : ℕ) (Delta : ℤ) :
    Complex.exp (2*Real.pi*Complex.I*(h:ℂ)*
      (((-Delta*(inverseResidue v u:ℤ):ℤ):ℝ):ℂ)/(v:ℂ)) =
      PRZZKloostermanInputs.e (-((h:ℝ)*(Delta:ℝ))*inverseResidue v u/v) := by
  unfold PRZZKloostermanInputs.e
  push_cast
  congr 1
  ring

/-- Poisson on the explicit signed residue class. Applying this to a
sharp finite quotient mask still requires smoothing or cutoff removal. -/
theorem poisson_signed (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (u v : ℕ) (hv : 0 < v) (Delta : ℤ) :
    (∑' j : ℤ, f ((-Delta*(inverseResidue v u:ℤ):ℤ)+(v:ℝ)*j)) =
      ∑' h : ℤ, (((v:ℝ)⁻¹:ℝ):ℂ)*𝓕 f ((h:ℝ)/v)*
        PRZZKloostermanInputs.e (-((h:ℝ)*(Delta:ℝ))*inverseResidue v u/v) := by
  rw [PRZZL1Poisson.progression_normalized f hf hs v
    ((-Delta*(inverseResidue v u:ℤ):ℤ):ℝ) (by exact_mod_cast hv)]
  apply tsum_congr
  intro h
  unfold PRZZKloostermanInputs.e
  push_cast
  congr 2
  ring

/-- Every member of the actual finite AFE fibre supplies coprimality and
the explicit residue progression; no per-fibre congruence premise remains. -/
theorem fibre_progression (L N : ℕ) (z : PRZZAFEIndices.Label)
    (i : PRZZAFEIndices.Index) (hi : i ∈ PRZZAFEIndices.fibre L N z) :
    let d := Nat.gcd i.2.1 i.2.2
    let u := i.2.1/d
    let v := i.2.2/d
    ∃ j : ℤ, (i.1.1:ℤ)=z.2.1*(inverseResidue v u:ℤ)+(v:ℤ)*j := by
  dsimp only
  have hmem := Finset.mem_filter.mp hi
  have hr := (Finset.mem_product.mp (Finset.mem_product.mp hmem.1).2).2
  have hr0 : 0 < i.2.2 := (Finset.mem_Icc.mp hr).1
  have hd := Nat.gcd_pos_of_pos_right i.2.1 hr0
  have hv : 0 < i.2.2/Nat.gcd i.2.1 i.2.2 := Nat.div_pos
    (Nat.le_of_dvd hr0 (Nat.gcd_dvd_right i.2.1 i.2.2)) hd
  exact (progression_iff _ _ hv (Nat.coprime_div_gcd_div_gcd hd) _ _).mp
    (PRZZGroupedTime.fibre_quotient L N z i hi).1

/-- The same sign reversal also linearizes the original ratio k*v/(m*u).
This retains the quadratic error, rather than asserting equality of phases. -/
theorem signed_phase_error (m k u v delta t : ℝ) (hmu : m*u ≠ 0)
    (hgap : m*u-k*v=delta) (hsmall : |delta/(m*u)| ≤ 1/2) :
    ‖Complex.exp (Complex.I*((t*Real.log (k*v/(m*u)):ℝ):ℂ))-
      Complex.exp (Complex.I*((t*(-delta)/(m*u):ℝ):ℂ))‖ ≤
        2*|t| *delta^2/(m*u)^2 := by
  have he : k*v/(m*u)=1+(-delta)/(m*u) := by
    apply (div_eq_iff hmu).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hmu]
    linarith only [hgap]
  rw [he]
  simpa [neg_div,mul_div_assoc] using
    PRZZPhaseError.offDiagonal_error t (-delta) m u (by simpa only [neg_div,abs_neg] using hsmall)

#print axioms fibre_progression
#print axioms signed_phase_error
#print axioms congruence_iff
#print axioms progression_iff
#print axioms truncated_progression
#print axioms astar_residue_phase
#print axioms poisson_signed
end XiPrime8845.PRZZCongruencePoisson
