import PRZZL1Poisson
import PRZZKloostermanInputs

/-! L1 residue-class and phase transport for Pratt--Robles Section 3.2.
The congruence n*m = -Delta (mod q) gives the negative inverse phase in A*.
Poisson is proved here for a smooth compact weight, not yet the AFE kernel.
No tail removal or AFE identity is asserted. -/
noncomputable section
open scoped ContDiff FourierTransform
namespace XiPrime8845.PRZZL1Residue
open PRZZKloostermanInputs

theorem residue_iff (n q : ℕ) (hn : n.Coprime q) (delta : ℤ) (z : ZMod q) :
    (n:ZMod q)*z = -(delta:ZMod q) ↔
      z = -(delta:ZMod q)*(n:ZMod q)⁻¹ := by
  have hi := ZMod.coe_mul_inv_eq_one n hn
  constructor
  · intro h
    calc
      z = ((n:ZMod q)*(n:ZMod q)⁻¹)*z := by rw [hi,one_mul]
      _ = ((n:ZMod q)*z)*(n:ZMod q)⁻¹ := by ring
      _ = _ := by rw [h]
  · intro h
    rw [h]
    calc
      _ = -(delta:ZMod q)*((n:ZMod q)*(n:ZMod q)⁻¹) := by ring
      _ = _ := by rw [hi,mul_one]

theorem progression_residue (q n : ℕ) (hq : 0 < q) (hn : n.Coprime q)
    (delta k : ℤ) :
    (n:ZMod q)*((-(delta:ℤ)*(inverseResidue q n:ℤ)+(q:ℤ)*k:ℤ):ZMod q) =
      -(delta:ZMod q) := by
  let : NeZero q := ⟨hq.ne'⟩
  apply (residue_iff n q hn delta _).mpr
  simp [inverseResidue]

/-- Literal signed frequency, modulus Jacobian and inverse residue.
Both frequency signs are kept in the integer tsum. -/
theorem poisson_inverse_progression (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (q n : ℕ) (hq : 0 < q) (delta : ℤ) :
    (∑' k : ℤ, f (-(delta:ℝ)*inverseResidue q n+(q:ℝ)*k)) =
      ∑' h : ℤ, (((q:ℝ)⁻¹:ℝ):ℂ)*𝓕 f ((h:ℝ)/q)*
        e (-((h:ℝ)*(delta:ℝ))*inverseResidue q n/q) := by
  rw [PRZZL1Poisson.progression_normalized f hf hs (q:ℝ)
    (-(delta:ℝ)*inverseResidue q n) (by exact_mod_cast hq)]
  apply tsum_congr
  intro h
  congr 1
  unfold e
  push_cast
  congr 1
  ring

#print axioms residue_iff
#print axioms progression_residue
#print axioms poisson_inverse_progression
end XiPrime8845.PRZZL1Residue
