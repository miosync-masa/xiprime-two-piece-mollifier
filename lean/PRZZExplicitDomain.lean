import PRZZQuotientMass
import PRZZHeightMass

/-! Explicit congruence and quotient bounds for the projected AFE fibres.
The sharp analytic estimates still require their original scale hypotheses. -/
noncomputable section
open scoped BigOperators
open Finset Complex
namespace XiPrime8845.PRZZExplicitDomain
open PRZZAFEIndices PRZZQuotientMass PRZZAFEProgression PRZZGroupedTime
set_option maxHeartbeats 3000000

def admissible (L : ℕ) (z : Label) (p : ℕ × ℕ × ℕ) : Prop :=
  let d := Nat.gcd p.2.1 p.2.2
  let u := p.2.1/d
  let v := p.2.2/d
  let q : ℤ := ((p.1:ℤ)*(u:ℤ)-z.2.1)/(v:ℤ)
  d = z.1 ∧ Nat.log 2 u = z.2.2.1 ∧ Nat.log 2 v = z.2.2.2 ∧
    (v:ℤ) ∣ (p.1:ℤ)*(u:ℤ)-z.2.1 ∧ 1 ≤ q ∧ q ≤ L

def domain (L N : ℕ) (z : Label) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (Icc 1 L ×ˢ (Icc 1 N ×ˢ Icc 1 N)).filter (admissible L z)

theorem image_eq_domain (L N : ℕ) (z : Label) :
    (fibre L N z).image project = domain L N z := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    have hmem := mem_filter.mp hi
    have hq := fibre_quotient L N z i hi
    have hg := congrArg (fun z : Label => z.1) hmem.2
    have hj := congrArg (fun z : Label => z.2.2.1) hmem.2
    have hl := congrArg (fun z : Label => z.2.2.2) hmem.2
    apply mem_filter.mpr
    refine ⟨?_,?_⟩
    · exact mem_product.mpr ⟨(mem_product.mp (mem_product.mp hmem.1).1).1,
        (mem_product.mp hmem.1).2⟩
    · exact ⟨hg,hj,hl,hq.1,hq.2.2⟩
  · intro hp
    obtain ⟨hmem,hg,hj,hl,hdiv,hlo,hhi⟩ := mem_filter.mp hp
    let i := restore z p
    have hr := (mem_product.mp (mem_product.mp hmem).2).2
    have hr0 : 0 < p.2.2 := (mem_Icc.mp hr).1
    have hd : 0 < Nat.gcd p.2.1 p.2.2 := Nat.gcd_pos_of_pos_right p.2.1 hr0
    have hv : (p.2.2/Nat.gcd p.2.1 p.2.2 : ℕ) ≠ 0 :=
      Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hr0 (Nat.gcd_dvd_right _ _)) hd)
    let q : ℤ := ((p.1:ℤ)*(p.2.1/Nat.gcd p.2.1 p.2.2:ℕ)-z.2.1)/
      (p.2.2/Nat.gcd p.2.1 p.2.2:ℕ)
    have hq : (q.toNat:ℤ) = q := Int.toNat_of_nonneg (by change 1 ≤ q at hlo; omega)
    have he := (quotient_iff (p.2.1/Nat.gcd p.2.1 p.2.2:ℕ)
      (p.2.2/Nat.gcd p.2.1 p.2.2:ℕ) p.1 z.2.1 q (by exact_mod_cast hv)).mpr ⟨hdiv,rfl⟩
    apply mem_image.mpr
    refine ⟨i,?_,rfl⟩
    apply mem_filter.mpr
    constructor
    · apply mem_product.mpr
      refine ⟨mem_product.mpr ⟨(mem_product.mp hmem).1,?_⟩,(mem_product.mp hmem).2⟩
      apply mem_Icc.mpr
      change 1 ≤ q.toNat ∧ q.toNat ≤ L
      constructor
      · exact_mod_cast (show (1:ℤ) ≤ (q.toNat:ℤ) by rw [hq]; exact hlo)
      · exact_mod_cast (show (q.toNat:ℤ) ≤ L by rw [hq]; exact hhi)
    · change (Nat.gcd p.2.1 p.2.2,
        (p.1:ℤ)*(p.2.1/Nat.gcd p.2.1 p.2.2:ℕ)-
          (q.toNat:ℤ)*(p.2.2/Nat.gcd p.2.1 p.2.2:ℕ),
        Nat.log 2 (p.2.1/Nat.gcd p.2.1 p.2.2),
        Nat.log 2 (p.2.2/Nat.gcd p.2.1 p.2.2)) = z
      rw [hq,he,hj,hl,hg]

theorem fibre_explicit (L N : ℕ) (z : Label) (f : PRZZAFEIndices.Index → ℂ) :
    (∑ i ∈ fibre L N z, f i) = ∑ p ∈ domain L N z, f (restore z p) := by
  rw [fibre_sum,image_eq_domain]

theorem grouped_explicit (L N : ℕ) (f : PRZZAFEIndices.Index → ℂ) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z, f i) =
      ∑ z ∈ labels L N, ∑ p ∈ domain L N z, f (restore z p) := by
  simp_rw [fibre_explicit]

#print axioms image_eq_domain
#print axioms fibre_explicit
#print axioms grouped_explicit
end XiPrime8845.PRZZExplicitDomain
