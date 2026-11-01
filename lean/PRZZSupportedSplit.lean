import SmoothMobius
import PRZZCoefficientSeparation

/-! Unique supported/coprime splitting, with prime powers retained.
The summand is arbitrary: no cutoff or analytic weight is discarded. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSupportedSplit
attribute [local instance] Classical.propDecidable
open SmoothMobius
set_option maxHeartbeats 2000000

theorem supported_coprime (d h r : ℕ) (hs : supported d h)
    (hr : d.Coprime r) : h.Coprime r := by
  by_contra hc
  obtain ⟨p,hp,hh,hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  exact hp.not_dvd_one (hr.gcd_eq_one ▸ Nat.dvd_gcd (hs p hp hh) hpr)

theorem exists_split (d n : ℕ) (hn : 0 < n) :
    ∃ h r : ℕ, 0 < h ∧ 0 < r ∧ supported d h ∧ d.Coprime r ∧ h*r = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hc : d.Coprime n
    · exact ⟨1,n,by omega,hn,fun p hp hh => False.elim (hp.not_dvd_one hh),hc,one_mul n⟩
    obtain ⟨p,hp,hpd,hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨m,hm⟩ := hpn
    have hmpos : 0 < m := by nlinarith
    have hmlt : m < n := by nlinarith [hp.two_le]
    obtain ⟨h,r,hh,hr,hs,hc,he⟩ := ih m hmlt hmpos
    refine ⟨p*h,r,Nat.mul_pos hp.pos hh,hr,?_,hc,?_⟩
    · apply (supported_mul d p h).mpr
      exact ⟨fun q hq hqp => (Nat.dvd_prime hp).mp hqp |>.elim
        (fun hq1 => False.elim (hq.ne_one hq1)) (fun hqp => hqp ▸ hpd),hs⟩
    · rw [mul_assoc,he,← hm]

theorem split_unique (d h r h' r' : ℕ)
    (hs : supported d h) (hs' : supported d h')
    (hc : d.Coprime r) (hc' : d.Coprime r')
    (hh : 0 < h) (he : h*r = h'*r') : h = h' ∧ r = r' := by
  have hd : h ∣ h' := (supported_coprime d h r' hs hc').dvd_of_dvd_mul_right
    (he ▸ Nat.dvd_mul_right h r)
  have hd' : h' ∣ h := (supported_coprime d h' r hs' hc).dvd_of_dvd_mul_right
    (he.symm ▸ Nat.dvd_mul_right h' r')
  have hh' := Nat.dvd_antisymm hd hd'
  refine ⟨hh',?_⟩
  rw [← hh'] at he
  exact Nat.eq_of_mul_eq_mul_left hh he

/-- A finite exact reindexing; the product restriction is not enlarged
to an uncut rectangle. -/
theorem sum_split {R : Type*} [AddCommMonoid R] (d N : ℕ) (F : ℕ → R) :
    (∑ n ∈ Icc 1 N, F n) =
      ∑ h ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        if supported d h ∧ d.Coprime r ∧ h*r ≤ N then F (h*r) else 0 := by
  classical
  let s := ((Icc 1 N).product (Icc 1 N)).filter
    (fun z : ℕ × ℕ => supported d z.1 ∧ d.Coprime z.2 ∧ z.1*z.2 ≤ N)
  have he : (∑ z ∈ s, F (z.1*z.2)) = ∑ n ∈ Icc 1 N, F n := by
    apply sum_nbij (fun z : ℕ × ℕ => z.1*z.2)
    · intro z hz
      rcases mem_filter.mp hz with ⟨hz,hs,hc,hN⟩
      have hz := mem_product.mp hz
      exact mem_Icc.mpr ⟨by nlinarith [(mem_Icc.mp hz.1).1,(mem_Icc.mp hz.2).1],hN⟩
    · intro z hz w hw he
      rcases mem_filter.mp hz with ⟨hz,hs,hc,hN⟩
      rcases mem_filter.mp hw with ⟨hw,hs',hc',hN'⟩
      have hh := (mem_Icc.mp (mem_product.mp hz).1).1
      exact Prod.ext (split_unique d z.1 z.2 w.1 w.2 hs hs' hc hc' (by omega) he).1
        (split_unique d z.1 z.2 w.1 w.2 hs hs' hc hc' (by omega) he).2
    · intro n hn
      have hn := mem_Icc.mp hn
      obtain ⟨h,r,hh,hr,hs,hc,he⟩ := exists_split d n (by omega)
      refine ⟨(h,r),?_,he⟩
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hh,?_⟩,mem_Icc.mpr ⟨hr,?_⟩⟩,hs,hc,he ▸ hn.2⟩
      · nlinarith
      · nlinarith
    · intros; rfl
  rw [← he]
  simp only [s,sum_filter,Finset.product_eq_sprod,Finset.sum_product]

/-- The residual is coprime to the entire supported coefficient argument,
so the original coefficient allocation theorem now has its input supplied. -/
theorem source_allocation (js : List ℕ) (d h r : ℕ)
    (hs : supported d h) (hc : d.Coprime r) :
    PRZZGCoefficient.coefficient js (d*(h*r)) =
      PRZZCoefficientSeparation.evaluate (PRZZCoefficientSeparation.allocations js) (d*h) r := by
  rw [← mul_assoc]
  exact PRZZCoefficientSeparation.coefficient_separation js (d*h) r
    (hc.mul_left (supported_coprime d h r hs hc))

def hSupport (N d : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun h => supported d h ∧ d*h ≤ N)

theorem mem_hSupport (N d h : ℕ) (hh : h ∈ hSupport N d) :
    1 ≤ h ∧ d*h ≤ N ∧ supported d h := by
  have hh := mem_filter.mp hh
  exact ⟨(mem_Icc.mp hh.1).1,hh.2.2,hh.2.1⟩

theorem sum_cutoff {R : Type*} [AddCommMonoid R] (d N : ℕ) (hd : 1 ≤ d) (F : ℕ → R) :
    (∑ n ∈ Icc 1 N, if d*n ≤ N then F n else 0) =
      ∑ h ∈ hSupport N d, ∑ r ∈ Icc 1 N,
        if d.Coprime r ∧ d*(h*r) ≤ N then F (h*r) else 0 := by
  classical
  rw [sum_split d N]
  simp only [hSupport,sum_filter]
  apply sum_congr rfl
  intro h hh
  have hh1 := (mem_Icc.mp hh).1
  by_cases hs : supported d h ∧ d*h ≤ N
  · simp only [hs,if_true]
    apply sum_congr rfl
    intro r hr
    by_cases hc : d.Coprime r <;> by_cases hcut : d*(h*r) ≤ N
    · have hn : h*r ≤ N := by nlinarith
      simp [hs.1,hc,hcut,hn]
    · simp [hc,hcut]
    · simp [hc]
    · simp [hc]
  · simp only [hs,if_false]
    apply sum_eq_zero
    intro r hr
    have hr1 := (mem_Icc.mp hr).1
    by_cases hcut : d*(h*r) ≤ N
    · have hdh : d*h ≤ N := by nlinarith
      have hns : ¬ supported d h := fun h => hs ⟨h,hdh⟩
      simp [hns]
    · simp [hcut]

#print axioms mem_hSupport
#print axioms sum_cutoff
#print axioms sum_split
#print axioms source_allocation
#print axioms supported_coprime
#print axioms exists_split
#print axioms split_unique
end XiPrime8845.PRZZSupportedSplit
