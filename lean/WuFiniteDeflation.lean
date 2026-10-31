import WuCriticalMultiplicity
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Entire removal of a finite divisor. Values at removed zeros are the
analytic extensions, not the totalized quotient (which would be zero there).
The factorization and order restoration hold at every complex point. -/
noncomputable section
open scoped BigOperators
open Complex Filter Topology
namespace XiPrime8845.WuFiniteDeflation
open WuAuxiliaryMultiplicity
set_option maxHeartbeats 2000000

def divisor (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : ℂ :=
  ∏ c ∈ Z, (s-c)^(m c)

theorem divisor_entire (Z : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ (divisor Z m) := by unfold divisor; fun_prop

theorem divisor_order (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) :
    analyticOrderAt (divisor Z m) s = if s ∈ Z then (m s:ℕ∞) else 0 := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp [divisor,analyticOrderAt_eq_zero]
  | @insert c Z hc ih =>
    have he : divisor (insert c Z) m = (fun z => (z-c)^(m c))*divisor Z m := by
      funext z; simp [divisor,hc]
    rw [he,analyticOrderAt_mul (by fun_prop) ((divisor_entire Z m).analyticAt s),ih]
    by_cases hs : s = c
    · subst s; simp [hc,show (fun z : ℂ => (z-c)^(m c)) = ((·-c)^(m c)) from rfl]
    · have hz : (s-c)^(m c) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
      have ho : analyticOrderAt (fun z : ℂ => (z-c)^(m c)) s = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hz)
      rw [ho]
      simp [hs]

theorem iterate_dslope_entire (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (n : ℕ) :
    Differentiable ℂ ((Function.swap dslope c)^[n] f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    exact differentiableOn_univ.mp ((differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
      hf.differentiableOn)

theorem single_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (c : ℂ) (n : ℕ) (hnc : n ≤ analyticOrderNatAt f c) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = (z-c)^n*g z := by
  obtain ⟨p,hp⟩ := hf.analyticAt c
  have hnt := entire_order_ne_top f hf hn c
  have hp0 : p ≠ 0 := by
    intro he
    apply hnt
    apply analyticOrderAt_eq_top.mpr
    exact hp.locally_zero_iff.mpr he
  let g := (Function.swap dslope c)^[p.order] f
  have hg := iterate_dslope_entire f hf c p.order
  have hgc : g c ≠ 0 := hp.iterate_dslope_fslope_ne_zero hp0
  have he : ∀ z, f z = (z-c)^p.order*g z := fun z => by
    simpa only [smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope z
  have ho : analyticOrderNatAt f c = p.order :=
    ((hf.analyticAt c).analyticOrderNatAt_eq_iff hnt).mpr
      ⟨g,hg.analyticAt c,hgc,Eventually.of_forall (fun z => by simpa only [smul_eq_mul] using he z)⟩
  have hnp : n ≤ p.order := ho ▸ hnc
  refine ⟨fun z => (z-c)^(p.order-n)*g z, by fun_prop, ?_⟩
  intro z
  rw [he,← mul_assoc,← pow_add,Nat.add_sub_of_le hnp]

theorem finite_factor (Z : Finset ℂ) (m : ℂ → ℕ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hm : ∀ c ∈ Z, m c ≤ analyticOrderNatAt f c) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = divisor Z m z*g z := by
  classical
  induction Z using Finset.induction_on generalizing f with
  | empty => exact ⟨f,hf,by simp [divisor]⟩
  | @insert c Z hc ih =>
    obtain ⟨g,hg,he⟩ := single_factor f hf hn c (m c) (hm c (Finset.mem_insert_self _ _))
    have hgn : ∃ z, g z ≠ 0 := by
      obtain ⟨z,hz⟩ := hn
      exact ⟨z,fun h => hz (by rw [he z,h,mul_zero])⟩
    have hmg : ∀ z ∈ Z, m z ≤ analyticOrderNatAt g z := by
      intro z hz
      have hzc : z ≠ c := fun h => hc (h ▸ hz)
      have heq : f = (fun z => (z-c)^(m c))*g := funext he
      have hz0 : analyticOrderAt (fun z : ℂ => (z-c)^(m c)) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero _ (sub_ne_zero.mpr hzc)))
      have ho : analyticOrderAt f z = analyticOrderAt g z := by
        rw [heq,analyticOrderAt_mul (by fun_prop) (hg.analyticAt z),
          hz0,zero_add]
      simpa only [analyticOrderNatAt,ho] using hm z (Finset.mem_insert_of_mem hz)
    obtain ⟨h,hh,heh⟩ := ih g hg hgn hmg
    refine ⟨h,hh,?_⟩
    intro z
    rw [he z,heh z]
    simp only [divisor,Finset.prod_insert hc]
    ring

/-- The removed order is added back exactly, including at removed zeros. -/
theorem order_restore (Z : Finset ℂ) (m : ℂ → ℕ) (f g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (hn : ∃ z, f z ≠ 0)
    (he : ∀ z, f z = divisor Z m z*g z) (s : ℂ) :
    analyticOrderNatAt f s = (if s ∈ Z then m s else 0)+analyticOrderNatAt g s := by
  classical
  have hgn : ∃ z, g z ≠ 0 := by
    obtain ⟨z,hz⟩ := hn
    exact ⟨z,fun h => hz (by rw [he z,h,mul_zero])⟩
  have heq : f = divisor Z m*g := funext he
  rw [heq,analyticOrderNatAt_mul ((divisor_entire Z m).analyticAt s) (hg.analyticAt s)
    (by rw [divisor_order]; split <;> simp) (entire_order_ne_top g hg hgn s)]
  simp only [analyticOrderNatAt,divisor_order]
  split <;> simp

#print axioms divisor_order
#print axioms single_factor
#print axioms finite_factor
#print axioms order_restore
end XiPrime8845.WuFiniteDeflation
