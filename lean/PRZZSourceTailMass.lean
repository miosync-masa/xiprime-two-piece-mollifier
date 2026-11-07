import PRZZTransformedSourceBudget
import PRZZSourceRows
import PRZZOptimalOuter

/-! Actual paired tails with the d-dilated arithmetic coefficients and
dual Gamma multiplier. Constants precede height. The finite dyadic pair
family is explicit; outer Delta/d/dyadic summations are not hidden here. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Filter
namespace XiPrime8845.PRZZSourceTailMass
set_option maxHeartbeats 3000000

def coeff (F G : ℝ → ℂ) (js : List ℕ) (d : ℕ) (Q R T t : ℝ)
    (alpha beta : ℂ) (p : ℕ × ℕ) : ℂ :=
  ((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*
    star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
    (F (Q⁻¹*((d:ℝ)*p.1))*G (R⁻¹*((d:ℝ)*p.2)))*
    PRZZAFEDual.dualMultiplier (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) t /
      ((p.1:ℂ)*(p.2:ℂ))

def tail (F : ℝ → ℂ) (M T eH t : ℝ) (alpha beta : ℂ)
    (delta : ℤ) (h : ℕ) (residue : ℝ) (p : ℕ × ℕ) : ℂ :=
  ∑' j, PRZZFrozenTail.pair F M p.2 residue (p,(delta,h))
    (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    ⌈PRZZSourceCutoffs.poissonCutoff 1 T M ((p.2:ℝ)^2) eH⌉₊ j t

/-- The retained original cutoff pairs supply the left scale and positive
indices. A positive lattice witness supplies the lower M bound. -/
theorem retained_support (N d j l m : ℕ) (T M Q : ℝ)
    (F G FM : ℝ → ℂ) (p : ℕ × ℕ)
    (hNT : (N:ℝ) ≤ T) (hm : 1 ≤ m) (hfm : FM m ≠ 0)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsF : Function.support F ⊆ Icc (Q/2) (3*Q))
    (hp : p ∈ PRZZSourceRows.rows N d j l F G) :
    1 ≤ 3*M ∧ 0 < p.1 ∧ 0 < p.2 ∧ (p.2:ℝ) ≤ T ∧ Q/2 ≤ (d:ℝ)*p.1 := by
  classical
  have hh := Finset.mem_filter.mp hp
  have hc := Finset.mem_product.mp hh.1
  have hu := Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N j p.1).mp hc.1).1
  have hv := Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N l p.2).mp hc.2).1
  exact ⟨PRZZExtendedTailDomain.nonempty_scale FM M m hsM hm hfm,
    by omega,by omega,(by exact_mod_cast hv.2 : (p.2:ℝ) ≤ N).trans hNT,
    (hsF hh.2.2.2.2.1).1⟩

/-- No coefficient-mass or Fourier-tail estimate is assumed. Logarithms
from the actual arithmetic degree are absorbed by spending one height power. -/
theorem summed (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH A : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N d j l : ℕ) (M Q R Q1 t : ℝ) (alpha beta : ℂ)
        (delta : ℤ) (h : ℕ) (residue : (ℕ × ℕ) → ℝ) (s : Finset (ℕ × ℕ)),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ 3*M → M ≤ T^b → 0 < Q1 →
      t ∈ Icc T (2*T) → ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ →
      s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N ∧ Q1/2 ≤ (d:ℝ)*p.1) →
      |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      ‖∑ p ∈ s, coeff F G js d Q R T t alpha beta p *
        tail W M T eH t alpha beta delta h (residue p) p‖ ≤ K*T^(-A) := by
  obtain ⟨Ct,hCt,htail⟩ := PRZZTransformedSourceBudget.actual_tail_absorbed W hW hsW
    a b S r eD eH (A+1) ha hb hS hr heD he
  obtain ⟨Cc,hCc,hmass⟩ := PRZZDualError.dual_dilated_pair_mass F G hF hG hsF hsG S hS
  obtain ⟨Cl,hCl,hlog⟩ := PRZZOptimalOuter.power_log_absorbed
    (2*PRZZGCoefficient.degree js) (-(A+1)) (-A) (by linarith)
  refine ⟨Cc*Ct*Cl+1,by positivity,?_⟩
  filter_upwards [hmass,eventually_ge_atTop (36:ℝ),
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))] with T hmass hT hL
  intro N d j l M Q R Q1 t alpha beta delta h residue s hN hd hNT hM hMT hQ ht
    halpha hbeta hsep hbox hlen hdelta
  have hT0 : 0 < T := by linarith
  have hN0 : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hmass' := hmass alpha beta halpha hbeta js N d j l Q R t s hN hd hNT ht hbox
    (fun p hp => ⟨(hlen p hp).1,(hlen p hp).2.1⟩)
  have hterm : ∀ p ∈ s,
      ‖coeff F G js d Q R T t alpha beta p * tail W M T eH t alpha beta delta h (residue p) p‖ ≤
      ‖coeff F G js d Q R T t alpha beta p *
        Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))‖ * (Ct*T^(-(A+1))) := by
    intro p hp
    have hc := Finset.mem_product.mp (hbox hp)
    have hu := Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N j p.1).mp hc.1).1
    have hv := Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N l p.2).mp hc.2).1
    have hh := htail T M t (residue p) d Q1 (p,(delta,h)) alpha beta hT hL hM hMT
      (Nat.zero_lt_one.trans_le hu.1) (Nat.zero_lt_one.trans_le hv.1)
      ((by exact_mod_cast hv.2 : (p.2:ℝ) ≤ N).trans hNT) ht
      halpha hbeta hsep (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) hQ
      (hlen p hp).2.2 hdelta
    simpa only [tail,norm_mul,mul_assoc] using mul_le_mul_of_nonneg_left hh
      (norm_nonneg (coeff F G js d Q R T t alpha beta p))
  have heq : ∀ p, coeff F G js d Q R T t alpha beta p *
      Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ)) =
      (((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
        (F (Q⁻¹*((d:ℝ)*p.1))*G (R⁻¹*((d:ℝ)*p.2)))*
          (PRZZAFEDual.dualMultiplier (alpha/(Real.log T:ℂ)) (beta/(Real.log T:ℂ)) t *
            Complex.exp (((alpha+beta)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ)))) /
              ((p.1:ℂ)*(p.2:ℂ)) := by intro p; unfold coeff; ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.sum_mul] at hsum
  simp only [heq] at hsum
  simp only [mul_assoc] at hmass' hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_right hmass' (by positivity))
  have hpw := hlog T (by linarith)
  have hlogN : (Real.log N)^(2*PRZZGCoefficient.degree js) ≤
      (Real.log T)^(2*PRZZGCoefficient.degree js) := by
    gcongr
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlogN hCc) (by positivity))
  have hh := mul_le_mul_of_nonneg_left hpw (show 0 ≤ Cc*Ct by positivity)
  have hz : 0 ≤ T^(-A) := by positivity
  nlinarith only [hbound',hh,hz]

/-- The already estimated literal arithmetic tail under a continuous time
weight. No time-independent replacement for the dual multiplier is made. -/
theorem integrated (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH A : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N d j l : ℕ) (M Q R Q1 : ℝ) (alpha beta : ℂ)
        (delta : ℤ) (h : ℕ) (residue : (ℕ × ℕ) → ℝ) (s : Finset (ℕ × ℕ)) (w : ℝ → ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 1 ≤ 3*M → M ≤ T^b → 0 < Q1 →
      ‖alpha‖ ≤ S → ‖beta‖ ≤ S → r ≤ ‖alpha+beta‖ → Continuous w →
      s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N ∧ Q1/2 ≤ (d:ℝ)*p.1) →
      |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      ‖∫ t in Icc T (2*T), w t * ∑ p ∈ s, coeff F G js d Q R T t alpha beta p *
        tail W M T eH t alpha beta delta h (residue p) p‖ ≤
        K*T^(-A)*(∫ t in Icc T (2*T), ‖w t‖) := by
  obtain ⟨K,hK,h⟩ := summed F G W hF hG hsF hsG hW hsW js a b S r eD eH A
    ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with T hT
  intro N d j l M Q R Q1 alpha beta delta h residue s w hN hd hNT hM hMT hQ
    halpha hbeta hsep hw hbox hlen hdelta
  have hcont : Continuous (fun t => K*T^(-A)*‖w t‖) := continuous_const.mul hw.norm
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    hcont.integrableOn_Icc ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (hT N d j l M Q R Q1 t alpha beta delta h residue s hN hd hNT hM hMT hQ ht
        halpha hbeta hsep hbox hlen hdelta) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The domain needed by `integrated` is supplied for the complete retained
pair family, including a genuine positive pre-Poisson lattice witness. -/
theorem retained_domain (N d j l m : ℕ) (T M Q : ℝ) (F G FM : ℝ → ℂ)
    (hNT : (N:ℝ) ≤ T) (hm : 1 ≤ m) (hfm : FM m ≠ 0)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsF : Function.support F ⊆ Icc (Q/2) (3*Q)) :
    1 ≤ 3*M ∧
    PRZZSourceRows.rows N d j l F G ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) ∧
    ∀ p ∈ PRZZSourceRows.rows N d j l F G,
      d*p.1 ≤ N ∧ d*p.2 ≤ N ∧ Q/2 ≤ (d:ℝ)*p.1 := by
  classical
  refine ⟨PRZZExtendedTailDomain.nonempty_scale FM M m hsM hm hfm,
    Finset.filter_subset _ _,?_⟩
  intro p hp
  have hh := (Finset.mem_filter.mp hp).2
  exact ⟨hh.1,hh.2.1,
    (retained_support N d j l m T M Q F G FM p hNT hm hfm hsM hsF hp).2.2.2.2⟩

#print axioms retained_domain
#print axioms integrated
#print axioms retained_support
#print axioms summed
end XiPrime8845.PRZZSourceTailMass
