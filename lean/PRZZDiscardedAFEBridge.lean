import PRZZSourceMaskFamily

/-! Reconstruct the exact AFE term from its time-zero arithmetic
coefficient and logarithmic phase. This is not the linearized phase.
Finite successor indices preserve both original sharp AFE cutoffs. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set MeasureTheory
namespace XiPrime8845.PRZZDiscardedAFEBridge
open PRZZAFEIndices PRZZUnfrozenPoisson PRZZMellinSeparation PRZZPowerJets
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem term_phase (a : ℕ → ℂ) (alpha beta : ℂ) (V : ℕ → ℝ → ℂ)
    (t : ℝ) (m k n r : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    PRZZL1Finite.term a a alpha beta V t m k n r =
      PRZZActualLocalReplacement.coefficient a a alpha beta 0 ((m,k),(n,r))*
        (exp (I*((t*Real.log (((k:ℝ)*r)/((m:ℝ)*n)):ℝ):ℂ))*V (m*k) t) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have invpow (j : ℕ) (hj : 0 < j) (w : ℂ) : ((j:ℂ)^w)⁻¹ = power w (j:ℝ) := by
    simpa only [Complex.ofReal_natCast] using power_inv_cpow w (j:ℝ) (by exact_mod_cast hj)
  have he := positive_weight_identity 1 m k n r t alpha beta
    (by norm_num) hmR hkR hnR hrR
  simp only [one_mul] at he
  have hone : power 1 1 = 1 := by simp [power]
  rw [hone,one_mul] at he
  have hex (u : ℝ) (W : ℕ → ℝ → ℂ) :
      PRZZL1Finite.term a a alpha beta W u m k n r =
        (a n*star (a r))*W (m*k) u*
          (power ((1/2:ℂ)+alpha+(u:ℂ)*I) m*
            power ((1/2:ℂ)+beta-(u:ℂ)*I) k*
            power ((1/2:ℂ)+(u:ℂ)*I) n*power ((1/2:ℂ)-(u:ℂ)*I) r) := by
    unfold PRZZL1Finite.term PRZZL1Finite.directTerm
    simp only [div_eq_mul_inv,mul_inv_rev]
    rw [invpow m hm,invpow k hk,invpow n hn,invpow r hr]
    simp only [star_mul,star_power]
    simp [sub_eq_add_neg,map_ofNat,add_comm,add_left_comm,add_assoc] <;> ring
  rw [hex t V]
  unfold PRZZActualLocalReplacement.coefficient
  rw [hex 0 (fun _ _ => 1),he]
  simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_zero,mul_one]
  ring

/-- Two successors are an exact bijection, not an enlargement by zero
or an independent replacement of either AFE truncation. -/
theorem successor_sum (L : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ range L, f (m+1)) = ∑ m ∈ Icc 1 L, f m := by
  apply sum_bij (fun m _ => m+1)
  · intro m hm; exact mem_Icc.mpr ⟨by omega,by have := mem_range.mp hm; omega⟩
  · intro m hm k hk h; omega
  · intro m hm
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hm
    exact ⟨m-1,mem_range.mpr (by omega),by omega⟩
  · intro m hm; rfl

/-- Original pair order is restored after the two finite successor
bijections. No label count or duplicated partition is introduced. -/
theorem four_sum (L N : ℕ) (f : Index → ℂ) :
    (∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      ∑ p ∈ range L ×ˢ range L, f ((p.1+1,p.2+1),(n,r))) =
      ∑ i ∈ indices L N, f i := by
  simp only [sum_product]
  trans ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, ∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L, f ((m,k),(n,r))
  · apply sum_congr rfl; intro n hn
    apply sum_congr rfl; intro r hr
    calc
      _ = ∑ m ∈ range L, ∑ k ∈ Icc 1 L, f ((m+1,k),(n,r)) := by
        apply sum_congr rfl; intro m hm
        exact successor_sum L (fun k => f ((m+1,k),(n,r)))
      _ = _ := successor_sum L (fun m => ∑ k ∈ Icc 1 L, f ((m,k),(n,r)))
  · simp only [indices,sum_product]
    simp_rw [sum_comm (s := Icc 1 N) (t := Icc 1 L)]

theorem integrand_original (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ)
    (K n r : ℕ) (T M Q V eps : ℝ) (alpha beta : ℂ) (s : Finset (ℕ × ℕ)) (t : ℝ)
    (hn : 0 < n) (hr : 0 < r) :
    PRZZDualDiscardedIBP.integrand F G H P js K n r T M Q V 1 eps alpha beta s t =
      (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        ∑ p ∈ s, ((scaledCutoff G Q n*scaledCutoff H V r)*
          PRZZDiscardedOuter.sourceMask P (scaledCutoff G Q) K T M Q 1 eps n r p)*
            PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
              (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
              (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t (p.1+1) (p.2+1) n r := by
  unfold PRZZDualDiscardedIBP.integrand
  rw [mul_sum]
  apply sum_congr rfl; intro p hp
  rw [term_phase _ (-beta) (-alpha) _ t (p.1+1) (p.2+1) n r (by omega) (by omega) hn hr,
    PRZZWRowReindex.weight_eq]
  unfold PRZZDualDiscardedIBP.coefficient PRZZDualTimeIBP.weight
    PRZZTimeAmplitude.amplitude PRZZTimeJets.reciprocal
  simp only [Nat.cast_add,Nat.cast_one,one_mul,Nat.cast_mul]
  rw [show -beta+-alpha = -(alpha+beta) by ring]
  ring

/-- Pointwise identification of the *previous* IBP integrand, including
its true dual Gamma factor and time cutoff, with the original masked
AFE sum. The two sharp AFE cutoffs are unchanged. -/
theorem outer_integrand (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    (∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      PRZZDualDiscardedIBP.integrand F G H P js (L+2) n r
        T 1 Q V 1 eps alpha beta (range L ×ˢ range L) t) =
      (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        PRZZSourceMaskFamily.masked L N P (scaledCutoff G Q) (scaledCutoff H V)
          (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) T Q eps (-beta) (-alpha) t := by
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (r : ℕ) (hr : r ∈ Finset.Icc 1 N) :=
    integrand_original F G H P js (L+2) n r T 1 Q V eps alpha beta
      (range L ×ˢ range L) t (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hr).1
  calc
    _ = (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, ∑ p ∈ range L ×ˢ range L,
          ((scaledCutoff G Q n*scaledCutoff H V r)*
            PRZZDiscardedOuter.sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps n r p)*
              PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
                (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
                (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t (p.1+1) (p.2+1) n r := by
      simp only [mul_sum]
      apply sum_congr rfl; intro n hn
      apply sum_congr rfl; intro r hr
      simpa only [mul_sum] using he n hn r hr
    _ = _ := by
      unfold PRZZSourceMaskFamily.masked
      congr 1
      have h := four_sum L N (fun i =>
        ((scaledCutoff G Q i.2.1*scaledCutoff H V i.2.2)*
          PRZZDiscardedOuter.sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps
            i.2.1 i.2.2 (i.1.1-1,i.1.2-1))*
          PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
            (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
            (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t i.1.1 i.1.2 i.2.1 i.2.2)
      simpa only [Nat.add_sub_cancel,Prod.mk.eta] using h

/-- The already estimated IBP family is now exactly the matching part
of the original resolved family, under the full real time integral. The
support of the fixed time cutoff supplies positivity; no Fubini or
reconstruction equality is assumed. -/
theorem outer_family (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) :
    PRZZDualDiscardedIBP.outerValue F G H P js N (L+2) T 1 Q V 1 eps alpha beta
      (fun _ _ => range L ×ˢ range L) =
      ∫ t : ℝ, (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
          (scaledCutoff G Q) (scaledCutoff H V)
          (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
          (PRZZSourceMaskFamily.discarded T Q eps) (-beta) (-alpha) t := by
  unfold PRZZDualDiscardedIBP.outerValue
  apply integral_congr_ae
  apply Filter.Eventually.of_forall; intro t
  dsimp only
  rw [outer_integrand]
  by_cases hf : scaledCutoff F T t = 0
  · simp only [hf,zero_mul]
  · have hx : F (T⁻¹*t) ≠ 0 := hf
    have hp := (hF hx).1
    have ht : 0 < t := by
      have he : T*(T⁻¹*t) = t := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hp hT.le]
    rw [PRZZSourceMaskFamily.masked_family L J N P _ _ hP hlo hhi _ T Q eps hT hQ
      (-beta) (-alpha) (by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hab)
      t ht]

#print axioms integrand_original
#print axioms outer_integrand
#print axioms outer_family
#print axioms term_phase
#print axioms successor_sum
#print axioms four_sum
end XiPrime8845.PRZZDiscardedAFEBridge
