import PRZZDualNativeFreeze

/-! Actual positive-time continuity and finite integration of the native
freezing field. Positivity comes from the original congruence and positive
summation indices, not an integrability or reconstruction premise. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZNativeFreezeTime
open PRZZNativeComponents PRZZRetainedNative
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem row_continuous (L J d : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (M T : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ)
    (hT : 0 < T) (hu : 0 < z.1.1) (hv : 0 < z.1.2) (hs : alpha+beta ≠ 0) :
    ContinuousOn (row .freeze L J F G H M z alpha beta a d) (Icc T (2*T)) := by
  have htc : ContinuousOn (fun t : ℝ => t) (Icc T (2*T)) := continuousOn_id
  have ht0 (t : ℝ) (ht : t ∈ Icc T (2*T)) : 0 < t := hT.trans_le ht.1
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  unfold row
  dsimp only
  split_ifs
  · apply continuousOn_const.mul
    unfold PRZZUnfrozenPoisson.errorSum
    apply continuousOn_finsetSum; intro m hm
    apply continuousOn_finsetSum; intro k hk
    split_ifs with hmk
    · have hm0 : (0:ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hk0 : (0:ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
      have he : (m:ℝ)*z.1.1-(k:ℝ)*z.1.2 = -(z.2.1:ℝ) := by exact_mod_cast hmk
      have hratio : 0 < 1+(z.2.1:ℝ)/((m:ℝ)*z.1.1) := by
        have hp : 0 < (m:ℝ)*z.1.1 := mul_pos hm0 hu0
        rw [show 1+(z.2.1:ℝ)/((m:ℝ)*z.1.1) =
          ((m:ℝ)*z.1.1+(z.2.1:ℝ))/((m:ℝ)*z.1.1) by field_simp]
        exact div_pos (by nlinarith [mul_pos hk0 hv0]) hp
      have hc : ContinuousOn (fun t : ℝ => 2*Real.pi*(m:ℝ)^2*z.1.1/(t*z.1.2)) (Icc T (2*T)) :=
        continuousOn_const.div (htc.mul continuousOn_const) (fun t ht =>
          (mul_pos (ht0 t ht) hv0).ne')
      have hx (t : ℝ) (ht : t ∈ Icc T (2*T)) :
          0 < 2*Real.pi*(m:ℝ)^2*z.1.1/(t*z.1.2) := by
        have := ht0 t ht
        positivity
      have hw := PRZZSourceWOuter.sourceW_continuous (alpha+beta) hs
      have hw1 := hw.comp (hc.mul continuousOn_const) (fun t ht => mul_pos (hx t ht) hratio)
      have hw0 := hw.comp hc (fun t ht => hx t ht)
      unfold PRZZUnfrozenPoisson.errorTerm PRZZAmplitudeFreeze.error
      apply continuousOn_const.mul
      exact ((continuousOn_const.mul hw1).mul
        ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (htc.mul continuousOn_const))).cexp)).sub
        (hw0.mul ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (htc.mul continuousOn_const))).cexp))
    · exact continuousOn_const
  · exact continuousOn_const

def rows (L J N : ℕ) (F G H phi : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (T : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if delta ≠ 0 ∧ R s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
          ∫ t in Icc T (2*T), phi t*row .freeze L J (PRZZWRowLimit.profile F) G H
            ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t else 0 else 0

theorem selected_continuous (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (T : ℝ)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) :
    ContinuousOn (selectedPart .freeze L J N F G H a R alpha beta) (Icc T (2*T)) := by
  change ContinuousOn (fun t => selectedPart .freeze L J N F G H a R alpha beta t) _
  simp_rw [selected_reindex]
  apply continuousOn_finsetSum; intro s hss
  apply continuousOn_finsetSum; intro d hd
  apply continuousOn_finsetSum; intro u hu
  apply continuousOn_finsetSum; intro v hv
  split_ifs
  · apply continuousOn_finsetSum; intro delta hdel
    split_ifs
    · exact row_continuous L J d _ G H a _ T _ alpha beta hT
        (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs
    · exact continuousOn_const
  · exact continuousOn_const

theorem selected_time (L J N : ℕ) (F G H phi : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (T : ℝ)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hphi : ContinuousOn phi (Icc T (2*T))) :
    (∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N F G H a R alpha beta t) =
      rows L J N F G H phi a R alpha beta T := by
  have hi (d u v s : ℕ) (delta : ℤ) (hu : u ∈ Finset.Icc 1 N) (hv : v ∈ Finset.Icc 1 N) :
      IntegrableOn (fun t => phi t*row .freeze L J (PRZZWRowLimit.profile F) G H
        ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t) (Icc T (2*T)) :=
    (hphi.mul (row_continuous L J d (PRZZWRowLimit.profile F) G H a ((2:ℝ)^s) T
      ((u,v),(-delta,1)) alpha beta hT
      (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs)).integrableOn_compact isCompact_Icc
  simp_rw [selected_reindex]
  unfold rows
  simp only [mul_sum,mul_ite,mul_zero]
  rw [integral_finsetSum]
  · apply sum_congr rfl; intro s hss
    rw [integral_finsetSum]
    · apply sum_congr rfl; intro d hd
      rw [integral_finsetSum]
      · apply sum_congr rfl; intro u hu
        rw [integral_finsetSum]
        · apply sum_congr rfl; intro v hv
          split_ifs
          · rw [integral_finsetSum]
            · apply sum_congr rfl; intro delta hdel
              split_ifs <;> simp
            · intro delta hdel; split_ifs
              · exact hi d u v s delta hu hv
              · exact integrable_zero _ _ _
          · simp
        · intro v hv; split_ifs
          · apply integrable_finsetSum; intro delta hdel; split_ifs
            · exact hi d u v s delta hu hv
            · exact integrable_zero _ _ _
          · exact integrable_zero _ _ _
      · intro u hu; apply integrable_finsetSum; intro v hv; split_ifs
        · apply integrable_finsetSum; intro delta hdel; split_ifs
          · exact hi d u v s delta hu hv
          · exact integrable_zero _ _ _
        · exact integrable_zero _ _ _
    · intro d hd; apply integrable_finsetSum; intro u hu
      apply integrable_finsetSum; intro v hv; split_ifs
      · apply integrable_finsetSum; intro delta hdel; split_ifs
        · exact hi d u v s delta hu hv
        · exact integrable_zero _ _ _
      · exact integrable_zero _ _ _
  · intro s hss; apply integrable_finsetSum; intro d hd
    apply integrable_finsetSum; intro u hu
    apply integrable_finsetSum; intro v hv; split_ifs
    · apply integrable_finsetSum; intro delta hdel; split_ifs
      · exact hi d u v s delta hu hv
      · exact integrable_zero _ _ _
    · exact integrable_zero _ _ _

theorem retained_charge (L J N : ℕ) (F G H phi : ℝ → ℂ) (js : List ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Icc T (2*T))) :
    ‖∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N F
      (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t‖ ≤
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile F) G H phi js
        T 1 Q V eps alpha beta := by
  rw [selected_time L J N F _ _ phi _ _ alpha beta T hT hs hphi]
  unfold rows PRZZNativeFreezeEnvelope.charge
  rw [sum_comm (s := Icc 1 N)]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hss
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro delta hdel
    have hg : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
    have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have he : (¬PRZZSourceMaskFamily.discarded T Q eps s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)) ↔
        |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
      simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le]
      rw [lt_div_iff₀ hd0]
      simp only [mul_comm]
    have hn : delta ≠ 0 ↔ 0 < |(delta:ℝ)| := by
      rw [abs_pos]; exact_mod_cast Iff.rfl
    simp only [he,hn,mul_one]
    split_ifs <;> simp
  · simp [had]

#print axioms retained_charge
#print axioms row_continuous
#print axioms selected_continuous
#print axioms selected_time
end XiPrime8845.PRZZNativeFreezeTime
