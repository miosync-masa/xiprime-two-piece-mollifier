import PRZZFilteredResidual

/-! The discarded sourceMask sum is the actual original complementary
W sum, with both valued cutoffs and the exact logarithmic phase. The
existing complete-family complement inherits its height-uniform tail
bound. No pointwise bound or decomposition equality is supplied as a
premise. Diagonal main-term evaluation and central space/time Fubini to
literal A* are separate results, not asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex MeasureTheory Finset
namespace XiPrime8845.PRZZLiteralComplement
open PRZZL1Finite PRZZUnfrozenPoisson PRZZPowerJets PRZZAFEIndices
set_option maxHeartbeats 7000000

theorem coefficient_power (a b : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ)
    (m k n r : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    term a b alpha beta (fun _ _ => 1) t m k n r =
      a n*star (b r)*
        (power ((1/2:ℂ)+alpha+t*I) m*power ((1/2:ℂ)+beta-t*I) k*
          power ((1/2:ℂ)+t*I) n*power ((1/2:ℂ)-t*I) r) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hc : star (power ((1/2:ℂ)+t*I) r) = power ((1/2:ℂ)-t*I) r := by
    rw [star_power]
    congr 1
    simp [sub_eq_add_neg]
  unfold term directTerm
  simp only [← Complex.ofReal_natCast m,← Complex.ofReal_natCast k,
    ← Complex.ofReal_natCast n,← Complex.ofReal_natCast r,div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [power_inv_cpow _ _ hm',power_inv_cpow _ _ hk',power_inv_cpow _ _ hn',power_inv_cpow _ _ hr']
  simp
  change (starRingEnd ℂ) (power ((1/2:ℂ)+t*I) r) = _ at hc
  simp at hc
  rw [hc]
  ring

/-- Every original time-dependent denominator contributes to this exact
phase, not merely to a norm bound. -/
theorem coefficient_phase (a b : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ)
    (m k n r : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    term a b alpha beta (fun _ _ => 1) t m k n r =
      term a b alpha beta (fun _ _ => 1) 0 m k n r *
        exp (I*((t*Real.log (((k:ℝ)*r)/((m:ℝ)*n)):ℝ):ℂ)) := by
  rw [coefficient_power a b alpha beta t m k n r hm hk hn hr,
    coefficient_power a b alpha beta 0 m k n r hm hk hn hr]
  have h := positive_weight_identity 1 m k n r t alpha beta (by norm_num)
    (by exact_mod_cast hm) (by exact_mod_cast hk) (by exact_mod_cast hn) (by exact_mod_cast hr)
  simp only [one_mul] at h
  have hp : power (1:ℂ) 1 = 1 := by simp [power]
  rw [hp,one_mul] at h
  simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_zero]
  rw [h]
  ring

theorem term_amplitude (a b : ℕ → ℂ) (alpha beta sigma : ℂ)
    (F : ℝ → ℂ) (T t : ℝ) (m k n r : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    PRZZMellinSeparation.scaledCutoff F T t *
      term a b alpha beta (fun (x : ℕ) (t : ℝ) =>
        PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r =
    PRZZActualLocalReplacement.coefficient a b alpha beta 0 ((m,k),(n,r))*
      exp (I*((t*Real.log (((k:ℝ)*r)/((m:ℝ)*n)):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*((m:ℝ)*k)) sigma t := by
  have he : term a b alpha beta (fun (x : ℕ) (t : ℝ) =>
      PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r =
      PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*((m:ℝ)*k)/t)*
        term a b alpha beta (fun _ _ => 1) t m k n r := by
    simp only [term,directTerm,Nat.cast_mul]
    ring
  rw [he,coefficient_phase a b alpha beta t m k n r hm hk hn hr]
  unfold PRZZActualLocalReplacement.coefficient PRZZTimeAmplitude.amplitude PRZZTimeJets.reciprocal
  ring

/-- The literal complementary pieces in the complete original label
fibres. Equality at the cutoff belongs to the complement. -/
def complementaryIntegral (L N K : ℕ) (P : ℝ → ℝ) (M T Q eps : ℝ)
    (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta sigma : ℂ) : ℂ := by
  classical
  exact ∫ t : ℝ, ∑ j ∈ range K, ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
    (if PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps ≤
        |((i.1.2:ℝ)*i.2.2)-((i.1.1:ℝ)*i.2.1)| then
      PRZZAFEProgression.piece (fun x => (P x:ℂ)) (2^j*M) i.1.1 else 0) *
      (F1 i.2.1*F2 i.2.2*PRZZMellinSeparation.scaledCutoff F T t *
        term a a alpha beta (fun (x : ℕ) (t : ℝ) =>
          PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t))
            t i.1.1 i.1.2 i.2.1 i.2.2)

/-- Every original AFE and mollifier index, both cutoff values, the
spatial partition and time cutoff are present on both sides. -/
theorem complementary_eq_sourceMask (L N K : ℕ) (P : ℝ → ℝ) (M T Q eps : ℝ)
    (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta sigma : ℂ) :
    complementaryIntegral L N K P M T Q eps F F1 F2 a alpha beta sigma =
      ∫ t : ℝ, ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
        PRZZDiscardedOuter.row F T a a alpha beta sigma n r (range L ×ˢ range L)
          (fun p => (F1 n*F2 r)*PRZZDiscardedOuter.sourceMask P F1 K T M Q 1 eps n r p) t := by
  classical
  unfold complementaryIntegral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  unfold PRZZDiscardedOuter.row
  simp only [Finset.sum_product]
  simp_rw [← PRZZAFEIndices.grouped]
  simp only [indices,Finset.sum_product]
  -- Move the original mollifier pair outside the spatial and AFE sums.
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 L) (t := Finset.Icc 1 N)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
  have ha (m k : ℕ) (hm : m ∈ Finset.Icc 1 L) (hk : k ∈ Finset.Icc 1 L) :=
    term_amplitude a a alpha beta sigma F T t m k n r
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hk).1 hn0 hr0
  have he : (∑ j ∈ range K, ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
      (if PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps ≤ |(k:ℝ)*r-(m:ℝ)*n| then
        PRZZAFEProgression.piece (fun x => (P x:ℂ)) (2^j*M) m else 0)*
      (F1 n*F2 r*PRZZMellinSeparation.scaledCutoff F T t*
        term a a alpha beta (fun (x : ℕ) (t : ℝ) =>
          PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r)) =
    ∑ j ∈ range K, ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
      (if PRZZSourceCutoffs.deltaCutoff T (2^j*M) Q eps ≤ |(k:ℝ)*r-(m:ℝ)*n| then
        PRZZAFEProgression.piece (fun x => (P x:ℂ)) (2^j*M) m else 0)*
      (F1 n*F2 r*(PRZZActualLocalReplacement.coefficient a a alpha beta 0 ((m,k),(n,r))*
        exp (I*((t*Real.log (((k:ℝ)*r)/((m:ℝ)*n)):ℝ):ℂ))*
        PRZZTimeAmplitude.amplitude F T (2*Real.pi*((m:ℝ)*k)) sigma t)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro k hk
    rw [show F1 n*F2 r*PRZZMellinSeparation.scaledCutoff F T t*
        term a a alpha beta (fun (x : ℕ) (t : ℝ) =>
          PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r =
        F1 n*F2 r*(PRZZMellinSeparation.scaledCutoff F T t*
          term a a alpha beta (fun (x : ℕ) (t : ℝ) =>
            PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r) by ring,ha m k hm hk]
  rw [he]
  simp_rw [PRZZL1Truncation.positive_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  unfold PRZZDiscardedOuter.sourceMask
  by_cases hf : F1 n = 0
  · simp [hf]
  · simp only [one_mul,div_one,if_neg hf,PRZZDiscardedPartition.mask,
      Nat.cast_add,Nat.cast_one,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The unreduced original gap and reduced label select exactly the same
complement. Positivity excludes the diagonal, including at the boundary. -/
theorem fibre_complement_iff (L N : ℕ) (z : Label) (i : Index)
    (hi : i ∈ fibre L N z) (D : ℝ) (hD : 0 < D) :
    D ≤ |(i.1.2:ℝ)*i.2.2-(i.1.1:ℝ)*i.2.1| ↔
      z.2.1 ≠ 0 ∧ ¬ |(z.2.1:ℝ)| < D/(z.1:ℝ) := by
  have hm := Finset.mem_filter.mp hi
  have hn : 0 < i.2.1 :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hm.1).2).1).1
  have hd : 0 < (z.1:ℝ) := by
    rw [← hm.2]
    exact_mod_cast Nat.gcd_pos_of_pos_left i.2.2 hn
  have he : (i.1.1:ℝ)*i.2.1-(i.1.2:ℝ)*i.2.2 = (z.1:ℝ)*(z.2.1:ℝ) := by
    have h := gap_eq i
    rw [hm.2] at h
    exact_mod_cast h
  rw [abs_sub_comm,he,abs_mul,abs_of_pos hd]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro hz
      simp only [hz,Int.cast_zero,abs_zero,mul_zero] at h
      linarith
    · rw [not_lt,div_le_iff₀ hd]
      nlinarith only [h]
  · rintro ⟨_,h⟩
    rw [not_lt,div_le_iff₀ hd] at h
    nlinarith only [h]

/-- This is the complement of the existing complete W-row partition,
not a newly assumed decomposition. The cutoff is divided by the actual
gcd, and both original cutoff values remain in the coefficients. -/
theorem complete_complement_eq (L N : ℕ) (P : ℝ → ℝ) (T Q eps : ℝ)
    (hT : 0 < T) (hQ : 0 < Q) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) :
    (∫ t : ℝ, PRZZMellinSeparation.scaledCutoff F T t *
      PRZZWRowLimit.complement L N (fun x => (P x:ℂ))
        (fun j z => |(z.2.1:ℝ)| <
          PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ))
        (PRZZWRowReindex.leftCoefficient a F1)
        (PRZZWRowReindex.rightCoefficient a F2) alpha beta t) =
      complementaryIntegral L N (L+2) P 1 T Q eps F F1 F2 a alpha beta (alpha+beta) := by
  classical
  unfold complementaryIntegral PRZZWRowLimit.complement
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [Finset.mul_sum,mul_one]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro z hz
  let f : Index → ℂ := fun i =>
    PRZZAFEProgression.piece (fun x => (P x:ℂ)) (2^j) i.1.1 *
      term (PRZZWRowReindex.leftCoefficient a F1)
        (PRZZWRowReindex.rightCoefficient a F2) alpha beta
        (PRZZActualDirectSum.mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2
  have hrow : PRZZWRowLimit.row L N (fun x => (P x:ℂ)) j z
      (PRZZWRowReindex.leftCoefficient a F1)
      (PRZZWRowReindex.rightCoefficient a F2) alpha beta t =
      ∑ i ∈ fibre L N z, f i := by
    exact (PRZZExplicitDomain.fibre_explicit L N z f).symm
  have hD : 0 < PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps := by
    unfold PRZZSourceCutoffs.deltaCutoff
    positivity
  by_cases hc : z.2.1 ≠ 0 ∧ ¬ |(z.2.1:ℝ)| <
      PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ)
  · rw [if_pos hc,hrow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hg := (fibre_complement_iff L N z i hi _ hD).mpr hc
    simp only [if_pos hg,f,PRZZWRowReindex.term_cutoffs,PRZZWRowReindex.weight_eq]
    ring
  · rw [if_neg hc,mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hg : ¬ PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps ≤
        |(i.1.2:ℝ)*i.2.2-(i.1.1:ℝ)*i.2.1| := by
      simpa only [fibre_complement_iff L N z i hi _ hD] using hc
    simp only [if_neg hg,zero_mul]

/-- The already proved arbitrary-power tail estimate now bounds the
literal complementary family. The constant precedes every truncation and
spatial partition length; no coefficient-mass or geometry premise remains. -/
theorem complementary_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H)
    (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L N K : ℕ) (A B alpha beta : ℂ) (T M Q R : ℝ)
      (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      0 < M → 0 < Q → 1 ≤ T^(1-eps) →
      ‖complementaryIntegral L N K P M T Q eps F
        (PRZZMellinSeparation.scaledCutoff G Q)
        (PRZZMellinSeparation.scaledCutoff H R)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta
        ((A+B)/(Real.log T:ℂ))‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,h⟩ := PRZZFilteredResidual.source_valued_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro L N K A B alpha beta T M Q R P hN hNT hT hlog hsep ha hb
    hP hlo hhi hleft hright hM hQ hheight
  rw [complementary_eq_sourceMask]
  simpa only [PRZZDiscardedOuter.tailError,one_mul] using
    h N K A B alpha beta T M Q R 1 P hN hNT hT hlog hsep ha hb
      hP hlo hhi hleft hright hM hQ (by norm_num) hheight
      (fun _ _ => range L ×ˢ range L)

/-- Direct application to the complement of the complete family, with
the actual logarithmically scaled shifts. This statement retains no
separate sourceMask identity or row-geometry assumption. -/
theorem complete_complement_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H)
    (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L N : ℕ) (A B : ℂ) (T Q R : ℝ) (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+(A/(Real.log T:ℂ)).re → 0 ≤ 1/2+(B/(Real.log T:ℂ)).re →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      0 < Q → 1 ≤ T^(1-eps) →
      ‖∫ t : ℝ, PRZZMellinSeparation.scaledCutoff F T t *
        PRZZWRowLimit.complement L N (fun x => (P x:ℂ))
          (fun j z => |(z.2.1:ℝ)| <
            PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ))
          (PRZZWRowReindex.leftCoefficient
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff G Q))
          (PRZZWRowReindex.rightCoefficient
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff H R))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,h⟩ := complementary_negligible F G H hF hcF hsF hG hH hcG hcH hsG
    js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro L N A B T Q R P hN hNT hT hlog hsep ha hb hP hlo hhi hleft hright hQ hheight
  rw [complete_complement_eq L N P T Q eps (by linarith) hQ]
  simpa only [← add_div] using h L N (L+2) A B (A/(Real.log T:ℂ))
    (B/(Real.log T:ℂ)) T 1 Q R P hN hNT hT hlog hsep ha hb hP hlo hhi
      hleft hright (by norm_num) hQ hheight

#print axioms complete_complement_negligible
#print axioms complementary_negligible
#print axioms fibre_complement_iff
#print axioms complete_complement_eq
#print axioms coefficient_power
#print axioms coefficient_phase
#print axioms term_amplitude
#print axioms complementary_eq_sourceMask
end XiPrime8845.PRZZLiteralComplement
