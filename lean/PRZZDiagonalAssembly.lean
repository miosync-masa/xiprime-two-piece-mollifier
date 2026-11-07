import PRZZLiteralComplement
import PRZZDiagonalContour

/-! Original diagonal arithmetic coefficients and their primitive series.
Cutoff values and sharp AFE bounds are retained before passing to a limit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Finset Filter Topology
namespace XiPrime8845.PRZZDiagonalAssembly
open PRZZL1Finite PRZZPowerJets PRZZDyadicEnvelope
set_option maxHeartbeats 6000000

def coefficient (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (d u v : ℕ) : ℂ :=
  F1 (d*u)*F2 (d*v)*a (d*u)*star (a (d*v))*
    power 1 d*power (1+beta) u*power (1+alpha) v

theorem coefficient_eq (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (d u v : ℕ)
    (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    coefficient a F1 F2 alpha beta d u v =
      F1 (d*u)*F2 (d*v)*a (d*u)*star (a (d*v))/
        ((d:ℂ)*(u:ℂ)^(1+beta)*(v:ℂ)^(1+alpha)) := by
  unfold coefficient
  rw [← PRZZUnfrozenPoisson.power_inv_cpow _ _ (by exact_mod_cast hd),
    ← PRZZUnfrozenPoisson.power_inv_cpow _ _ (by exact_mod_cast hu),
    ← PRZZUnfrozenPoisson.power_inv_cpow _ _ (by exact_mod_cast hv)]
  simp only [Complex.cpow_one,Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

theorem primitive_power (d u v ell : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hv : 0 < v) (he : 0 < ell) (alpha beta : ℂ) :
    power ((1/2:ℂ)+alpha) (v*ell)*power ((1/2:ℂ)+beta) (u*ell)*
      power (1/2) (d*u)*power (1/2) (d*v) =
      power 1 d*power (1+beta) u*power (1+alpha) v*power (1+alpha+beta) ell := by
  simp only [power,Real.log_mul hv.ne' he.ne',Real.log_mul hu.ne' he.ne',
    Real.log_mul hd.ne' hu.ne',Real.log_mul hd.ne' hv.ne',Complex.ofReal_add,← Complex.exp_add]
  congr 1
  ring

/-- Exact original AFE term on the primitive diagonal. The time phase
cancels as a complex number; no modulus-only identification is used. -/
theorem primitive_term (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v ell : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (he : 0 < ell)
    (t : ℝ) (ht : 0 < t) :
    F1 (d*u)*F2 (d*v)*term a a alpha beta
      (PRZZActualDirectSum.mainWeight alpha beta) t (v*ell) (u*ell) (d*u) (d*v) =
      coefficient a F1 F2 alpha beta d u v *
        (sourceW (alpha+beta) ((ell:ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v))) /
          (ell:ℂ)^(1+alpha+beta)) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have huR : (0:ℝ) < u := by exact_mod_cast hu
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have heR : (0:ℝ) < ell := by exact_mod_cast he
  have hp : (((u*ell:ℕ):ℝ)*((d*v:ℕ):ℝ))/(((v*ell:ℕ):ℝ)*((d*u:ℕ):ℝ)) = 1 := by
    push_cast
    field_simp
  have hc := PRZZLiteralComplement.coefficient_phase a a alpha beta t
    (v*ell) (u*ell) (d*u) (d*v) (Nat.mul_pos hv he) (Nat.mul_pos hu he)
      (Nat.mul_pos hd hu) (Nat.mul_pos hd hv)
  rw [hp,Real.log_one,mul_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one] at hc
  have hk : term a a alpha beta (PRZZActualDirectSum.mainWeight alpha beta) t
      (v*ell) (u*ell) (d*u) (d*v) =
      sourceW (alpha+beta) ((ell:ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v))) *
        term a a alpha beta (fun _ _ => 1) t (v*ell) (u*ell) (d*u) (d*v) := by
    rw [PRZZWRowReindex.weight_eq]
    have harg : 2*Real.pi*((v*ell*(u*ell):ℕ):ℝ)/t =
        (ell:ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v)) := by
      push_cast
      field_simp
    simp only [term,directTerm,harg]
    ring
  rw [hk,hc,PRZZLiteralComplement.coefficient_power a a alpha beta 0
    (v*ell) (u*ell) (d*u) (d*v) (Nat.mul_pos hv he) (Nat.mul_pos hu he)
      (Nat.mul_pos hd hu) (Nat.mul_pos hd hv)]
  simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_zero,Nat.cast_mul]
  rw [primitive_power d u v ell hdR huR hvR heR alpha beta]
  rw [← PRZZUnfrozenPoisson.power_inv_cpow _ _ heR]
  simp only [Complex.ofReal_natCast,coefficient,div_eq_mul_inv]
  ring

/-- The coprime diagonal has one and only one positive primitive index. -/
theorem primitive_index (u v m k : ℕ) (_hu : 0 < u) (hv : 0 < v)
    (hc : Nat.Coprime u v) (hm : 0 < m) (he : m*u = k*v) :
    ∃ ell : ℕ, 0 < ell ∧ m = v*ell ∧ k = u*ell := by
  have hd : v ∣ m := hc.symm.dvd_mul_right.mp (by rw [he]; exact dvd_mul_left v k)
  obtain ⟨ell,hmul⟩ := hd
  have he0 : 0 < ell := by nlinarith
  refine ⟨ell,he0,hmul,?_⟩
  rw [hmul] at he
  apply mul_right_cancel₀ hv.ne'
  nlinarith [he]

/-- No sharp AFE index is enlarged or counted twice in the primitive
finite reindexing. -/
theorem finite_diagonal (L u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hc : Nat.Coprime u v) (f : ℕ → ℕ → ℂ) :
    (∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L, if m*u = k*v then f m k else 0) =
      ∑ ell ∈ Icc 1 L, if v*ell ≤ L ∧ u*ell ≤ L then f (v*ell) (u*ell) else 0 := by
  classical
  let s := ((Finset.Icc 1 L) ×ˢ (Finset.Icc 1 L)).filter (fun p : ℕ × ℕ => p.1*u = p.2*v)
  let q := (Finset.Icc 1 L).filter (fun ell => v*ell ≤ L ∧ u*ell ≤ L)
  have hh : (∑ p ∈ s, f p.1 p.2) = ∑ ell ∈ q, f (v*ell) (u*ell) := by
    symm
    apply Finset.sum_bij (fun ell _ => (v*ell,u*ell))
    · intro ell hel
      obtain ⟨hel,hvL,huL⟩ := Finset.mem_filter.mp hel
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith [(mem_Icc.mp hel).1],hvL⟩,
        Finset.mem_Icc.mpr ⟨by nlinarith [(mem_Icc.mp hel).1],huL⟩⟩,by ring⟩
    · intro ell hel ell' hel' heq
      have hh := congrArg Prod.fst heq
      exact mul_left_cancel₀ hv.ne' hh
    · intro p hp
      obtain ⟨hp,heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hm,hk⟩ := Finset.mem_product.mp hp
      obtain ⟨ell,he,hmul,hkul⟩ := primitive_index u v p.1 p.2 hu hv hc (mem_Icc.mp hm).1 heq
      refine ⟨ell,?_,Prod.ext hmul.symm hkul.symm⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨he,?_⟩,?_,?_⟩
      · nlinarith [(mem_Icc.mp hm).2]
      · simpa [← hmul] using (mem_Icc.mp hm).2
      · simpa [← hkul] using (mem_Icc.mp hk).2
    · intro ell hel; rfl
  simpa only [s,q,Finset.sum_filter,Finset.sum_product] using hh

def primitiveCutoff (L u v : ℕ) : Finset ℕ :=
  (range L).filter (fun n => v*(n+1) ≤ L ∧ u*(n+1) ≤ L)

theorem primitiveCutoff_tendsto (u v : ℕ) :
    Tendsto (fun L => primitiveCutoff L u v) atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro L K hLK n hn
    obtain ⟨hn,hv,hu⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hn).trans_le hLK),hv.trans hLK,hu.trans hLK⟩
  · intro n
    refine ⟨max (n+1) (max (v*(n+1)) (u*(n+1))),?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      exact (Nat.lt_succ_self n).trans_le (le_max_left _ _)
    · exact ⟨(le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩

theorem scalar_bound (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (X : ℝ) (hX : 0 < X) (ell : ℕ) (he : 0 < ell) :
    ‖sourceW sigma ((ell:ℝ)^2/X)/(ell:ℂ)^(1+sigma)‖ ≤
      PRZZWArithmeticCutoff.decayConstant sigma*X^2/(ell:ℝ)^4 := by
  have heR : (0:ℝ) < ell := by exact_mod_cast he
  have hn : 1 ≤ ‖(ell:ℂ)^(1+sigma)‖ := by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos heR]
    apply Real.one_le_rpow (by exact_mod_cast he)
    simp; linarith
  have hw := PRZZSourceDecay.sourceW_decay sigma hs 2 ((ell:ℝ)^2/X) (by norm_num) (by positivity)
  change _ ≤ PRZZWArithmeticCutoff.decayConstant sigma*((ell:ℝ)^2/X)^(-(2:ℝ)) at hw
  have hp : ((ell:ℝ)^2/X)^(-(2:ℝ)) = X^2/(ell:ℝ)^4 := by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    field_simp
  rw [hp] at hw
  rw [norm_div]
  exact (div_le_self (norm_nonneg _) hn).trans (hw.trans_eq (by ring))

theorem scalar_summable (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun n : ℕ => sourceW sigma (((n+1:ℕ):ℝ)^2/X)/((n+1:ℕ):ℂ)^(1+sigma)) := by
  have hp : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)^4) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
  apply Summable.of_norm
  apply (hp.mul_left (PRZZWArithmeticCutoff.decayConstant sigma*X^2)).of_nonneg_of_le
  · intro n; exact norm_nonneg _
  · intro n
    simpa only [div_eq_mul_inv,one_mul] using scalar_bound sigma hs hr X hX (n+1) (by omega)

/-- The sharp original AFE rectangle tends to the primitive scalar
diagonal multiplied by the exact original coefficient. -/
theorem pair_cutoff_removed (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v)
    (hs : alpha+beta ≠ 0) (hr : -1 ≤ (alpha+beta).re) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun L : ℕ => ∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L,
      if m*u = k*v then F1 (d*u)*F2 (d*v)*term a a alpha beta
        (PRZZActualDirectSum.mainWeight alpha beta) t m k (d*u) (d*v) else 0)
      atTop (𝓝 (coefficient a F1 F2 alpha beta d u v *
        PRZZDiagonalMellin.diagonal (alpha+beta) (t/(2*Real.pi*(u:ℝ)*v)))) := by
  have hX : 0 < t/(2*Real.pi*(u:ℝ)*v) := by positivity
  have hi := (scalar_summable (alpha+beta) hs hr _ hX).hasSum.comp (primitiveCutoff_tendsto u v)
  have he (L : ℕ) : (∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L,
      if m*u = k*v then F1 (d*u)*F2 (d*v)*term a a alpha beta
        (PRZZActualDirectSum.mainWeight alpha beta) t m k (d*u) (d*v) else 0) =
      coefficient a F1 F2 alpha beta d u v *
        ∑ n ∈ primitiveCutoff L u v,
          sourceW (alpha+beta) (((n+1:ℕ):ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v)))/
            ((n+1:ℕ):ℂ)^(1+(alpha+beta)) := by
    rw [finite_diagonal L u v hu hv hc]
    have hh : (∑ ell ∈ Icc 1 L,
        if v*ell ≤ L ∧ u*ell ≤ L then F1 (d*u)*F2 (d*v)*term a a alpha beta
          (PRZZActualDirectSum.mainWeight alpha beta) t (v*ell) (u*ell) (d*u) (d*v) else 0) =
        ∑ ell ∈ Icc 1 L, if v*ell ≤ L ∧ u*ell ≤ L then
          coefficient a F1 F2 alpha beta d u v *
            (sourceW (alpha+beta) ((ell:ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v)))/
              (ell:ℂ)^(1+(alpha+beta))) else 0 := by
      apply Finset.sum_congr rfl
      intro ell hell
      split_ifs
      · simpa only [add_assoc] using primitive_term a F1 F2 alpha beta d u v ell hd hu hv (mem_Icc.mp hell).1 t ht
      · rfl
    rw [hh,PRZZL1Truncation.positive_sum]
    simp only [primitiveCutoff,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  simp_rw [he]
  exact hi.const_mul _

def scalarTerm (sigma : ℂ) (u v : ℕ) (n : ℕ) (t : ℝ) : ℂ :=
  sourceW sigma (((n+1:ℕ):ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v)))/((n+1:ℕ):ℂ)^(1+sigma)

def scalarCap (sigma : ℂ) (T : ℝ) (u v : ℕ) : ℝ :=
  PRZZWArithmeticCutoff.decayConstant sigma*(2*T/(2*Real.pi*(u:ℝ)*v))^2

theorem scalar_time_bound (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (T : ℝ) (hT : 0 < T) (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) :
    ‖scalarTerm sigma u v n t‖ ≤ scalarCap sigma T u v*(1/((n+1:ℕ):ℝ)^4) := by
  have ht0 : 0 < t := hT.trans_le ht.1
  have hh := scalar_bound sigma hs hr (t/(2*Real.pi*(u:ℝ)*v)) (by positivity) (n+1) (by omega)
  apply hh.trans
  change _ ≤ PRZZWArithmeticCutoff.decayConstant sigma*(2*T/(2*Real.pi*(u:ℝ)*v))^2*
    (1/((n+1:ℕ):ℝ)^4)
  have hc : 0 ≤ PRZZWArithmeticCutoff.decayConstant sigma := by
    unfold PRZZWArithmeticCutoff.decayConstant
    positivity
  simp only [mul_one_div]
  gcongr
  exact ht.2

theorem scalar_time_continuous (sigma : ℂ) (hs : sigma ≠ 0) (T : ℝ) (hT : 0 < T)
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (n : ℕ) :
    ContinuousOn (scalarTerm sigma u v n) (Set.Icc T (2*T)) := by
  unfold scalarTerm
  apply ContinuousOn.div_const
  apply (PRZZSourceWOuter.sourceW_continuous sigma hs).comp
  · fun_prop (disch := intro t ht; have ht0 : 0 < t := hT.trans_le ht.1; positivity)
  · intro t ht
    have ht0 : 0 < t := hT.trans_le ht.1
    change (0:ℝ) < ((n+1:ℕ):ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v))
    positivity

theorem diagonal_time_continuous (sigma : ℂ) (hs : sigma ≠ 0) (hr : -1 ≤ sigma.re)
    (T : ℝ) (hT : 0 < T) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (fun t : ℝ => PRZZDiagonalMellin.diagonal sigma
      (t/(2*Real.pi*(u:ℝ)*v))) (Set.Icc T (2*T)) := by
  have hp : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)^4) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
  exact continuousOn_tsum (fun n => scalar_time_continuous sigma hs T hT u v hu hv n)
    (hp.mul_left (scalarCap sigma T u v))
    (fun n t ht => scalar_time_bound sigma hs hr T hT u v hu hv n t ht)

def admissible (N d u v : ℕ) : Prop := Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N

def assembled (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then coefficient a F1 F2 alpha beta d u v *
      PRZZDiagonalMellin.diagonal (alpha+beta) (t/(2*Real.pi*(u:ℝ)*v)) else 0

def main (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) : ℂ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then coefficient a F1 F2 alpha beta d u v *
      riemannZeta (1+(alpha+beta)) else 0

def errorMass (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ) : ℝ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then ‖coefficient a F1 F2 alpha beta d u v‖*
      (T/(2*Real.pi*(u:ℝ)*v))^(-(1/8:ℝ)) else 0

/-- The pointwise bound uses the actual finite weighted coefficient mass,
not a supplied cap or a count of rows. -/
theorem assembled_error : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (T t : ℝ),
    alpha+beta ≠ 0 → ‖alpha+beta‖ ≤ 1/8 → 0 < T → T ≤ t →
    ‖assembled N a F1 F2 alpha beta t-main N a F1 F2 alpha beta‖ ≤
      C*(1+16/‖alpha+beta‖^2)*errorMass N a F1 F2 alpha beta T := by
  classical
  obtain ⟨C,hC,h⟩ := PRZZDiagonalContour.diagonal_error
  refine ⟨C,hC,?_⟩
  intro N a F1 F2 alpha beta T t hs hn hT htt
  have ht : 0 < t := hT.trans_le htt
  unfold assembled main errorMass
  simp only [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
  have hv0 : 0 < v := (Finset.mem_Icc.mp hv).1
  by_cases ha : admissible N d u v
  · simp only [if_pos ha,← mul_sub,norm_mul]
    have hh := h (alpha+beta) (t/(2*Real.pi*(u:ℝ)*v)) hs hn (by positivity)
    have hscale : (t/(2*Real.pi*(u:ℝ)*v))^(-(1/8:ℝ)) ≤
        (T/(2*Real.pi*(u:ℝ)*v))^(-(1/8:ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
        (by gcongr) (by norm_num)
    apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans
    calc
      _ ≤ ‖coefficient a F1 F2 alpha beta d u v‖ *
          (C*(1+16/‖alpha+beta‖^2)*(T/(2*Real.pi*(u:ℝ)*v))^(-(1/8:ℝ))) := by gcongr
      _ = _ := by ring
  · simp [ha]

theorem assembled_continuous (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hr : -1 ≤ (alpha+beta).re) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (assembled N a F1 F2 alpha beta) (Set.Icc T (2*T)) := by
  classical
  unfold assembled
  apply continuousOn_finsetSum
  intro d hd
  apply continuousOn_finsetSum
  intro u hu
  apply continuousOn_finsetSum
  intro v hv
  by_cases ha : admissible N d u v
  · simp only [if_pos ha]
    apply ContinuousOn.const_mul
    exact diagonal_time_continuous (alpha+beta) hs hr T hT u v
      (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1
  · simp only [if_neg ha]
    exact continuousOn_const

/-- The actual exterior arithmetic sum is integrated in time before
estimating its main-term defect. Integrability is supplied. -/
theorem assembled_time_error : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ),
    alpha+beta ≠ 0 → ‖alpha+beta‖ ≤ 1/8 → 0 < T →
    ∀ phi : ℝ → ℂ, Continuous phi →
    ‖(∫ t in Set.Icc T (2*T), phi t*assembled N a F1 F2 alpha beta t)-
      (∫ t in Set.Icc T (2*T), phi t)*main N a F1 F2 alpha beta‖ ≤
      C*(1+16/‖alpha+beta‖^2)*errorMass N a F1 F2 alpha beta T *
        (∫ t in Set.Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := assembled_error
  refine ⟨C,hC,?_⟩
  intro N a F1 F2 alpha beta T hs hn hT phi hphi
  have hr : -1 ≤ (alpha+beta).re := by
    have hh := (abs_le.mp ((abs_re_le_norm (alpha+beta)).trans hn)).1
    linarith
  have hi : IntegrableOn (fun t : ℝ => phi t*assembled N a F1 F2 alpha beta t) (Set.Icc T (2*T)) :=
    ((hphi.continuousOn).mul (assembled_continuous N a F1 F2 alpha beta hs hr T hT)).integrableOn_compact isCompact_Icc
  have hj : IntegrableOn (fun t : ℝ => phi t*main N a F1 F2 alpha beta) (Set.Icc T (2*T)) :=
    (hphi.mul_const (main N a F1 F2 alpha beta)).integrableOn_Icc
  rw [← integral_mul_const,← integral_sub hi hj]
  apply (norm_integral_le_integral_norm _).trans
  let B := C*(1+16/‖alpha+beta‖^2)*errorMass N a F1 F2 alpha beta T
  have hb : IntegrableOn (fun t : ℝ => B*‖phi t‖) (Set.Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hb ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [← mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_left (h N a F1 F2 alpha beta T t hs hn hT ht.1)
      (norm_nonneg _)).trans_eq (by dsimp [B]; ring)

def pair (L : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
    if m*u = k*v then F1 (d*u)*F2 (d*v)*term a a alpha beta
      (PRZZActualDirectSum.mainWeight alpha beta) t m k (d*u) (d*v) else 0

theorem pair_eq_filter (L : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v)
    (t : ℝ) (ht : 0 < t) :
    pair L a F1 F2 alpha beta d u v t = coefficient a F1 F2 alpha beta d u v *
      ∑ n ∈ primitiveCutoff L u v, scalarTerm (alpha+beta) u v n t := by
  unfold pair
  rw [finite_diagonal L u v hu hv hc]
  have he : (∑ ell ∈ Finset.Icc 1 L,
      if v*ell ≤ L ∧ u*ell ≤ L then F1 (d*u)*F2 (d*v)*term a a alpha beta
        (PRZZActualDirectSum.mainWeight alpha beta) t (v*ell) (u*ell) (d*u) (d*v) else 0) =
      ∑ ell ∈ Finset.Icc 1 L, if v*ell ≤ L ∧ u*ell ≤ L then
        coefficient a F1 F2 alpha beta d u v *
          (sourceW (alpha+beta) ((ell:ℝ)^2/(t/(2*Real.pi*(u:ℝ)*v)))/(ell:ℂ)^(1+(alpha+beta))) else 0 := by
    apply Finset.sum_congr rfl
    intro ell hell
    split_ifs
    · simpa only [add_assoc] using primitive_term a F1 F2 alpha beta d u v ell hd hu hv (mem_Icc.mp hell).1 t ht
    · rfl
  rw [he,PRZZL1Truncation.positive_sum]
  simp only [primitiveCutoff,scalarTerm,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]

theorem pair_continuous (L : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v)
    (hs : alpha+beta ≠ 0) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (pair L a F1 F2 alpha beta d u v) (Set.Icc T (2*T)) := by
  apply ContinuousOn.congr _ (fun t ht => pair_eq_filter L a F1 F2 alpha beta d u v hd hu hv hc t (hT.trans_le ht.1))
  apply ContinuousOn.const_mul
  exact continuousOn_finsetSum _ (fun n hn => scalar_time_continuous (alpha+beta) hs T hT u v hu hv n)

theorem pair_time_cutoff_removed (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hc : Nat.Coprime u v)
    (hs : alpha+beta ≠ 0) (hr : -1 ≤ (alpha+beta).re) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L : ℕ => ∫ t in Set.Icc T (2*T), phi t*pair L a F1 F2 alpha beta d u v t)
      atTop (𝓝 (∫ t in Set.Icc T (2*T), phi t*(coefficient a F1 F2 alpha beta d u v *
        PRZZDiagonalMellin.diagonal (alpha+beta) (t/(2*Real.pi*(u:ℝ)*v))))) := by
  obtain ⟨E,hE⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi.continuousOn
  let w := fun n : ℕ => scalarCap (alpha+beta) T u v*(1/((n+1:ℕ):ℝ)^4)
  have hp : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)^4) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
  have hw : Summable w := hp.mul_left _
  have hw0 : ∀ n, 0 ≤ w n := by intro n; dsimp [w,scalarCap,PRZZWArithmeticCutoff.decayConstant]; positivity
  let B := max E 0*‖coefficient a F1 F2 alpha beta d u v‖*(∑' n, w n)
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => B)
  · intro L
    exact (hphi.continuousOn.mul (pair_continuous L a F1 F2 alpha beta d u v hd hu hv hc hs T hT)).aestronglyMeasurable measurableSet_Icc
  · exact continuousOn_const.integrableOn_compact isCompact_Icc
  · intro L
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [pair_eq_filter L a F1 F2 alpha beta d u v hd hu hv hc t (hT.trans_le ht.1),norm_mul,norm_mul]
    have hb : ‖∑ n ∈ primitiveCutoff L u v, scalarTerm (alpha+beta) u v n t‖ ≤ ∑' n, w n := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun n hn => scalar_time_bound (alpha+beta) hs hr T hT u v hu hv n t ht)).trans
      exact hw.sum_le_tsum _ (fun n hn => hw0 n)
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_right ((hE t ht).trans (le_max_left E (0:ℝ)))
        (norm_nonneg (coefficient a F1 F2 alpha beta d u v))) hb
      (norm_nonneg _) (mul_nonneg (le_max_right E 0) (norm_nonneg _))
    simpa only [B,mul_assoc] using hh
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (pair_cutoff_removed a F1 F2 alpha beta d u v hd hu hv hc hs hr t (hT.trans_le ht.1)).const_mul (phi t)

#print axioms pair_eq_filter
#print axioms pair_continuous
#print axioms pair_time_cutoff_removed
#print axioms scalar_time_bound
#print axioms scalar_time_continuous
#print axioms diagonal_time_continuous
#print axioms assembled_error
#print axioms assembled_continuous
#print axioms assembled_time_error
#print axioms primitiveCutoff_tendsto
#print axioms scalar_bound
#print axioms scalar_summable
#print axioms pair_cutoff_removed
#print axioms coefficient_eq
#print axioms primitive_power
#print axioms primitive_term
#print axioms primitive_index
#print axioms finite_diagonal
end XiPrime8845.PRZZDiagonalAssembly
