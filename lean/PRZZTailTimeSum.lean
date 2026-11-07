import PRZZAbsorbedFourierTail

/-! Finite two-sided Fourier tails in the pruned row sum and time integral.
The actual smooth weight is used. Arithmetic coefficients remain literal;
their total mass is explicit, not hidden in a height-dependent constant. -/
noncomputable section
open scoped BigOperators FourierTransform ContDiff
open MeasureTheory Set
namespace XiPrime8845.PRZZTailTimeSum
set_option maxHeartbeats 3000000

structure Row where
  M : ℝ
  Q1 : ℝ
  Q2 : ℝ
  q : ℝ
  u : ℝ
  delta : ℝ
  H : ℕ

def Domain (d T b eD eH : ℝ) (z : Row) : Prop :=
  1 ≤ 3*z.M ∧ z.M ≤ T^b ∧ 0 < z.Q1 ∧ 0 < z.Q2 ∧
  0 < z.q ∧ z.q ≤ T ∧ z.q ≤ 3*z.Q2/d ∧ 1 ≤ z.u ∧ z.Q1/2 ≤ d*z.u ∧
  |z.delta| ≤ PRZZSourceCutoffs.deltaCutoff T z.M z.Q1 eD/d ∧
  PRZZSourceCutoffs.poissonCutoff d T z.M z.Q2 eH ≤ (z.H:ℝ)+1

def weight (F : ℝ → ℂ) (T t : ℝ) (alpha beta : ℂ) (z : Row) : ℝ → ℂ :=
  PRZZFullWeightSmooth.weight F z.M (2*Real.pi*z.u/(t*z.q)) (z.delta*t/z.u)
    (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))

/-- Use the pre-Poisson cutoff witness for the only lower M restriction. -/
theorem domain_of_active (d T b eD eH : ℝ) (z : Row) (s : Finset ℕ) (F : ℝ → ℂ)
    (hs : ∀ m ∈ s, 1 ≤ m)
    (hF : Function.support F ⊆ Icc (z.M/2) (3*z.M))
    (ha : PRZZPrunedTailRows.Active s F)
    (hM : z.M ≤ T^b) (hQ1 : 0 < z.Q1) (hQ2 : 0 < z.Q2)
    (hq : 0 < z.q) (hqT : z.q ≤ T) (hbox : z.q ≤ 3*z.Q2/d)
    (hu : 1 ≤ z.u) (hleft : z.Q1/2 ≤ d*z.u)
    (hdelta : |z.delta| ≤ PRZZSourceCutoffs.deltaCutoff T z.M z.Q1 eD/d)
    (hcut : PRZZSourceCutoffs.poissonCutoff d T z.M z.Q2 eH ≤ (z.H:ℝ)+1) :
    Domain d T b eD eH z :=
  ⟨PRZZPrunedTailRows.active_scale s F z.M hs hF ha,
    hM,hQ1,hQ2,hq,hqT,hbox,hu,hleft,hdelta,hcut⟩

def tail (F : ℝ → ℂ) (T t : ℝ) (alpha beta : ℂ) (z : Row) (j : ℕ) : ℝ :=
  ‖𝓕 (weight F T t alpha beta z) (((z.H+j:ℝ)+1)/z.q)‖+
    ‖𝓕 (weight F T t alpha beta z) (-(((z.H+j:ℝ)+1)/z.q))‖

def finiteTail (F : ℝ → ℂ) (T t : ℝ) (alpha beta : ℂ) (z : Row)
    (freq : Finset ℕ) (phasePlus phaseMinus : ℕ → ℂ) : ℂ :=
  ∑ j ∈ freq, (z.q⁻¹:ℝ) •
    (𝓕 (weight F T t alpha beta z) (((z.H+j:ℝ)+1)/z.q)*phasePlus j+
      𝓕 (weight F T t alpha beta z) (-(((z.H+j:ℝ)+1)/z.q))*phaseMinus j)

theorem finite_le (F : ℝ → ℂ) (T t : ℝ) (alpha beta : ℂ) (z : Row)
    (freq : Finset ℕ) (p m : ℕ → ℂ) (hq : 0 < z.q)
    (hp : ∀ j, ‖p j‖ ≤ 1) (hm : ∀ j, ‖m j‖ ≤ 1)
    (hs : Summable (tail F T t alpha beta z)) :
    ‖finiteTail F T t alpha beta z freq p m‖ ≤
      ∑' j, z.q⁻¹*tail F T t alpha beta z j := by
  apply (norm_sum_le _ _).trans
  apply le_trans (Finset.sum_le_sum (fun j hj => ?_))
    ((hs.mul_left z.q⁻¹).sum_le_tsum freq (fun j _ => by unfold tail; positivity))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hq)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le _ _).trans
  simp only [norm_mul,tail]
  exact add_le_add (by simpa using mul_le_mul_of_nonneg_left (hp j) (norm_nonneg _))
    (by simpa using mul_le_mul_of_nonneg_left (hm j) (norm_nonneg _))

/-- The time bound invokes the actual source tail, not a tail-bound premise.
`keep` can be instantiated with the pre-Poisson nonempty-row mask;
coefficients and phases survive. This bounds finite frequency truncations.
It does not assert integrability for arbitrary phase functions or interchange
an infinite Fourier series with the time integral. -/
theorem integrated (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ι : Type) (rows : Finset ι) (data : ι → Row)
      (keep : ι → Prop) [DecidablePred keep] (c : ι → ℂ) (freq : Finset ℕ)
      (p m : ι → ℝ → ℕ → ℂ) (d T : ℝ) (alpha beta : ℂ) (Phi : ℝ → ℂ),
      0 < d → 36 ≤ T → 1 ≤ Real.log T → ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      Continuous Phi →
      (∀ i ∈ rows, keep i → Domain d T b eD eH (data i)) →
      (∀ i ∈ rows, ∀ t ∈ Icc T (2*T), ∀ j, ‖p i t j‖ ≤ 1 ∧ ‖m i t j‖ ≤ 1) →
      ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ i ∈ rows,
        c i*(if keep i then finiteTail F T t alpha beta (data i) freq (p i t) (m i t) else 0))‖ ≤
      K*T^(-A)*(∑ i ∈ rows, ‖c i‖)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  obtain ⟨n,K,hK,h⟩ := PRZZAbsorbedFourierTail.source_tail F hF hsF a b S r eD eH A
    ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro ι rows data keep inst c freq p m d T alpha beta Phi hd hT hlog halpha hsep hPhi hdom hphase
  have hT0 : 0 < T := by linarith
  have hbound : ∀ t ∈ Icc T (2*T), ∀ i ∈ rows,
      ‖(if keep i then finiteTail F T t alpha beta (data i) freq (p i t) (m i t) else 0)‖ ≤ K*T^(-A) := by
    intro t ht i hi
    by_cases hk : keep i
    · rw [if_pos hk]
      obtain ⟨hM,hMT,hQ1,hQ2,hq,hqT,hbox,hu,hleft,hdelta,hcut⟩ := hdom i hi hk
      have hh := h (data i).H d T (data i).M (data i).Q1 (data i).Q2 (data i).q
        (data i).u t (data i).delta alpha beta hd hT hlog hM hMT hQ1 hQ2 hq hqT hbox
        hu hleft (hT0.trans_le ht.1) ht.2 hdelta halpha hsep hcut
      exact (finite_le F T t alpha beta (data i) freq (p i t) (m i t) hq
        (fun j => (hphase i hi t ht j).1) (fun j => (hphase i hi t ht j).2) hh.1).trans hh.2
    · simp only [if_neg hk,norm_zero]; positivity
  have hcont : Continuous (fun t : ℝ => ‖Phi (t/T)‖*(∑ i ∈ rows, ‖c i‖*(K*T^(-A)))) := by fun_prop
  have hh := PRZZSourceTailBudget.weighted_time_bound rows c
    (fun i t => if keep i then finiteTail F T t alpha beta (data i) freq (p i t) (m i t) else 0)
    (fun _ _ => K*T^(-A)) (fun t => Phi (t/T)) (Icc T (2*T)) measurableSet_Icc hbound
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  apply hh.trans_eq
  simp only [← Finset.sum_mul,integral_mul_const]
  ring

#print axioms finite_le
#print axioms domain_of_active
#print axioms integrated
end XiPrime8845.PRZZTailTimeSum
