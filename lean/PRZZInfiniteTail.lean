import PRZZSourceRows

/-! Transfer the actual absolute Fourier budget to the complex infinite tail.
Outer finite sums retain their coefficient mass. No AFE reindexing identity
or bound on the number of source configurations is assumed implicitly. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform
open Set MeasureTheory
namespace XiPrime8845.PRZZInfiniteTail
open PRZZTailTimeSum
set_option maxHeartbeats 3000000

theorem infinite_le (F : ℝ → ℂ) (T t : ℝ) (alpha beta : ℂ) (z : Row)
    (p m : ℕ → ℂ) (hq : 0 < z.q)
    (hp : ∀ j, ‖p j‖ ≤ 1) (hm : ∀ j, ‖m j‖ ≤ 1)
    (hs : Summable (tail F T t alpha beta z)) :
    let f := fun j => PRZZFourierTime.term F z.M z.u z.q z.delta
      (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) z.H j p m t
    Summable f ∧ ‖∑' j, f j‖ ≤ ∑' j, z.q⁻¹*tail F T t alpha beta z j := by
  dsimp only
  let f := fun j => PRZZFourierTime.term F z.M z.u z.q z.delta
    (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) z.H j p m t
  have hb : ∀ j, ‖f j‖ ≤ z.q⁻¹*tail F T t alpha beta z j := by
    intro j
    unfold f PRZZFourierTime.term
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hq)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (norm_add_le _ _).trans
    simp only [norm_mul,tail,weight]
    exact add_le_add (by simpa using mul_le_mul_of_nonneg_left (hp j) (norm_nonneg _))
      (by simpa using mul_le_mul_of_nonneg_left (hm j) (norm_nonneg _))
  have hn : Summable (fun j => ‖f j‖) := (hs.mul_left z.q⁻¹).of_nonneg_of_le
    (fun j => norm_nonneg _) hb
  exact ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum hb (hs.mul_left z.q⁻¹))⟩

/-- A single constant precedes every source row, time and residue phase. -/
theorem source_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d T t : ℝ) (z : Row) (alpha beta : ℂ)
      (p m : ℕ → ℂ),
      0 < d → 36 ≤ T → 1 ≤ Real.log T → t ∈ Icc T (2*T) →
      Domain d T b eD eH z → ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      (∀ j, ‖p j‖ ≤ 1) → (∀ j, ‖m j‖ ≤ 1) →
      let f := fun j => PRZZFourierTime.term F z.M z.u z.q z.delta
        (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) z.H j p m t
      Summable f ∧ ‖∑' j, f j‖ ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := PRZZAbsorbedFourierTail.source_tail F hF hsF
    a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro d T t z alpha beta p m hd hT hlog ht hz halpha hsep hp hm
  obtain ⟨hM,hMT,hQ1,hQ2,hq,hqT,hbox,hu,hleft,hdelta,hcut⟩ := hz
  have hh := h z.H d T z.M z.Q1 z.Q2 z.q z.u t z.delta alpha beta
    hd hT hlog hM hMT hQ1 hQ2 hq hqT hbox hu hleft (by linarith [ht.1]) ht.2
    hdelta halpha hsep hcut
  have hi := infinite_le F T t alpha beta z p m hq hp hm hh.1
  exact ⟨hi.1,hi.2.trans hh.2⟩

/-- Applies to nested finite d, Delta, M, j, l grids via their product index.
The total outer coefficient mass is explicit, not absorbed without a bound. -/
theorem outer_sum {ι : Type*} (s : Finset ι) (c f : ι → ℂ) (B : ℝ)
    (h : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∑ i ∈ s, c i*f i‖ ≤ (∑ i ∈ s, ‖c i‖)*B := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ s, ‖c i‖*B := Finset.sum_le_sum (fun i hi => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg _))
    _ = _ := (Finset.sum_mul s _ B).symm

/-- The same arbitrary-power budget now bounds the infinite complex tail
inside the weighted time integral and a finite outer configuration sum. -/
theorem integrated (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ι : Type) (rows : Finset ι) (data : ι → Row)
      (keep : ι → Prop) [DecidablePred keep] (c : ι → ℂ)
      (p m : ι → ℝ → ℕ → ℂ) (d T : ℝ) (alpha beta : ℂ) (Phi : ℝ → ℂ),
      0 < d → 36 ≤ T → 1 ≤ Real.log T → ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      Continuous Phi →
      (∀ i ∈ rows, keep i → Domain d T b eD eH (data i)) →
      (∀ i ∈ rows, ∀ t ∈ Icc T (2*T), ∀ j, ‖p i t j‖ ≤ 1 ∧ ‖m i t j‖ ≤ 1) →
      ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ i ∈ rows, c i*(if keep i then
        ∑' j, PRZZFourierTime.term F (data i).M (data i).u (data i).q (data i).delta
          (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) (data i).H j
          (p i t) (m i t) t else 0))‖ ≤
      K*T^(-A)*(∑ i ∈ rows, ‖c i‖)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  obtain ⟨K,hK,h⟩ := source_bound F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro ι rows data keep inst c p m d T alpha beta Phi hd hT hlog halpha hsep hPhi hdom hphase
  let f := fun i t => if keep i then
    ∑' j, PRZZFourierTime.term F (data i).M (data i).u (data i).q (data i).delta
      (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) (data i).H j
      (p i t) (m i t) t else 0
  have hbound : ∀ t ∈ Icc T (2*T), ∀ i ∈ rows, ‖f i t‖ ≤ K*T^(-A) := by
    intro t ht i hi
    dsimp only [f]
    split_ifs with hk
    · exact (h d T t (data i) alpha beta (p i t) (m i t) hd hT hlog ht
        (hdom i hi hk) halpha hsep (fun j => (hphase i hi t ht j).1)
        (fun j => (hphase i hi t ht j).2)).2
    · simp only [norm_zero]; positivity
  have hcont : Continuous (fun t : ℝ => ‖Phi (t/T)‖*(∑ i ∈ rows, ‖c i‖*(K*T^(-A)))) := by fun_prop
  have hh := PRZZSourceTailBudget.weighted_time_bound rows c f
    (fun _ _ => K*T^(-A)) (fun t => Phi (t/T)) (Icc T (2*T)) measurableSet_Icc hbound
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  apply hh.trans_eq
  simp only [← Finset.sum_mul,integral_mul_const]
  ring

#print axioms integrated
#print axioms infinite_le
#print axioms source_bound
#print axioms outer_sum
end XiPrime8845.PRZZInfiniteTail
