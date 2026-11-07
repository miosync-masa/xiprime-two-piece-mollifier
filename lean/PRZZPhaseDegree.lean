import PRZZNormalizedTail

/-! The reciprocal-phase polynomial has degree at most its derivative order.
Thus its height loss grows linearly in the integration-by-parts order. -/
noncomputable section
namespace XiPrime8845.PRZZPhaseDegree
open Polynomial PRZZReciprocalJets
open PRZZFullWeightJets (convolution)
open PRZZEnvelopeMass
set_option maxHeartbeats 2000000

theorem convolution_growth (A B a b : ℕ → ℝ) (U : ℝ)
    (_hU : 0 ≤ U) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (ha : ∀ i, A i ≤ a i*U^i) (hb : ∀ i, B i ≤ b i*U^i) (n : ℕ) :
    convolution A B n ≤ convolution a b n*U^n := by
  unfold convolution
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (ha i) (Nat.cast_nonneg (n.choose i)))
    (hb (n-i)) (hB _) (mul_nonneg (Nat.cast_nonneg (n.choose i)) ((hA i).trans (ha i)))
  apply hh.trans_eq
  have hp : U^i*U^(n-i) = U^n := by rw [← pow_add,Nat.add_sub_of_le hin]
  calc
    _ = ((n.choose i:ℝ)*a i*b (n-i))*(U^i*U^(n-i)) := by ring
    _ = _ := by rw [hp]

theorem degree_bound (n : ℕ) : (polys n).natDegree ≤ n := by
  induction n with
  | zero => simp [polys]
  | succ n ih =>
    change (next n (polys n)).natDegree ≤ n+1
    unfold next
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      simp only [natDegree_neg, natDegree_X]
      have hh := natDegree_derivative_le (polys n)
      omega
    · apply natDegree_mul_le.trans
      have hh := natDegree_add_le (C (n:ℂ)) (C Complex.I*X)
      have hm : (C Complex.I*(X : ℂ[X])).natDegree ≤ (C Complex.I).natDegree+(X : ℂ[X]).natDegree := natDegree_mul_le
      simp only [natDegree_C,natDegree_X] at hh hm
      omega

theorem phase_order (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    envelope n R ≤ envelope n 1*(1+R)^n := by
  apply (PRZZJetUniform.phase_polynomial n R hR).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1+R) (degree_bound n))
    (envelope_nonneg n 1 (by norm_num))

/-- Actual Delta-cutoff phase radius; constants precede height. -/
theorem phase_height (n : ℕ) (eps T : ℝ) (heps : 0 ≤ eps) (hT : 1 ≤ T) :
    envelope n (8*T^eps) ≤ (envelope n 1*9^n)*T^(eps*(n:ℝ)) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hp : 1 ≤ T^eps := Real.one_le_rpow hT heps
  have hh := phase_order n (8*T^eps) (by positivity)
  calc
    _ ≤ envelope n 1*(9*T^eps)^n := hh.trans (by
      apply mul_le_mul_of_nonneg_left _ (envelope_nonneg n 1 (by norm_num))
      gcongr; linarith)
    _ = _ := by
      rw [mul_pow,← Real.rpow_natCast (T^eps) n,← Real.rpow_mul hT0.le]
      ring

/-- Uniform in the actual modulus box and every frequency beyond H_d.
The width-three source cutoff supplies q <= 3 Q2/d. -/
theorem cutoff_gain (d T M Q2 q h eD eH : ℝ)
    (hd : 0 < d) (hT : 1 ≤ T) (hM : 0 < M) (hQ : 0 < Q2)
    (hq : 0 ≤ q) (hbox : q ≤ 3*Q2/d) (heD : 0 ≤ eD)
    (hh : PRZZSourceCutoffs.poissonCutoff d T M Q2 eH ≤ h) :
    (1+8*T^eD)*q/(M*h) ≤ 27*T^(eD-eH) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hh0 : 0 < h := lt_of_lt_of_le (by
    unfold PRZZSourceCutoffs.poissonCutoff; positivity) hh
  have hp : 1 ≤ T^eD := Real.one_le_rpow hT heD
  have hr := PRZZSourceCutoffs.tail_ratio d T M Q2 eH eD h hd hT0 hM hQ hh
  calc
    _ ≤ (9*T^eD)*(3*Q2/d)/(M*h) := by gcongr; linarith
    _ = 27*(Q2*T^eD/(d*M*h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)

/-- Any fixed prefactor exponent is absorbed by choosing the order before
height and before the modulus/time indices. This does not supply that
prefactor for the full arithmetic family. -/
theorem cutoff_absorbed (eD eH B A : ℝ) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∀ d T M Q2 q h : ℝ,
      0 < d → 1 ≤ T → 0 < M → 0 < Q2 → 0 ≤ q → q ≤ 3*Q2/d →
      PRZZSourceCutoffs.poissonCutoff d T M Q2 eH ≤ h →
      T^B*((1+8*T^eD)*q/(M*h))^n ≤ (27:ℝ)^n*T^(-A) := by
  obtain ⟨n,hn⟩ := PRZZSourceCutoffs.exists_tail_order eD eH B A he
  refine ⟨n,?_⟩
  intro d T M Q2 q h hd hT hM hQ hq hbox hh
  have hh0 : 0 < h := lt_of_lt_of_le (by
    unfold PRZZSourceCutoffs.poissonCutoff
    have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
    positivity) hh
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hg := cutoff_gain d T M Q2 q h eD eH hd hT hM hQ hq hbox heD hh
  calc
    _ ≤ T^B*(27*T^(eD-eH))^n := by gcongr
    _ = (27:ℝ)^n*(T^B*(T^(eD-eH))^n) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hn T hT) (by positivity)

/-- The entire Leibniz cap incurs only one order-n phase loss. -/
theorem cap_phase_growth (C D E : ℕ → ℝ) (a k M R Z P s : ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i)
    (hk : 0 ≤ k) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs : 0 ≤ s) :
    PRZZJetUniform.uniformCap C D E a k M R Z P s n ≤
      PRZZJetUniform.uniformCap C D E a k M 0 Z P s n*(1+R)^n := by
  let A := convolution C (fun i => (Z+i)^i*Real.exp P)
  let W := fun i => (D i+E i*s)*(k*(M/2)^2)^(-a)
  have hA : ∀ i, 0 ≤ A i := fun i => convolution_nonneg _ _ (fun j => (hc j).1)
    (fun j => by positivity) i
  have hW : ∀ i, 0 ≤ W i := by intro i; dsimp [W]; obtain ⟨hd,he⟩ := (hc i).2; positivity
  have hU : 1 ≤ 1+R := by linarith
  have hphase : ∀ i, 0 ≤ envelope i 1 := fun i => envelope_nonneg i 1 (by norm_num)
  have hphaseR : ∀ i, 0 ≤ envelope i 1*(1+R)^(polys i).natDegree :=
    fun i => mul_nonneg (hphase i) (pow_nonneg (by linarith) _)
  have hinner : ∀ i, convolution A (fun j => envelope j 1*(1+R)^(polys j).natDegree) i ≤
      convolution A (fun j => envelope j 1) i*(1+R)^i := by
    intro i
    apply convolution_growth _ _ _ _ (1+R) (by positivity) hA hphaseR
    · intro j; exact le_mul_of_one_le_right (hA j) (one_le_pow₀ hU)
    · intro j
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (degree_bound j)) (hphase j)
  have hh := convolution_growth _ W _ W (1+R) (by positivity)
    (fun i => convolution_nonneg _ _ hA hphaseR i) hW hinner
    (fun i => le_mul_of_one_le_right (hW i) (one_le_pow₀ hU)) n
  simpa [PRZZJetUniform.uniformCap,A,W] using hh

/-- A nonzero original right cutoff supplies the modulus upper bound. -/
theorem source_modulus (F : ℝ → ℂ) (d Q q : ℝ) (hd : 0 < d)
    (hs : Function.support F ⊆ Set.Icc (Q/2) (3*Q)) (hf : F (d*q) ≠ 0) :
    q ≤ 3*Q/d := by
  exact (le_div_iff₀ hd).mpr (by simpa [mul_comm] using (hs hf).2)

/-- Expose the order-dependent gain separately from the fixed scale cost
in the normalized two-sided tail. -/
theorem normalized_shape (B M q R : ℝ) (n H : ℕ) (hM : 0 < M) :
    2*((3*M-M/2)*(B*(1+R)^(n+2)/(M/2)^(n+2)))*q^(n+1)/
        ((2*Real.pi)^(n+2)*((H:ℝ)+1)^n) =
      (5*2^(n+2)/(2*Real.pi)^(n+2))*B*(1+R)^2*(q/M)*
        ((1+R)*q/(M*((H:ℝ)+1)))^n := by
  simp only [div_pow,mul_pow,pow_add,pow_succ]
  field_simp
  <;> ring

#print axioms normalized_shape
#print axioms source_modulus
#print axioms convolution_growth
#print axioms cap_phase_growth
#print axioms cutoff_gain
#print axioms cutoff_absorbed
#print axioms degree_bound
#print axioms phase_order
#print axioms phase_height
end XiPrime8845.PRZZPhaseDegree
