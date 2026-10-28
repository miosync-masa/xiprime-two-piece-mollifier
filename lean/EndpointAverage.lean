import CoprimeApproximation

/-! Localization of supported second moments to a thin harmonic window.
Take Q large, then the logarithmic window small, then L large. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace XiPrime8845.EndpointAverage
open SupportTail SupportProductTail SmoothMobius ShiftedEndpoint CoprimeApproximation
attribute [local instance] Classical.propDecidable

def mass (g K : ℕ) : ℝ := supportedSum g (Finset.Icc 1 K) (fun r => 1/(r : ℝ))
def tail (g K Q : ℕ) : ℝ :=
  supportedSum g ((Finset.Icc 1 K).filter (fun r => Q ≤ r)) (fun r => 1/(r : ℝ))

theorem mass_nonneg (g K : ℕ) : 0 ≤ mass g K := by unfold mass supportedSum; positivity
theorem tail_nonneg (g K Q : ℕ) : 0 ≤ tail g K Q := by unfold tail supportedSum; positivity

theorem tail_le_mass (g K Q : ℕ) : tail g K Q ≤ mass g K := by
  unfold tail mass supportedSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
  · intros; positivity

theorem mass_le_head_add_tail (g K Q : ℕ) : mass g K ≤ SupportTail.harmonic Q + tail g K Q := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.Icc 1 K).filter (supported g)) (p := fun r => Q ≤ r) (f := fun r => 1/(r : ℝ))
  have hhead : (∑ r ∈ ((Finset.Icc 1 K).filter (supported g)).filter (fun r => ¬ Q ≤ r), 1/(r : ℝ)) ≤
      SupportTail.harmonic Q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1.1.1, by omega⟩
    · intros; positivity
  have he : ∑ r ∈ ((Finset.Icc 1 K).filter (supported g)).filter (fun r => Q ≤ r), 1/(r : ℝ) = tail g K Q := by
    simp only [tail, supportedSum, Finset.filter_filter, and_comm]
  rw [he] at hsplit
  change _ = mass g K at hsplit
  linarith

theorem mass_square_bound (g K Q : ℕ) :
    mass g K ^ 2 ≤ SupportTail.harmonic Q ^ 2 + 2 * tail g K Q * mass g K := by
  have ht := tail_le_mass g K Q
  have ht0 := tail_nonneg g K Q
  have hm0 := mass_nonneg g K
  have hh0 : 0 ≤ SupportTail.harmonic Q := by unfold SupportTail.harmonic; positivity
  have hh := mass_le_head_add_tail g K Q
  have hs := mul_self_le_mul_self (sub_nonneg.mpr ht) (show mass g K-tail g K Q ≤ SupportTail.harmonic Q by linarith)
  nlinarith [sq_nonneg (tail g K Q)]

theorem harmonic_window (M N : ℕ) (hMN : M ≤ N) :
    (∑ g ∈ Finset.Ioc M N, 1/(g : ℝ)) = SupportTail.harmonic N-SupportTail.harmonic M := by
  have he (n : ℕ) : SupportTail.harmonic n = ∑ g ∈ Finset.Ioc 0 n, 1/(g : ℝ) := by
    rfl
  rw [he N, he M]
  have h := Finset.sum_Ioc_consecutive (fun g : ℕ => 1/(g : ℝ)) (Nat.zero_le M) hMN
  linarith

/-- Uniform in the supported cutoff K; localization is paid by harmonic
window mass for the head and a global product-safe Rankin tail. -/
theorem window_second_moment (M N K Q : ℕ) (hMN : M ≤ N) (hQ : 0 < Q) :
    (∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*mass g K ^ 2) ≤
      SupportTail.harmonic Q ^ 2 * (SupportTail.harmonic N-SupportTail.harmonic M) +
      2 * SupportTail.harmonic N * ((Q : ℝ)^(-1/4 : ℝ)*productConstant) := by
  have htail := tail_times_mass_bound N ((Finset.Icc 1 K).filter (fun r => Q ≤ r))
    (Finset.Icc 1 K) Q (by exact_mod_cast hQ)
    (fun r hr => by exact_mod_cast (Finset.mem_filter.mp hr).2)
    (fun r hr => Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hr).1))
  have htailwin : (∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*tail g K Q*mass g K) ≤
      SupportTail.harmonic N * ((Q : ℝ)^(-1/4 : ℝ)*productConstant) := by
    apply le_trans _ htail
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro g hg
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hg ⊢
      omega
    · intro g _ _
      exact mul_nonneg (mul_nonneg (by positivity) (tail_nonneg g K Q)) (mass_nonneg g K)
  calc
    _ ≤ ∑ g ∈ Finset.Ioc M N, (1/(g : ℝ)) *
        (SupportTail.harmonic Q ^ 2 + 2*tail g K Q*mass g K) := by
      exact Finset.sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (mass_square_bound g K Q) (by positivity))
    _ = SupportTail.harmonic Q ^ 2*(SupportTail.harmonic N-SupportTail.harmonic M) +
        2*(∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*tail g K Q*mass g K) := by
      rw [← harmonic_window M N hMN]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ _ := by linarith

/-- Endpoint-window domination for the actual scaled coprime sum. -/
theorem actual_window_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U K : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hK : 0 ≤ K) (hbound : ∀ t : ℝ, 0 ≤ t → WeightedMobius.absoluteError t ≤ K)
    (L : ℝ) (hL : 0 < L) (M N Q : ℕ) (hMN : M ≤ N) (hQ : 0 < Q)
    (u : ℕ → ℝ) (A : ℂ) (hA : ‖A‖ ≤ C)
    (hu : ∀ g ∈ Finset.Ioc M N, u g ∈ Set.Icc 0 U) :
    (∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*‖actual L g (u g) θ P A‖^2) ≤
      coprimeCap P θ C U K ^ 2 *
        (SupportTail.harmonic Q ^ 2*(SupportTail.harmonic N-SupportTail.harmonic M) +
          2*SupportTail.harmonic N*((Q : ℝ)^(-1/4 : ℝ)*productConstant)) := by
  have hB : 0 ≤ coprimeCap P θ C U K := mul_nonneg (Real.exp_pos _).le
    (scaledCap_nonneg P θ C U K hθ hC hU hK)
  have hmaj : (∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*‖actual L g (u g) θ P A‖^2) ≤
      coprimeCap P θ C U K ^ 2 * ∑ g ∈ Finset.Ioc M N, (1/(g : ℝ))*mass g ⌊Real.exp (L*U)⌋₊^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro g hg
    have hh := scaled_coprime_common_bound P hP A g L (u g) θ C U K hL hθ hA (hu g hg) hK hbound
    have hs := mul_self_le_mul_self (norm_nonneg _) hh
    have ht := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1/(g : ℝ))
    convert ht using 1
    · simp only [actual, pow_two]
    · unfold mass
      ring
  exact hmaj.trans (mul_le_mul_of_nonneg_left (window_second_moment M N _ Q hMN hQ) (sq_nonneg _))

theorem harmonic_eq_mobius (N : ℕ) : SupportTail.harmonic N = MobiusHarmonic.harmonic N := by
  rfl

/-- For the actual exponential endpoint window its harmonic mass is L*delta+O(1),
with the constant 4 explicit and independent of L,U,delta. -/
theorem harmonic_log_window_bound (L U delta : ℝ) (hL : 0 ≤ L)
    (hd : 0 ≤ delta) (hdU : delta ≤ U) :
    SupportTail.harmonic ⌊Real.exp (L*U)⌋₊ -
      SupportTail.harmonic ⌊Real.exp (L*(U-delta))⌋₊ ≤ L*delta+4 := by
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL (hd.trans hdU))
  have hy : 1 ≤ Real.exp (L*(U-delta)) := Real.one_le_exp_iff.mpr (mul_nonneg hL (sub_nonneg.mpr hdU))
  have h1 := (abs_le.mp (MobiusHarmonic.harmonicError_bound _ hx)).2
  have h2 := (abs_le.mp (MobiusHarmonic.harmonicError_bound _ hy)).1
  have hb1 : 2/Real.exp (L*U) ≤ 2 := by simpa using div_le_self (by norm_num : (0:ℝ) ≤ 2) hx
  have hb2 : 2/Real.exp (L*(U-delta)) ≤ 2 := by simpa using div_le_self (by norm_num : (0:ℝ) ≤ 2) hy
  simp only [MobiusHarmonic.harmonicError, Real.log_exp] at h1 h2
  rw [harmonic_eq_mobius, harmonic_eq_mobius]
  nlinarith

theorem endpoint_cutoff_mem (L U delta : ℝ) (hL : 0 < L) (g : ℕ)
    (hg : g ∈ Finset.Ioc ⌊Real.exp (L*(U-delta))⌋₊ ⌊Real.exp (L*U)⌋₊) :
    U-Real.log g/L ∈ Set.Icc 0 delta := by
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast
    (show 1 ≤ g by have := (Finset.mem_Ioc.mp hg).1; omega)
  have hg0 : 0 < (g : ℝ) := lt_of_lt_of_le zero_lt_one hg1
  have hupper := (Nat.le_floor_iff (Real.exp_pos (L*U)).le).mp (Finset.mem_Ioc.mp hg).2
  have hlower : Real.exp (L*(U-delta)) < g := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt (Finset.mem_Ioc.mp hg).1) ((Nat.le_floor_iff (Real.exp_pos _).le).mpr h)
  have hu := (Real.log_le_iff_le_exp hg0).mpr hupper
  have hd : L*(U-delta) < Real.log g := by
    rw [← Real.exp_lt_exp, Real.exp_log hg0]
    exact hlower
  have hu' := (div_le_iff₀ hL).mpr (show Real.log g ≤ U*L by nlinarith)
  have hd' := (le_div_iff₀ hL).mpr (show (U-delta)*L ≤ Real.log g by nlinarith)
  exact ⟨by linarith,by linarith⟩

/-- Explicit domination of the actual u_g<=delta endpoint. The bound has
head size H_Q^2*(L*delta+4) and a product-safe Q^(-1/4) tail. -/
theorem actual_log_endpoint_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U K : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hK : 0 ≤ K) (hbound : ∀ t : ℝ, 0 ≤ t → WeightedMobius.absoluteError t ≤ K)
    (L delta : ℝ) (hL : 0 < L) (hd : 0 ≤ delta) (hdU : delta ≤ U)
    (Q : ℕ) (hQ : 0 < Q) (A : ℂ) (hA : ‖A‖ ≤ C) :
    (∑ g ∈ Finset.Ioc ⌊Real.exp (L*(U-delta))⌋₊ ⌊Real.exp (L*U)⌋₊,
      (1/(g : ℝ))*‖actual L g (U-Real.log g/L) θ P A‖^2) ≤
      coprimeCap P θ C U K ^ 2 *
        (SupportTail.harmonic Q ^ 2*(L*delta+4) +
          2*SupportTail.harmonic ⌊Real.exp (L*U)⌋₊*((Q : ℝ)^(-1/4 : ℝ)*productConstant)) := by
  have hMN : ⌊Real.exp (L*(U-delta))⌋₊ ≤ ⌊Real.exp (L*U)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hL.le))
  apply (actual_window_bound P hP θ C U K hθ hC hU hK hbound L hL _ _ Q hMN hQ
    (fun g => U-Real.log g/L) A hA (fun g hg =>
      ⟨(endpoint_cutoff_mem L U delta hL g hg).1,(endpoint_cutoff_mem L U delta hL g hg).2.trans hdU⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact add_le_add (mul_le_mul_of_nonneg_left
    (harmonic_log_window_bound L U delta hL.le hd hdU) (sq_nonneg _)) le_rfl

#print axioms endpoint_cutoff_mem
#print axioms actual_log_endpoint_bound
#print axioms mass_square_bound
#print axioms window_second_moment
#print axioms actual_window_bound
#print axioms harmonic_log_window_bound
end XiPrime8845.EndpointAverage
