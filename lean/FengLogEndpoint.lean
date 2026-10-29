import FengLogBounds

/-! Localized harmonic averages for the logarithmic Feng block only.
The shared and off-g prime-power corrections still require their own estimates. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengLogEndpoint
open CoprimeEndpoint SupportProductTail FengAtG FengLogBounds
set_option maxHeartbeats 1000000

/-- A reusable endpoint bound for any quantity dominated by the Euler square. -/
theorem euler_window_bound (b : ℕ → ℝ) (L U δ D : ℝ) (Q : ℕ)
    (hL : 0 < L) (hδ : 0 ≤ δ) (hδU : δ ≤ U) (hD : 0 ≤ D) (hQ : 0 < Q)
    (hb : ∀ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U),
      b g ≤ D*SupportTail.eulerMass g 0 ^ 2) :
    (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*b g)/L ≤
      D*windowEnvelope L U δ Q := by
  have hMN : cutoff L (U-δ) ≤ cutoff L U := Nat.floor_mono
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hL.le))
  have hw := full_window _ _ Q hMN hQ
  have hh := EndpointAverage.harmonic_log_window_bound L U δ hL.le hδ hδU
  have hs : (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*b g) ≤
      D*(SupportTail.harmonic Q ^ 2*(L*δ+4)+
        2*SupportTail.harmonic (cutoff L U)*((Q:ℝ)^(-1/4:ℝ)*productConstant)) := by
    calc
      _ ≤ D*∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*SupportTail.eulerMass g 0 ^ 2 := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro g hg
        have h := mul_le_mul_of_nonneg_left (hb g hg) (by positivity : (0:ℝ)≤1/(g:ℝ))
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hw.trans
        (add_le_add (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) le_rfl)) hD
  apply (div_le_div_of_nonneg_right hs hL.le).trans_eq
  unfold windowEnvelope
  field_simp

/-- The head Q and endpoint width are chosen before L and the dominated family. -/
theorem euler_window_small (U D eps : ℝ) (hU : 0 < U) (hD : 0 ≤ D) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop, ∀ b : ℕ → ℝ,
      (∀ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), b g ≤ D*SupportTail.eulerMass g 0 ^ 2) →
      (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*b g)/L < eps := by
  have hp : Tendsto (fun Q : ℕ => (Q:ℝ)^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun Q : ℕ => D*(2*U*((Q:ℝ)^(-1/4:ℝ)*productConstant))) atTop (nhds 0) := by
    simpa using ((hp.mul_const productConstant).const_mul (2*U)).const_mul D
  obtain ⟨Q,hQ,htail⟩ := ((eventually_gt_atTop (0:ℕ)).and
    (ht.eventually (gt_mem_nhds (show (0:ℝ)<eps/2 by positivity)))).exists
  let a := D*SupportTail.harmonic Q ^ 2+1
  have ha : 0 < a := by dsimp [a]; positivity
  let δ := min U (eps/(4*a))
  have hδ : 0 < δ := lt_min hU (by positivity)
  have hδU : δ ≤ U := min_le_left _ _
  have hda : a*δ ≤ eps/4 := by
    have := mul_le_mul_of_nonneg_left (min_le_right U (eps/(4*a))) ha.le
    have he : a*(eps/(4*a)) = eps/4 := by field_simp
    exact this.trans_eq he
  have hlim : D*(SupportTail.harmonic Q ^ 2*δ+
      2*U*((Q:ℝ)^(-1/4:ℝ)*productConstant)) < eps := by
    dsimp [a] at hda
    nlinarith
  refine ⟨δ,hδ,hδU,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),
    ((windowEnvelope_tendsto U δ Q hU.le).const_mul D).eventually (gt_mem_nhds hlim)] with L hL hsmall
  intro b hb
  exact (euler_window_bound b L U δ D Q hL hδ.le hδU hD hQ hb).trans_lt hsmall

def endpointProduct (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (g : ℕ) : ℝ :=
  let u := LogProfileSum.coordinate L U g
  ‖logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A * logBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B‖

/-- Actual logarithmic blocks, not assumed envelopes: both shifts are uniform,
and g runs up to exp(L*U). The conclusion is only for this pair of blocks. -/
theorem logBlock_product_endpoint (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U eps : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U),
          (1/(g:ℝ))*endpointProduct L U θ P G A B g)/L < eps := by
  obtain ⟨DP,hDP,hPbound⟩ := logBlock_euler_bound P hP θ C U U hθ hC hU.le hU.le
  obtain ⟨DG,hDG,hGbound⟩ := logBlock_euler_bound G hG θ C U U hθ hC hU.le hU.le
  obtain ⟨δ,hδ,hδU,hsmall⟩ := euler_window_small U (DP*DG) eps hU (mul_nonneg hDP hDG) heps
  refine ⟨δ,hδ,hδU,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with L hL hs
  intro A B hA hB
  apply hs
  intro g hg
  have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hg0
  have hgexp : (g:ℝ) ≤ Real.exp (L*U) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  have hglog : Real.log g ≤ L*U := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<g)).mpr hgexp
  have ht := ShiftWeights.normalized_log_mem g L U hg1 hL hglog
  have ht' : |Real.log g/L| ≤ U := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hu := EndpointAverage.endpoint_cutoff_mem L U δ hL g hg
  have hu' : LogProfileSum.coordinate L U g ∈ Set.Icc 0 U := ⟨hu.1,hu.2.trans hδU⟩
  have hx := hPbound L hL g hg0 ht' _ hu' A hA
  have hy := hGbound L hL g hg0 ht' _ hu' B hB
  have hh := mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hDP (euler_nonneg g hg0))
  simpa only [endpointProduct,norm_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

/-- The same endpoint width works on both reflected bidiscs at once. -/
theorem logBlock_product_endpoint_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (θ U eps : ℝ)
    (hθ : 0 < θ) (hU : 0 < U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ p ∈ ElementaryGcd.twoBidiscs,
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U),
          (1/(g:ℝ))*endpointProduct L U θ P G p.1 p.2 g)/L < eps := by
  obtain ⟨δ,hd,hdU,h⟩ := logBlock_product_endpoint P G hP hG θ (5*PRZZAsymptotic.R/4) U eps
    hθ (by have := PRZZAsymptotic.radius_pos; positivity) hU heps
  refine ⟨δ,hd,hdU,?_⟩
  filter_upwards [h] with L hL
  intro p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact hL p.1 p.2 hs.1 hs.2

#print axioms euler_window_bound
#print axioms euler_window_small
#print axioms logBlock_product_endpoint
#print axioms logBlock_product_endpoint_twoBidiscs
end XiPrime8845.FengLogEndpoint
