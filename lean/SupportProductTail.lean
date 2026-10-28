import SupportTail

/-! Product-safe harmonic averages for supported convolution weights.
These bounds control two supported sums, not just their first moments. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.SupportProductTail
open SupportTail SmoothMobius
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def rootRad (n : ℕ) : ℝ := Real.sqrt (rad n : ℝ)

theorem rootRad_pos (n : ℕ) : 0 < rootRad n :=
  Real.sqrt_pos.mpr (by exact_mod_cast rad_pos n)

theorem rad_dvd_of_dvd (r n : ℕ) (hn : n ≠ 0) (h : r ∣ n) : rad r ∣ rad n := by
  unfold rad
  apply Finset.prod_primes_dvd
  · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).prime
  · intro p hp
    exact Finset.dvd_prod_of_mem (f := id) (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans h, hn⟩)

theorem rootRad_product_le (r s : ℕ) (hr : r ≠ 0) (hs : s ≠ 0) :
    rootRad r * rootRad s ≤ (rad (r*s) : ℝ) := by
  have hrle : (rad r : ℝ) ≤ rad (r*s) := by
    exact_mod_cast Nat.le_of_dvd (rad_pos _) (rad_dvd_of_dvd r (r*s) (mul_ne_zero hr hs) (dvd_mul_right r s))
  have hsle : (rad s : ℝ) ≤ rad (r*s) := by
    exact_mod_cast Nat.le_of_dvd (rad_pos _) (rad_dvd_of_dvd s (r*s) (mul_ne_zero hr hs) (dvd_mul_left s r))
  calc
    _ ≤ rootRad (r*s) * rootRad (r*s) := mul_le_mul (Real.sqrt_le_sqrt hrle)
      (Real.sqrt_le_sqrt hsle) (rootRad_pos s).le (rootRad_pos _).le
    _ = _ := by unfold rootRad; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ rad (r*s) by positivity)]

/-- Square-root radical weighting is still summable, allowing two factors. -/
theorem summable_root_weight :
    Summable (fun n : ℕ => (n : ℝ)^(-3/4 : ℝ) / rootRad n) := by
  choose a b hab hsf using Nat.sq_mul_squarefree
  have hinj : Function.Injective (fun n => (a n, b n)) := by
    intro n m h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    dsimp only at ha hb
    rw [← hab n, ← hab m, ha, hb]
  have haSum : Summable (fun a : ℕ => (a : ℝ)^(-5/4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hbSum : Summable (fun b : ℕ => (b : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor := (haSum.mul_of_nonneg hbSum (by intro n; positivity)
    (by intro n; positivity)).comp_injective hinj
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (by positivity) (rootRad_pos n).le) _ hmajor
  intro n
  change (n : ℝ)^(-3/4 : ℝ) / rootRad n ≤
    (a n : ℝ)^(-5/4 : ℝ) * (b n : ℝ)^(-3/2 : ℝ)
  by_cases hn : n = 0
  · subst n; simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (-3/4 : ℝ) ≠ 0), zero_div]; positivity
  have han : a n ∣ n := ⟨(b n)^2, by simpa only [mul_comm] using (hab n).symm⟩
  have har : a n ≤ rad n := Nat.le_of_dvd (rad_pos n) (squarefree_dvd_rad (hsf n) hn han)
  have ha0 : 0 < (a n : ℝ) := by exact_mod_cast (hsf n).ne_zero.bot_lt
  calc
    _ ≤ (n : ℝ)^(-3/4 : ℝ) / Real.sqrt (a n : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr ha0)
        (Real.sqrt_le_sqrt (by exact_mod_cast har))
    _ = (a n : ℝ)^(-5/4 : ℝ) * (b n : ℝ)^(-3/2 : ℝ) := by
      have hncast : (n : ℝ) = (b n : ℝ)^2 * (a n : ℝ) := by exact_mod_cast (hab n).symm
      have hapow : (a n : ℝ)^(-5/4 : ℝ) =
          (a n : ℝ)^(-3/4 : ℝ) / (a n : ℝ)^(1/2 : ℝ) := by
        rw [← Real.rpow_sub ha0]; norm_num
      rw [hncast, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity), Real.sqrt_eq_rpow, hapow]
      norm_num
      ring

def productConstant : ℝ := (∑' n : ℕ, (n : ℝ)^(-3/4 : ℝ)/rootRad n)^2

def supportedSum (g : ℕ) (s : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ r ∈ s.filter (supported g), b r

theorem supported_product_average (N : ℕ) (s t : Finset ℕ) (b c : ℕ → ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) (ht : ∀ r ∈ t, r ≠ 0) :
    (∑ g ∈ Icc 1 N, (1/(g : ℝ)) * supportedSum g s b * supportedSum g t c) =
      ∑ r ∈ s, ∑ q ∈ t, b r * c q * (SupportTail.harmonic (N/rad (r*q)) / (rad (r*q) : ℝ)) := by
  simp only [supportedSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [← supported_harmonic N (r*q) (mul_ne_zero (hs r hr) (ht q hq)),
    Finset.sum_filter, Finset.mul_sum]
  apply sum_congr rfl
  intro g hg
  rw [supported_mul]
  split_ifs <;> simp_all <;> ring

theorem supported_product_average_le (N : ℕ) (s t : Finset ℕ) (b c : ℕ → ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) (ht : ∀ r ∈ t, r ≠ 0)
    (hb : ∀ r ∈ s, 0 ≤ b r) (hc : ∀ r ∈ t, 0 ≤ c r) :
    (∑ g ∈ Icc 1 N, (1/(g : ℝ)) * supportedSum g s b * supportedSum g t c) ≤
      SupportTail.harmonic N * (∑ r ∈ s, b r / rootRad r) * (∑ q ∈ t, c q / rootRad q) := by
  rw [supported_product_average N s t b c hs ht]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_le_sum
  intro r hr
  apply sum_le_sum
  intro q hq
  have hH : 0 ≤ SupportTail.harmonic N := by unfold SupportTail.harmonic; positivity
  have ha := div_le_div_of_nonneg_left hH
    (mul_pos (rootRad_pos r) (rootRad_pos q)) (rootRad_product_le r q (hs r hr) (ht q hq))
  have hm := div_le_div_of_nonneg_right
    (harmonic_mono (Nat.div_le_self N (rad (r*q)))) (by positivity : (0:ℝ) ≤ rad (r*q))
  have hh := mul_le_mul_of_nonneg_left (hm.trans ha) (mul_nonneg (hb r hr) (hc q hq))
  convert hh using 1 <;> ring

def rootConstant : ℝ := ∑' n : ℕ, (n : ℝ)^(-3/4 : ℝ)/rootRad n

theorem rootConstant_nonneg : 0 ≤ rootConstant :=
  tsum_nonneg (fun n => div_nonneg (by positivity) (rootRad_pos n).le)

theorem root_sum_bound (s : Finset ℕ) (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r ∈ s, b r ≤ C * (r : ℝ)^(-3/4 : ℝ)) :
    (∑ r ∈ s, b r / rootRad r) ≤ C * rootConstant := by
  calc
    _ ≤ ∑ r ∈ s, C * ((r : ℝ)^(-3/4 : ℝ)/rootRad r) := by
      apply sum_le_sum
      intro r hr
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hb r hr) (rootRad_pos r).le
    _ = C * ∑ r ∈ s, (r : ℝ)^(-3/4 : ℝ)/rootRad r := (Finset.mul_sum ..).symm
    _ ≤ C * rootConstant := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum s (fun n _ => div_nonneg (by positivity) (rootRad_pos n).le)
        summable_root_weight) hC

/-- A finite second-moment bound with constants independent of both cutoffs. -/
theorem supported_product_bound (N : ℕ) (s t : Finset ℕ) (b c : ℕ → ℝ)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs : ∀ r ∈ s, r ≠ 0) (ht : ∀ r ∈ t, r ≠ 0)
    (hb0 : ∀ r ∈ s, 0 ≤ b r) (hc0 : ∀ r ∈ t, 0 ≤ c r)
    (hb : ∀ r ∈ s, b r ≤ B * (r : ℝ)^(-3/4 : ℝ))
    (hc : ∀ r ∈ t, c r ≤ C * (r : ℝ)^(-3/4 : ℝ)) :
    (∑ g ∈ Icc 1 N, (1/(g : ℝ))*supportedSum g s b*supportedSum g t c) ≤
      SupportTail.harmonic N * (B*C*productConstant) := by
  apply (supported_product_average_le N s t b c hs ht hb0 hc0).trans
  have h := mul_le_mul (root_sum_bound s b B hB hb) (root_sum_bound t c C hC hc)
    (sum_nonneg (fun r hr => div_nonneg (hc0 r hr) (rootRad_pos r).le))
    (mul_nonneg hB rootConstant_nonneg)
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ SupportTail.harmonic N by unfold SupportTail.harmonic; positivity)
  convert hh using 1
  · ring
  · change SupportTail.harmonic N * (B*C*rootConstant^2) =
      SupportTail.harmonic N * (B*rootConstant*(C*rootConstant))
    ring

/-- One tail may be multiplied by a full supported mass before averaging. -/
theorem tail_times_mass_bound (N : ℕ) (s t : Finset ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hs : ∀ r ∈ s, Q ≤ (r : ℝ)) (ht : ∀ r ∈ t, r ≠ 0) :
    (∑ g ∈ Icc 1 N, (1/(g : ℝ))*supportedSum g s (fun r => 1/(r : ℝ))*
      supportedSum g t (fun r => 1/(r : ℝ))) ≤
      SupportTail.harmonic N * (Q^(-1/4 : ℝ)*productConstant) := by
  have hb : ∀ r ∈ s, 1/(r : ℝ) ≤ Q^(-1/4 : ℝ)*(r : ℝ)^(-3/4 : ℝ) := by
    intro r hr
    convert rankin_point r Q (1/4) hQ (hs r hr) (by norm_num) using 1 <;> norm_num
  have hc : ∀ r ∈ t, 1/(r : ℝ) ≤ 1*(r : ℝ)^(-3/4 : ℝ) := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ht r hr)
    simpa only [show (1/4-1 : ℝ) = -3/4 by norm_num, Real.one_rpow, one_mul] using
      rankin_point r 1 (1/4) (by norm_num) hr1 (by norm_num)
  simpa only [mul_one] using supported_product_bound N s t _ _ (Q^(-1/4 : ℝ)) 1
    (by positivity) (by norm_num)
    (fun r hr => by exact_mod_cast (hQ.trans_le (hs r hr)).ne') ht
    (by intros; positivity) (by intros; positivity) hb hc

def normalizedProductTail (N K J : ℕ) (Q : ℝ) : ℝ :=
  (∑ g ∈ Icc 1 N, (1/(g : ℝ))*
    supportedSum g ((Icc 1 K).filter (fun r => Q ≤ (r : ℝ))) (fun r => 1/(r : ℝ))*
    supportedSum g (Icc 1 J) (fun r => 1/(r : ℝ))) / SupportTail.harmonic N

theorem normalizedProductTail_nonneg (N K J : ℕ) (Q : ℝ) :
    0 ≤ normalizedProductTail N K J Q := by
  unfold normalizedProductTail supportedSum SupportTail.harmonic
  positivity

theorem normalizedProductTail_bound (N K J : ℕ) (Q : ℝ) (hQ : 0 < Q) :
    normalizedProductTail N K J Q ≤ Q^(-1/4 : ℝ)*productConstant := by
  by_cases hH : SupportTail.harmonic N = 0
  · simp only [normalizedProductTail, hH, div_zero]
    unfold productConstant; positivity
  have hHpos : 0 < SupportTail.harmonic N := lt_of_le_of_ne
    (by unfold SupportTail.harmonic; positivity) (Ne.symm hH)
  rw [normalizedProductTail, div_le_iff₀ hHpos]
  simpa only [mul_comm] using tail_times_mass_bound N
    ((Icc 1 K).filter (fun r => Q ≤ (r : ℝ))) (Icc 1 J) Q hQ
    (fun r hr => (mem_filter.mp hr).2)
    (fun r hr => Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1))

open Filter Topology in
theorem normalizedProductTail_uniform_zero :
    TendstoUniformlyOn (fun (Q : ℝ) (p : ℕ × ℕ × ℕ) =>
      normalizedProductTail p.1 p.2.1 p.2.2 Q) (fun _ => 0) atTop Set.univ := by
  have hlim : Tendsto (fun Q : ℝ => Q^(-1/4 : ℝ)*productConstant) atTop (nhds 0) := by
    simpa only [neg_div, zero_mul] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).mul_const productConstant
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds heps)] with Q hQ hε
  intro p hp
  rw [dist_comm, Real.dist_eq, sub_zero, abs_of_nonneg (normalizedProductTail_nonneg _ _ _ _)]
  exact (normalizedProductTail_bound _ _ _ Q hQ).trans_lt hε

/-- A nonnegative coefficient envelope with summable radical weighting. -/
def RootBound (s : Finset ℕ) (b : ℕ → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ r ∈ s, 0 ≤ b r ∧ b r ≤ B*(r : ℝ)^(-3/4 : ℝ)

theorem supportedSum_nonneg (g : ℕ) (s : Finset ℕ) (b : ℕ → ℝ)
    (hb : ∀ r ∈ s, 0 ≤ b r) : 0 ≤ supportedSum g s b :=
  sum_nonneg (fun r hr => hb r (mem_filter.mp hr).1)

/-- Return errors in two complex factors to the harmonic g-average.
The four pointwise envelopes are explicit hypotheses, not arithmetic axioms. -/
theorem product_error_average (N : ℕ) (s t : Finset ℕ)
    (x y x₀ y₀ : ℕ → ℂ) (b c e f : ℕ → ℝ) (B C E F : ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) (ht : ∀ r ∈ t, r ≠ 0)
    (hb : RootBound s b B) (hc : RootBound t c C)
    (he : RootBound s e E) (hf : RootBound t f F)
    (hx : ∀ g ∈ Icc 1 N, ‖x₀ g‖ ≤ supportedSum g s b)
    (hy : ∀ g ∈ Icc 1 N, ‖y g‖ ≤ supportedSum g t c)
    (hex : ∀ g ∈ Icc 1 N, ‖x g-x₀ g‖ ≤ supportedSum g s e)
    (hey : ∀ g ∈ Icc 1 N, ‖y g-y₀ g‖ ≤ supportedSum g t f) :
    (∑ g ∈ Icc 1 N, (1/(g : ℝ))*‖x g*y g-x₀ g*y₀ g‖) ≤
      SupportTail.harmonic N * ((E*C+B*F)*productConstant) := by
  have hleft := supported_product_bound N s t e c E C he.1 hc.1 hs ht
    (fun r hr => (he.2 r hr).1) (fun r hr => (hc.2 r hr).1)
    (fun r hr => (he.2 r hr).2) (fun r hr => (hc.2 r hr).2)
  have hright := supported_product_bound N s t b f B F hb.1 hf.1 hs ht
    (fun r hr => (hb.2 r hr).1) (fun r hr => (hf.2 r hr).1)
    (fun r hr => (hb.2 r hr).2) (fun r hr => (hf.2 r hr).2)
  calc
    _ ≤ ∑ g ∈ Icc 1 N, (1/(g : ℝ)) *
        (supportedSum g s e * supportedSum g t c + supportedSum g s b * supportedSum g t f) := by
      apply sum_le_sum
      intro g hg
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [show x g*y g-x₀ g*y₀ g = (x g-x₀ g)*y g+x₀ g*(y g-y₀ g) by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul (hex g hg) (hy g hg) (norm_nonneg _)
          (supportedSum_nonneg g s e (fun r hr => (he.2 r hr).1)))
        (mul_le_mul (hx g hg) (hey g hg) (norm_nonneg _)
          (supportedSum_nonneg g s b (fun r hr => (hb.2 r hr).1)))
    _ = (∑ g ∈ Icc 1 N, (1/(g : ℝ))*supportedSum g s e*supportedSum g t c) +
        ∑ g ∈ Icc 1 N, (1/(g : ℝ))*supportedSum g s b*supportedSum g t f := by
      simp only [mul_add, Finset.sum_add_distrib, mul_assoc]
    _ ≤ _ := by nlinarith [hleft, hright]

/-- Head error eps/r plus a Rankin tail has a product-safe coefficient bound. -/
theorem head_tail_rootBound (s : Finset ℕ) (eps C Q : ℝ)
    (heps : 0 ≤ eps) (hC : 0 ≤ C) (hQ : 0 < Q) (hs : ∀ r ∈ s, r ≠ 0) :
    RootBound s (fun r => eps/(r : ℝ) + if Q ≤ (r : ℝ) then C/(r : ℝ) else 0)
      (eps+C*Q^(-1/4 : ℝ)) := by
  refine ⟨by positivity, ?_⟩
  intro r hr
  dsimp only
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hs r hr)
  have hrec : 1/(r : ℝ) ≤ (r : ℝ)^(-3/4 : ℝ) := by
    simpa only [show (1/4-1 : ℝ) = -3/4 by norm_num, Real.one_rpow, one_mul] using
      rankin_point r 1 (1/4) (by norm_num) hr1 (by norm_num)
  have hhead := mul_le_mul_of_nonneg_left hrec heps
  refine ⟨by split_ifs <;> positivity, ?_⟩
  by_cases h : Q ≤ (r : ℝ)
  · rw [if_pos h]
    have htail : 1/(r : ℝ) ≤ Q^(-1/4 : ℝ)*(r : ℝ)^(-3/4 : ℝ) := by
      convert rankin_point r Q (1/4) hQ h (by norm_num) using 1 <;> norm_num
    have hh := mul_le_mul_of_nonneg_left htail hC
    simp only [mul_one_div] at hhead hh
    nlinarith [hhead, hh]
  · rw [if_neg h, add_zero]
    have : 0 ≤ C*Q^(-1/4 : ℝ)*(r : ℝ)^(-3/4 : ℝ) := by positivity
    simp only [mul_one_div] at hhead
    nlinarith [hhead]

#print axioms product_error_average
#print axioms head_tail_rootBound
#print axioms supported_product_bound
#print axioms tail_times_mass_bound
#print axioms normalizedProductTail_bound
#print axioms normalizedProductTail_uniform_zero
#print axioms rootRad_product_le
#print axioms summable_root_weight
#print axioms supported_product_average
#print axioms supported_product_average_le
end XiPrime8845.SupportProductTail
