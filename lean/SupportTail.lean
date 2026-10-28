import ElementaryGcd

/-! Rankin tails and exact harmonic averaging of supported-number weights.
The finite Euler product depends on g; no g-uniform PNT error is asserted. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.SupportTail
set_option maxHeartbeats 1000000
open SmoothMobius ElementaryGcd
attribute [local instance] Classical.propDecidable

def powerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^s
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (by positivity) (by positivity)

def eulerMass (g : ℕ) (δ : ℝ) : ℝ :=
  ∏ p ∈ g.primeFactors, (1-(p : ℝ)^(δ-1))⁻¹

theorem supported_factored (g r : ℕ) (hg : g ≠ 0) :
    supported g r ↔ r ∈ Nat.factoredNumbers g.primeFactors := by
  simp only [Nat.mem_factoredNumbers', Nat.mem_primeFactors, supported]
  exact ⟨fun h p hp hpr => ⟨hp,h p hp hpr,hg⟩, fun h p hp hpr => (h p hp hpr).2.1⟩

/-- All prime powers are included in this convergent fixed-g Euler product. -/
theorem supported_hasSum (g : ℕ) (δ : ℝ) (hδ : δ < 1) :
    HasSum (fun r : Nat.factoredNumbers g.primeFactors => (r.val : ℝ)^(δ-1))
      (eulerMass g δ) := by
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerHom (δ-1)) (fun {p} hp => show ‖(p : ℝ)^(δ-1)‖ < 1 from by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith))
    g.primeFactors
  have hf : g.primeFactors.filter Nat.Prime = g.primeFactors :=
    filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  simpa only [powerHom, MonoidHom.coe_mk, OneHom.coe_mk, hf, eulerMass] using h.2

theorem rankin_point (x Q δ : ℝ) (hQ : 0 < Q) (hx : Q ≤ x) (hδ : 0 ≤ δ) :
    1/x ≤ Q^(-δ)*x^(δ-1) := by
  have hx0 : 0 < x := hQ.trans_le hx
  have hp := Real.rpow_le_rpow hQ.le hx hδ
  rw [Real.rpow_neg hQ.le, Real.rpow_sub_one hx0.ne']
  apply (div_le_iff₀ hx0).mpr
  -- Clear both positive denominators without changing the direction.
  have hqpow : 0 < Q^δ := Real.rpow_pos_of_pos hQ δ
  calc
    1 ≤ x^δ / Q^δ := (one_le_div hqpow).mpr hp
    _ = (Q^δ)⁻¹ * (x^δ/x) * x := by field_simp

theorem rankin_finite (s : Finset ℕ) (Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hs : ∀ r ∈ s, Q ≤ (r : ℝ)) :
    (∑ r ∈ s, 1/(r : ℝ)) ≤ Q^(-δ)*∑ r ∈ s, (r : ℝ)^(δ-1) := by
  rw [Finset.mul_sum]
  exact sum_le_sum fun r hr => rankin_point r Q δ hQ (hs r hr) hδ

def rad (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors, p

theorem rad_pos (r : ℕ) : 0 < rad r := by
  exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp

theorem supported_iff_rad_dvd (g r : ℕ) (hr : r ≠ 0) :
    supported g r ↔ rad r ∣ g := by
  constructor
  · intro h
    exact Finset.prod_primes_dvd g (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  · intro h p hp hpr
    exact (Finset.dvd_prod_of_mem (f := id) (Nat.mem_primeFactors.mpr ⟨hp,hpr,hr⟩)).trans h

def harmonic (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, 1/(n : ℝ)

theorem harmonic_mono {M N : ℕ} (h : M ≤ N) : harmonic M ≤ harmonic N := by
  exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
    (fun _ _ _ => by positivity)

theorem supported_harmonic (N r : ℕ) (hr : r ≠ 0) :
    (∑ g ∈ (Finset.Icc 1 N).filter (fun g => supported g r), 1/(g : ℝ)) =
      harmonic (N / rad r) / (rad r : ℝ) := by
  simp_rw [supported_iff_rad_dvd _ r hr]
  have h := sum_multiples N (rad r) (rad_pos r) (fun g => (1/(g : ℝ) : ℂ))
  have h' : (∑ g ∈ (Finset.Icc 1 N).filter (fun g => rad r ∣ g), 1/(g : ℝ)) =
      ∑ n ∈ Finset.Icc 1 (N/rad r), 1/((rad r*n : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [h']
  simp only [Nat.cast_mul, harmonic, div_mul_eq_div_div, Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  ring

/-- Swap the g/r sums before estimating. The gain is 1/rad(r), not tau(g). -/
theorem supported_average (N : ℕ) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) :
    (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) *
      ∑ r ∈ s.filter (supported g), b r) =
      ∑ r ∈ s, b r * (harmonic (N/rad r)/(rad r : ℝ)) := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [← supported_harmonic N r (hs r hr), Finset.sum_filter, Finset.mul_sum]
  apply sum_congr rfl
  intro g hg
  split_ifs <;> ring

theorem supported_average_le (N : ℕ) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) (hb : ∀ r ∈ s, 0 ≤ b r) :
    (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) * ∑ r ∈ s.filter (supported g), b r) ≤
      harmonic N * ∑ r ∈ s, b r/(rad r : ℝ) := by
  rw [supported_average N s b hs, Finset.mul_sum]
  apply sum_le_sum
  intro r hr
  have h := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (harmonic_mono (Nat.div_le_self N (rad r)))
      (by positivity : 0 ≤ (rad r : ℝ))) (hb r hr)
  convert h using 1
  ring

theorem supported_mass_le (g : ℕ) (hg : g ≠ 0) (s : Finset ℕ) (δ : ℝ)
    (hδ : δ < 1) (hs : ∀ r ∈ s, supported g r) :
    (∑ r ∈ s, (r : ℝ)^(δ-1)) ≤ eulerMass g δ := by
  have h : HasSum ((Nat.factoredNumbers g.primeFactors).indicator
      (fun n : ℕ => (n : ℝ)^(δ-1))) (eulerMass g δ) :=
    hasSum_subtype_iff_indicator.mp (supported_hasSum g δ hδ)
  have hb := sum_le_hasSum s (fun r _ => show
    0 ≤ (Nat.factoredNumbers g.primeFactors).indicator
      (fun n : ℕ => (n : ℝ)^(δ-1)) r from by
        apply Set.indicator_nonneg
        intro n hn
        positivity) h
  calc
    _ = ∑ r ∈ s, (Nat.factoredNumbers g.primeFactors).indicator
        (fun n : ℕ => (n : ℝ)^(δ-1)) r := by
      apply sum_congr rfl
      intro r hr
      exact (Set.indicator_of_mem ((supported_factored g r hg).mp (hs r hr))
        (fun n : ℕ => (n : ℝ)^(δ-1))).symm
    _ ≤ _ := hb

theorem supported_rankin_tail (g : ℕ) (hg : g ≠ 0) (s : Finset ℕ) (Q δ : ℝ)
    (hQ : 0 < Q) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hs : ∀ r ∈ s, supported g r) (hlarge : ∀ r ∈ s, Q ≤ (r : ℝ)) :
    (∑ r ∈ s, 1/(r : ℝ)) ≤ Q^(-δ) * eulerMass g δ := by
  exact (rankin_finite s Q δ hQ hδ0 hlarge).trans
    (mul_le_mul_of_nonneg_left (supported_mass_le g hg s δ hδ1 hs) (by positivity))

/-- Average first, then apply Rankin. The remaining series is independent of g.
Its global summability is deliberately not assumed in this finite inequality. -/
theorem averaged_rankin_bound (N : ℕ) (s : Finset ℕ) (Q δ : ℝ)
    (hQ : 0 < Q) (hδ : 0 ≤ δ) (hs : ∀ r ∈ s, Q ≤ (r : ℝ)) :
    (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) *
      ∑ r ∈ s.filter (supported g), 1/(r : ℝ)) ≤
      harmonic N * Q^(-δ) * ∑ r ∈ s, (r : ℝ)^(δ-1)/(rad r : ℝ) := by
  have hn (r : ℕ) (hr : r ∈ s) : r ≠ 0 := by
    have : 0 < (r : ℝ) := hQ.trans_le (hs r hr)
    exact_mod_cast this.ne'
  apply (supported_average_le N s (fun r => 1/(r : ℝ)) hn (by intros; positivity)).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by unfold harmonic; positivity)
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro r hr
  have h := div_le_div_of_nonneg_right (rankin_point r Q δ hQ (hs r hr) hδ)
    (by positivity : 0 ≤ (rad r : ℝ))
  convert h using 1
  ring

/-- A squarefree factor of n also divides rad(n). -/
theorem squarefree_dvd_rad {a n : ℕ} (ha : Squarefree a) (hn : n ≠ 0) (han : a ∣ n) :
    a ∣ rad n := by
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime
  · intro p hp
    exact Finset.dvd_prod_of_mem (f := id) (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans han, hn⟩)

/-- The remaining Rankin mass is summable, without a PNT or an Euler-product
estimate: write n=b^2*a with a squarefree and compare with two p-series. -/
theorem summable_rad_weight :
    Summable (fun n : ℕ => (n : ℝ)^(-3/4 : ℝ)/(rad n : ℝ)) := by
  choose a b hab hsf using Nat.sq_mul_squarefree
  have hinj : Function.Injective (fun n => (a n, b n)) := by
    intro n m h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    dsimp only at ha hb
    rw [← hab n, ← hab m, ha, hb]
  have haSum : Summable (fun a : ℕ => (a : ℝ)^(-7/4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hbSum : Summable (fun b : ℕ => (b : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor := (haSum.mul_of_nonneg hbSum (by intro n; positivity)
    (by intro n; positivity)).comp_injective hinj
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hmajor
  intro n
  change (n : ℝ)^(-3/4 : ℝ)/(rad n : ℝ) ≤
    (a n : ℝ)^(-7/4 : ℝ)*(b n : ℝ)^(-3/2 : ℝ)
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (-3/4 : ℝ) ≠ 0), zero_div]
    positivity
  have han : a n ∣ n := by
    exact ⟨(b n)^2, by simpa only [mul_comm] using (hab n).symm⟩
  have har : a n ≤ rad n := Nat.le_of_dvd (rad_pos n) (squarefree_dvd_rad (hsf n) hn han)
  have ha0 : 0 < (a n : ℝ) := by exact_mod_cast (hsf n).ne_zero.bot_lt
  calc
    _ ≤ (n : ℝ)^(-3/4 : ℝ)/(a n : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) ha0 (by exact_mod_cast har)
    _ = (a n : ℝ)^(-7/4 : ℝ)*(b n : ℝ)^(-3/2 : ℝ) := by
      have hncast : (n : ℝ) = (b n : ℝ)^2*(a n : ℝ) := by exact_mod_cast (hab n).symm
      have hapow : (a n : ℝ)^(-7/4 : ℝ) = (a n : ℝ)^(-3/4 : ℝ)/(a n : ℝ) := by
        rw [show (-7/4 : ℝ) = -3/4-1 by norm_num, Real.rpow_sub_one ha0.ne']
      rw [hncast, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity), hapow]
      norm_num
      ring

def tailConstant : ℝ := ∑' n : ℕ, (n : ℝ)^(-3/4 : ℝ)/(rad n : ℝ)

theorem tailConstant_nonneg : 0 ≤ tailConstant := by
  unfold tailConstant
  exact tsum_nonneg (fun n => by positivity)

/-- A universal averaged Rankin tail: the constant does not depend on g, N,
the finite r cutoff, or Q. It is not yet the error of the mollifier asymptotic. -/
theorem averaged_tail_uniform (N : ℕ) (s : Finset ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hs : ∀ r ∈ s, Q ≤ (r : ℝ)) :
    (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) *
      ∑ r ∈ s.filter (supported g), 1/(r : ℝ)) ≤
      harmonic N * Q^(-1/4 : ℝ) * tailConstant := by
  have h : (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) *
      ∑ r ∈ s.filter (supported g), 1/(r : ℝ)) ≤
      harmonic N * Q^(-1/4 : ℝ) * ∑ r ∈ s, (r : ℝ)^(-3/4 : ℝ)/(rad r : ℝ) := by
    convert averaged_rankin_bound N s Q (1/4) hQ (by norm_num) hs using 1
    norm_num
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by unfold harmonic; positivity)
  exact Summable.sum_le_tsum s (fun n _ => by positivity) summable_rad_weight

def normalizedTail (N K : ℕ) (Q : ℝ) : ℝ :=
  (∑ g ∈ Finset.Icc 1 N, (1/(g : ℝ)) *
    ∑ r ∈ (Finset.Icc 1 K).filter (fun r => supported g r ∧ Q ≤ (r : ℝ)),
      1/(r : ℝ)) / harmonic N

theorem normalizedTail_nonneg (N K : ℕ) (Q : ℝ) : 0 ≤ normalizedTail N K Q := by
  unfold normalizedTail harmonic
  positivity

/-- A genuine bound uniform in BOTH finite cutoffs N and K. -/
theorem normalizedTail_bound (N K : ℕ) (Q : ℝ) (hQ : 0 < Q) :
    normalizedTail N K Q ≤ Q^(-1/4 : ℝ)*tailConstant := by
  by_cases hH : harmonic N = 0
  · simp only [normalizedTail, hH, div_zero]
    exact mul_nonneg (by positivity) tailConstant_nonneg
  have hHpos : 0 < harmonic N := lt_of_le_of_ne (by unfold harmonic; positivity) (Ne.symm hH)
  rw [normalizedTail, div_le_iff₀ hHpos]
  have h := averaged_tail_uniform N ((Finset.Icc 1 K).filter (fun r => Q ≤ (r : ℝ)))
    Q hQ (fun r hr => (Finset.mem_filter.mp hr).2)
  simpa only [Finset.filter_filter, and_comm, mul_assoc, mul_left_comm, mul_comm] using h

open Filter Topology in
theorem normalizedTail_uniform_zero :
    TendstoUniformlyOn (fun (Q : ℝ) (p : ℕ × ℕ) => normalizedTail p.1 p.2 Q)
      (fun _ => 0) atTop Set.univ := by
  have hlim : Tendsto (fun Q : ℝ => Q^(-1/4 : ℝ)*tailConstant) atTop (nhds 0) := by
    simpa only [neg_div, zero_mul] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).mul_const tailConstant
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds heps)] with Q hQ hε
  intro p hp
  rw [dist_comm, Real.dist_eq, sub_zero, abs_of_nonneg (normalizedTail_nonneg _ _ _)]
  exact (normalizedTail_bound _ _ Q hQ).trans_lt hε

#print axioms supported_factored
#print axioms supported_hasSum
#print axioms rankin_point
#print axioms rankin_finite
#print axioms supported_iff_rad_dvd
#print axioms supported_harmonic
#print axioms supported_average
#print axioms supported_average_le
#print axioms supported_mass_le
#print axioms supported_rankin_tail
#print axioms averaged_rankin_bound
#print axioms squarefree_dvd_rad
#print axioms summable_rad_weight
#print axioms averaged_tail_uniform
#print axioms normalizedTail_bound
#print axioms normalizedTail_uniform_zero
end XiPrime8845.SupportTail
