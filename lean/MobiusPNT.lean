/-
Selected proofs ported from AlexKontorovich/PrimeNumberTheoremAnd,
commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (v4.32.2),
PrimeNumberTheoremAnd/Consequences.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Bundled license: xiprime-two-piece-mollifier/licenses/PNTPlus-Apache-2.0.txt.
Modified 2026 by MASAMICHI IIZUMI: selected only Mobius consequences,
removed blueprint tooling, localized declarations, replaced WeakPNT'' by
the pinned AF MediumPNT, and adapted proofs to Lean v4.33.0-rc2.
-/
import Mathlib
import Zeta23.FromPNTPlus.MediumPNT

/-! Qualitative Mobius cancellation from the already ported AF PNT.
No new axiom, toolchain change, or zero-counting claim is introduced. -/
set_option lang.lemmaCmd true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section
namespace XiPrime8845.MobiusPNT
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

abbrev Psi (x : ℝ) : ℝ := Chebyshev.psi x
def M (x : ℝ) : ℝ := ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
      μ d * Int.fract (N / d : ℚ) := calc
    (1 : ℚ) = ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, μ d := by
      have (x : ℕ) (hx : x ∈ Ioc 0 N) : ∑ d ∈ divisors x, μ d = if x = 1 then 1 else 0 := by
        rw [mem_Ioc] at hx
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      rw [sum_congr rfl this]
      simp [hN.ne']
    _ = ∑ d ∈ range (N + 1), μ d * (N / d : ℕ) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (add_one_pos _),
        sum_insert (by simp), Ico_add_one_add_one_eq_Ioc]
      simp
    _ = ∑ d ∈ range (N + 1), (μ d : ℚ) * ⌊(N / d : ℚ)⌋ := by
      simp_rw [Rat.floor_natCast_div_natCast]
      simp [← Int.natCast_ediv]
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
        μ d * Int.fract (N / d : ℚ) := by
      simp_rw [sum_mul, ← sum_sub_distrib, mul_comm_div, ← mul_sub, Int.self_sub_fract]
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d ∈ range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by simp), sum_insert (by simp),
      ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add,
      Finset.Ico_add_one_right_eq_Icc, zero_add]
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right hN, sum_insert (by simp), div_self (by simp; grind), Int.fract_one,
      mul_zero, zero_add]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      refine mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      exact abs_moebius_le_one
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    simp [cast_sub (one_le_iff_ne_zero.mpr hN.ne')]

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff₀, div_le_iff₀, cast_pos.mpr hN]
  <;> linarith [h_bound.left]



lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  norm_cast
  convert ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum μ ⌊x⌋₊ |>.symm using 1
  · rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp)]
    simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, div_zero, Int.floor_zero, mul_zero,
      zero_add, Int.natCast_ediv]
    refine sum_congr rfl fun n hn ↦ ?_
    congr
    norm_cast
    rw [← floor_div_natCast, Int.natCast_floor_eq_floor]
    positivity
  · simpa [moebius_mul_coe_zeta, one_apply]


noncomputable def mu_log : ArithmeticFunction ℝ :=
    ⟨(fun n ↦ μ n * ArithmeticFunction.log n), (by simp)⟩

lemma mu_log_apply (n : ℕ) : mu_log n = μ n * ArithmeticFunction.log n := by
  rfl

lemma mu_log_mul_zeta : mu_log * ArithmeticFunction.zeta = -Λ := by
  ext n
  rw [coe_mul_zeta_apply]
  simp_rw [mu_log_apply]
  rw [sum_moebius_mul_log_eq]
  rfl

lemma mu_log_eq_mu_mul_neg_lambda : mu_log = μ * -Λ := by
  rw [← mu_log_mul_zeta, mul_comm, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x/k) := by
  rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp), ← add_sum_Ioc_eq_sum_Icc (by simp)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero, log_zero, mul_zero,
    zero_add, div_zero, zero_mul]
  simp_rw [← log_apply, ← mu_log_apply, mu_log_eq_mu_mul_neg_lambda]
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [ArithmeticFunction.neg_apply, sum_neg_distrib]
  ring_nf
  congr 2
  unfold Psi
  congr
  rw [← floor_div_natCast]
  rfl

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Psi (x/k)) := by
  have h_log_identity : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k) = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    rw [Finset.sum_mul _ _ _]
    rw [← Finset.sum_sub_distrib] ; refine Finset.sum_congr rfl fun i hi => ?_ ; by_cases hi' : i = 0 <;> simp +decide [*, Real.log_div, ne_of_gt (zero_lt_one.trans_le hx)] ; ring
  generalize_proofs at *
  have h_log_identity' : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k = -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
    convert sum_mu_Lambda x using 1
  have h_psi_identity :
      (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k)) =
        -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    simpa [neg_neg] using (congrArg Neg.neg h_log_identity').symm
  unfold M
  symm
  calc
    (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k))) =
        (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [h_log_identity]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          (-∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) := by
          simp [h_psi_identity]
    _ = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x := by ring

noncomputable def R (x : ℝ) : ℝ := Psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x)^((1:ℝ)/10)))
      atTop (nhds 0) := by
    have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).comp Real.tendsto_log_atTop
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop hc)
    change Tendsto (fun x : ℝ => Real.exp (-(c * (Real.log x)^((1:ℝ)/10)))) atTop (nhds 0) at h
    simpa only [neg_mul] using h
  have hsmall : (fun x : ℝ => x * Real.exp (-c * (Real.log x)^((1:ℝ)/10)))
      =o[atTop] id := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · apply hexp.congr'
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      simp only [id_eq, mul_div_cancel_left₀ _ hx.ne']
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx hzero
      exact (hx.ne' hzero).elim
  change (Chebyshev.psi - id) =o[atTop] id
  exact hpnt.trans_isLittleO hsmall

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  have h_abs : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
    intros x hx
    have h_sum : ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) / n = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n := by
      rw [Finset.range_eq_Ico] ; rfl
    have := sum_mobius_div_self_le (⌊x⌋₊ + 1) ; simp_all +decide [Finset.sum_range_succ']
    norm_cast at *
  rw [Asymptotics.isBigO_iff]
  use 1; filter_upwards [Filter.eventually_ge_atTop 1] with x hx; simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm]
  simpa only [← Finset.mul_sum _ _ _, abs_mul] using mul_le_of_le_one_right (abs_nonneg x) (h_abs x hx)

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  have h_sum_log : ∀ x : ℝ, 1 ≤ x → |∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k)| ≤ 2 * x := by
    have h_sum_log_le_x : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) ≤ x := by
      intro x hx
      have h_sum_log : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (k : ℝ)) ≤ Real.log (x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊) := by
        rw [← Real.log_prod]
        · norm_num [Finset.prod_div_distrib]
          erw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
        · exact fun n hn => div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr <| by linarith [Finset.mem_Icc.mp hn])
      have h_exp_bound : x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊ ≤ Real.exp x := by
        have h_term : x ^ ⌊x⌋₊ / (⌊x⌋₊! : ℝ) ≤ ∑' k : ℕ, x ^ k / (k ! : ℝ) := by
          exact Summable.le_tsum (show Summable _ from Real.summable_pow_div_factorial x) ⌊x⌋₊ (fun _ _ => by positivity)
        simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using h_term
      exact h_sum_log.trans (Real.log_le_iff_le_exp (by positivity) |>.2 h_exp_bound)
    intros x hx
    have h_sum_eq : ∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) := by
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
    rw [abs_of_nonneg] <;> linarith [h_sum_log_le_x x hx, show 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| by linarith [Finset.mem_Icc.mp ‹_›]] ; linarith [Nat.floor_le <| show 0 ≤ x by linarith, show (↑‹ℕ› : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp ‹_› |>.2]]
  rw [Asymptotics.isBigO_iff]
  exact ⟨2, Filter.eventually_atTop.mpr ⟨1, fun x hx => le_trans (h_sum_log x hx) (by norm_num [abs_of_nonneg (by linarith : 0 ≤ x)])⟩⟩

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  have hR_bounded : BddAbove (Set.image (fun y => |R y|) (Set.Icc 0 K)) := by
    have hR_bounded : ∀ y ∈ Set.Icc 0 K, |R y| ≤ ∑ p ∈ Iic ⌊K⌋₊, log p + K := by
      intro y hy
      simp only [R, Psi, Chebyshev.psi_eq_sum_Icc]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · refine le_trans (sub_le_self _ hy.1) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr <| Nat.floor_mono hy.2) fun ?_ ?_ ?_ => ?_) ?_
        · exact vonMangoldt_nonneg
        · refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hK
          exact vonMangoldt_le_log
      · refine le_trans ?_ (le_add_of_nonneg_left ?_)
        · exact le_trans (sub_le_self _ <| Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) hy.2
        · exact Finset.sum_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact ⟨_, Set.forall_mem_image.2 hR_bounded⟩
  exact ⟨hR_bounded.choose, fun y hy => hR_bounded.choose_spec <| Set.mem_image_of_mem _ hy⟩

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
    have h_sum_bound : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) + C * ⌊x⌋₊ := by
      have h_sum_bound : ∀ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x / k + C := by
        exact fun k hk => by simpa only [mul_div_assoc] using! h (x / k) (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), show (k : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp hk |>.2])
      convert! Finset.sum_le_sum h_sum_bound using 1 ; norm_num [div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_comm]
    have h_harmonic : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
      intro n _hn
      have h := harmonic_le_one_add_log n
      simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div, add_comm, add_left_comm, add_assoc] using h
    have h_harmonic_x :
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) ≤ Real.log x + 1 := by
      refine (h_harmonic _ <| Nat.floor_pos.mpr hx).trans ?_
      have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        refine Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr hx) ?_
        exact Nat.floor_le (by positivity)
      simpa using add_le_add_right hlog 1
    have h_term1 : ε * x * (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ))) ≤ ε * x * (Real.log x + 1) := by
      refine mul_le_mul_of_nonneg_left h_harmonic_x ?_
      exact mul_nonneg hε (by positivity)
    have h_term2 : C * (⌊x⌋₊ : ℝ) ≤ C * x := by
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact Nat.floor_le (by positivity)
    exact h_sum_bound.trans (add_le_add h_term1 h_term2)

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  have h_eps : ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ ε * x * Real.log x := by
    intro ε hε_pos
    obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y ≥ A, |R y| ≤ (ε / 2) * y := by
      have := R_isLittleO
      rw [Asymptotics.isLittleO_iff] at this
      norm_num at *
      exact Exists.elim (this (half_pos hε_pos)) fun A hA => ⟨Max.max A 1, by positivity, fun y hy => by simpa only [abs_of_nonneg (by linarith [le_max_right A 1] : 0 ≤ y)] using hA y (le_trans (le_max_left A 1) hy)⟩
    obtain ⟨C_A, hC_A⟩ : ∃ C_A : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ C_A := by
      exact ⟨_, fun y hy => R_locally_bounded A hA.1.le |> Classical.choose_spec |> fun h => h y hy⟩
    have h_sum_bound : ∀ x ≥ max A 2, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ (ε / 2) * x * (Real.log x + 1) + C_A * x := by
      intros x hx
      have h_sum_bound : ∀ y ≥ 1, |R y| ≤ (ε / 2) * y + C_A := by
        intros y hy
        by_cases hyA : y ≥ A
        · exact le_add_of_le_of_nonneg (hA.right y hyA) (by
          exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩))
        · exact le_add_of_nonneg_of_le (by
          positivity) (hC_A y ⟨by
          linarith, by
            linarith⟩)
      have := sum_bounded_of_linear_bound (show 0 ≤ ε / 2 by positivity) (show 0 ≤ C_A by exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩)) (fun y hy => h_sum_bound y hy) x (by linarith [le_max_right A 2]) ; aesop
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, (ε / 2) * (Real.log x + 1) + C_A ≤ ε * Real.log x := by
      exact ⟨Real.exp (2 * (C_A / ε + 1)), fun x hx => by nlinarith [Real.log_exp (2 * (C_A / ε + 1)), Real.log_le_log (by positivity) hx, mul_div_cancel₀ C_A hε_pos.ne']⟩
    exact ⟨Max.max x₀ (Max.max A 2), fun x hx => le_trans (h_sum_bound x (le_trans (le_max_right _ _) hx)) (by nlinarith [hx₀ x (le_trans (le_max_left _ _) hx), le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2, Real.log_nonneg (show x ≥ 1 by linarith [le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2])])⟩
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h_sum_eq : ∀ x : ℝ, x ≥ 1 → (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x / k)|) = (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) := by
      intro x hx
      have h0 : (0 : ℕ) ∈ Finset.Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
      have hI : (Finset.Iic ⌊x⌋₊).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
        ext n
        simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
      rw [← Finset.sum_erase_add (Finset.Iic ⌊x⌋₊) (fun k => |R (x / k)|) h0]
      simp [hI, R, Psi, Chebyshev.psi_eq_sum_Icc]
    rw [Metric.tendsto_nhds]
    simp +zetaDelta only [gt_iff_lt, ge_iff_le, Real.dist_eq, sub_zero, abs_div, abs_mul,
    eventually_atTop] at *
    intro ε hε; obtain ⟨x₀, hx₀⟩ := h_eps (ε / 2) (half_pos hε) ; use Max.max x₀ 2; intro x hx; rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), abs_of_nonneg (by linarith [le_max_right x₀ 2]), abs_of_nonneg (Real.log_nonneg (by linarith [le_max_right x₀ 2]))] ; rw [div_lt_iff₀] <;> nlinarith [hx₀ x (le_trans (le_max_left x₀ 2) hx), Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x), mul_pos (by linarith [le_max_right x₀ 2] : 0 < x) (Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x)), h_sum_eq x (by linarith [le_max_right x₀ 2])]
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' (by nlinarith [Real.log_pos hx])

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → |R y| ≤ ε * y := by
    have := R_isLittleO.def hε
    rw [Filter.eventually_atTop] at this; rcases this with ⟨A, hA⟩ ; exact ⟨Max.max A 1, by positivity, fun y hy => by simpa [abs_of_nonneg (show 0 ≤ y by linarith [le_max_right A 1])] using hA y (le_trans (le_max_left A 1) hy)⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ CA := by
    exact R_locally_bounded A hA.1.le |> fun ⟨CA, hCA⟩ => ⟨CA, fun y hy => hCA y hy⟩
  exact ⟨Max.max CA 0, by positivity, fun y hy => if hy' : y ≤ A then le_trans (hCA y ⟨by linarith, by linarith⟩) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith]) else le_trans (hA.2 y (by linarith)) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith])⟩

lemma sum_abs_R_isLittleO' : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  apply sum_abs_R_isLittleO

lemma M_isLittleO : M =o[atTop] id := by
  have h_identity : ∀ x ≥ 1, M x * Real.log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k)) := by
    exact fun x a => M_log_identity x a
  have h_term1 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) =O[atTop] id := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k) := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * Real.log (x / k)| ≤ Real.log (x / k) := by
        intros k hk
        have h_abs : |(μ k : ℝ)| ≤ 1 := by
          norm_num [ArithmeticFunction.moebius]
          split_ifs <;> norm_num
        by_cases hk0 : k = 0
        · rw [hk0] ; norm_num [ArithmeticFunction.map_zero, Nat.cast_zero, Real.log_zero, div_zero, abs_zero]
        · have hx_pos : 0 < x := by positivity
          have hk_pos : 0 < (k : ℝ) := by positivity
          rw [Real.log_div hx_pos.ne' hk_pos.ne']
          simp only [abs_mul, ge_iff_le]
          simp_all only [ge_iff_le, mem_Iic]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) h_abs) (by rw [abs_of_nonneg] ; exact sub_nonneg_of_le <| Real.log_le_log hk_pos (Nat.cast_le.mpr hk |>.trans (Nat.floor_le hx_pos.le)))
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_log : (fun x => ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k)) =O[atTop] id := by
      convert sum_log_div_isBigO using 1
    rw [Asymptotics.isBigO_iff] at *
    exact ⟨h_sum_log.choose, by filter_upwards [h_sum_log.choose_spec, Filter.eventually_ge_atTop 1] with x hx₁ hx₂ using le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)⟩
  have h_term2 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
    convert sum_mobius_div_isBigO using 1
  have h_term3 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) =o[atTop] (fun x => x * Real.log x) := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)| := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * R (x / k)| ≤ |R (x / k)| := by
        norm_num [abs_mul]
        intro k hk; exact mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_abs_R : (fun x => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * Real.log x) := by
      exact sum_abs_R_isLittleO
    rw [Asymptotics.isLittleO_iff] at *
    intro c hc; filter_upwards [h_sum_abs_R hc, Filter.eventually_ge_atTop 1] with x hx₁ hx₂; exact le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)
  have h_combined : (fun x => M x * Real.log x) =o[atTop] (fun x => x * Real.log x) := by
    have h_combined : (fun x => M x * Real.log x) = (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) := by
      ext x; by_cases hx : 1 ≤ x <;> simp_all +decide only [ge_iff_le, mul_sub, sum_sub_distrib, not_le, Pi.sub_apply]
      · simp +decide [sub_sub, mul_sub, Finset.sum_sub_distrib, Psi, R]
      · unfold M R; norm_num [Nat.floor_eq_zero.mpr hx]
        norm_num [Finset.Iic_eq_Icc]
    rw [h_combined]
    refine Asymptotics.IsLittleO.sub ?_ h_term3
    refine Asymptotics.IsLittleO.sub ?_ ?_
    · refine h_term1.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> norm_num at hx⟩
    · refine h_term2.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> linarith⟩
  rw [Asymptotics.isLittleO_iff_tendsto'] at *
  · refine h_combined.congr' (by filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by rw [mul_div_mul_right _ _ (ne_of_gt <| Real.log_pos hx)] ; rfl)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos (by positivity) <| Real.log_pos hx
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using by nlinarith [Real.log_pos hx]
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'

lemma M_isLittleO' : M =o[atTop] id := by
  exact M_isLittleO


theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by
  have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
    have h_bound : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
      have h_sum : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
          convert! M_isLittleO using 1
        simpa only [Finset.range_eq_Ico] using! h_moebius_sum
      have h_mu_floor : (fun x : ℝ => (μ ⌊x⌋₊ : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
        · refine squeeze_zero_norm (a := fun x : ℝ => 1 / |x|) ?_ ?_
          · intro x; norm_num [abs_div]
            exact mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)
          · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
        · exact ⟨1, by intros; linarith⟩
      simpa [Finset.sum_range_succ] using h_sum.sub h_mu_floor
    convert h_bound using 1
  rw [Asymptotics.isLittleO_iff] at *
  simp_all +decide [Norm.norm]



lemma sum_mobius_floor (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1 := by
  classical
  have h := sum_mobius_mul_floor x hx
  have h0 : (0 : ℕ) ∈ Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
  have hI : (Iic ⌊x⌋₊).erase 0 = Icc 1 ⌊x⌋₊ := by
    ext n
    simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
  rw [← Finset.sum_erase_add (Iic ⌊x⌋₊) (fun n => (μ n : ℝ) * (⌊x / n⌋ : ℝ)) h0] at h
  simpa [hI] using h

lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
      have h_group : ∀ x : ℝ, x ≥ 1 → ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, k * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) := by
        intro x hx
        have h_group : ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ) * k := by
          have h_group : Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊ = Finset.biUnion (Finset.Ico 1 K) (fun k => Finset.Ioc (⌊x / (k + 1 : ℝ)⌋₊) (⌊x / (k : ℝ)⌋₊)) := by
            ext n
            simp only [mem_Ioc, mem_biUnion, mem_Ico]
            constructor
            · intro hn
              refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
              all_goals generalize_proofs at *
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
                exact ⟨by rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)] ; nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by rw [Nat.floor_lt (by positivity)] at *; rw [div_lt_iff₀ (by positivity)] at *; norm_num at *; linarith⟩
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [Nat.lt_floor_add_one (x / n)]
                nlinarith [Nat.lt_floor_add_one (x / n), show (n : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
              · refine Nat.le_floor ?_
                rw [le_div_iff₀] <;> norm_num
                · exact le_trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
                · exact Nat.floor_pos.mpr (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2, div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
            · field_simp
              rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
              refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
              · gcongr ; norm_cast
              · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
          rw [h_group, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
            simp +zetaDelta only [ge_iff_le, mem_Ico, mem_Ioc, mul_eq_mul_left_iff, Int.cast_eq_zero] at *
            rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at *
            exact Or.inl <| mod_cast Int.floor_eq_iff.mpr ⟨by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)], by rw [div_lt_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)]⟩
          · intros k hk l hl hkl; simp_all +decide [Finset.disjoint_left]
            field_simp
            intro a ha₁ ha₂ ha₃; contrapose! hkl
            rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
            rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith }) (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith })
        simpa only [mul_comm, Finset.mul_sum _ _ _] using h_group
      have h_M_x_over_k : ∀ k : ℕ, 1 ≤ k → k < K → (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
        have h_M : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
            refine Asymptotics.IsLittleO.of_norm_left ?_
            simpa only [← Int.norm_cast_real, Int.cast_sum] using mu_pnt.norm_left
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x => x) := by
            simp_all +decide only [ge_iff_le, Finset.sum_range_succ]
            refine h_M.add ?_
            rw [Asymptotics.isLittleO_iff_tendsto] <;> norm_num
            refine squeeze_zero_norm' (a := fun x : ℝ => 1 / |x|) ?_ ?_
            · norm_num [abs_div]
              exact ⟨1, fun x hx => mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)⟩
            · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
          convert! h_M.sub (show (fun x : ℝ => (μ 0 : ℝ)) =o[Filter.atTop] fun x : ℝ => x from ?_) using 2 <;> norm_num [Finset.sum_range_succ']
          erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
        intros k hk_pos hk_lt_K
        have h_M_x_over_k : (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) = (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) - (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k + 1 : ℝ)⌋₊, (μ n : ℝ)) := by
          ext x
          simp only [Pi.sub_apply]
          rw [eq_sub_iff_add_eq']
          simp only [show Finset.Icc (1 : ℕ) (⌊x / (↑k + 1)⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / (↑k + 1)⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / (↑k + 1)⌋₊)),
            show Finset.Icc (1 : ℕ) (⌊x / ↑k⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / ↑k⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / ↑k⌋₊))]
          rw [Finset.sum_Ioc_consecutive] <;> norm_num

          by_cases hx : 0 ≤ x <;> simp_all +decide only [ge_iff_le, floor_div_natCast, not_le]
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            exact Nat.le_floor <| by push_cast; nlinarith [Nat.floor_le (show 0 ≤ x / (k + 1) by positivity), Nat.lt_floor_add_one (x / (k + 1)), mul_div_cancel₀ x (by positivity : (k + 1 : ℝ) ≠ 0)]
          · rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le (by positivity)), Nat.floor_of_nonpos hx.le] ; norm_num
        rw [h_M_x_over_k]
        refine Asymptotics.IsLittleO.sub ?_ ?_
        · field_simp
          refine h_M.comp_tendsto (Filter.tendsto_id.atTop_mul_const (by positivity)) |> fun h => h.trans_isBigO ?_
          exact Asymptotics.isBigO_iff.mpr ⟨(k : ℝ) ⁻¹, Filter.eventually_atTop.mpr ⟨1, fun x hx => by simp +decide ; ring_nf; norm_num [show k ≠ 0 by linarith]⟩⟩
        · have := h_M.comp_tendsto (show Filter.Tendsto (fun x : ℝ => x / (k + 1)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_div_const (by positivity))
          rw [Asymptotics.isLittleO_iff] at *
          intro c hc; filter_upwards [this (show 0 < c * (k + 1) by positivity), Filter.eventually_gt_atTop 0] with x hx₁ hx₂; simp_all +decide only [ge_iff_le, norm_eq_abs, eventually_atTop, Function.comp_apply, norm_div, cast_nonneg,
    zero_le_one, add_nonneg, abs_of_nonneg]
          exact hx₁.trans (by rw [mul_assoc, mul_div_cancel₀ _ (by positivity)])
      have h_sum_o_x : (fun x : ℝ => ∑ k ∈ Finset.Ico 1 K, (k : ℝ) * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ))) =o[atTop] (fun x => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · have h_sum_little_o : ∀ k ∈ Finset.Ico 1 K, Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) / x) Filter.atTop (nhds 0) := by
            intro k hk; specialize h_M_x_over_k k (Finset.mem_Ico.mp hk |>.1) (Finset.mem_Ico.mp hk |>.2) ; rw [Asymptotics.isLittleO_iff_tendsto'] at h_M_x_over_k <;> aesop
          simpa [Finset.sum_div _ _ _, mul_div_assoc] using tendsto_finsetSum _ fun k hk => h_sum_little_o k hk |> Filter.Tendsto.const_mul _
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      exact h_sum_o_x.congr'
        (by filter_upwards [Filter.eventually_ge_atTop 1] with x hx using by rw [h_group x hx])
        (by norm_num)


lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
    have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = (∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) + (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) := by
      erw [Finset.sum_Ioc_consecutive] <;> norm_num
      · rfl
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast hK
    have h_floor : ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋) := by
      rw [Finset.mul_sum _ _ _] ; rw [← Finset.sum_sub_distrib] ; exact Finset.sum_congr rfl fun _ _ => by ring
    have h_bound : |∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ ⌊x / (K : ℝ)⌋₊ := by
      have h_bound : ∀ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, |(μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ 1 := by
        norm_num [abs_mul]
        exact fun n hn₁ hn₂ => mul_le_one₀ (mod_cast by exact abs_moebius_le_one) (abs_nonneg _) (abs_le.mpr ⟨by linarith [Int.fract_nonneg (x / n)], by linarith [Int.fract_lt_one (x / n)]⟩)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h_bound) (by norm_num))
    have h_sum_floor : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = 1 := by
      convert sum_mobius_floor x hx using 1
    cases abs_cases (x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ) ⌋₊, (μ n : ℝ) / n - 1) <;> cases abs_cases (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ) ⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ) ⌋) <;> linarith [abs_le.mp h_bound, Nat.floor_le (show 0 ≤ x / (K : ℝ) by positivity), Nat.lt_floor_add_one (x / (K : ℝ))]



theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    set S : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (μ n : ℝ) / n
    have h_bound : ∀ K : ℕ, 0 < K → ∀ x : ℝ, 1 ≤ x → |S (x / K)| ≤ 1 / K + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x := by
      intros K hK x hx
      have h_approx : |x * S (x / K) - 1| ≤ x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
        convert sum_mobius_div_approx x K hK hx using 1
      rw [abs_le] at *
      ring_nf at *
      constructor <;> nlinarith [inv_pos.2 (by positivity : 0 < x), mul_inv_cancel₀ (by positivity : x ≠ 0), abs_nonneg (∑ n ∈ Finset.Ioc ⌊ (K : ℝ) ⁻¹ * x⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x * (n : ℝ) ⁻¹⌋)]
    have h_tail_zero : ∀ K : ℕ, 0 < K → Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
      intro K hK
      have h_tail_zero : Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
        have := sum_mobius_floor_tail_isLittleO K hK
        rw [Asymptotics.isLittleO_iff_tendsto'] at this
        · simpa [abs_div] using this.abs.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [abs_div, abs_of_nonneg hx.le])
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      convert h_tail_zero using 1
    have h_eps : ∀ ϵ > 0, ∃ Y : ℝ, ∀ y ≥ Y, |S y| < ϵ := by
      intros ϵ hϵ_pos
      obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, 0 < K ∧ 1 / (K : ℝ) < ϵ / 3 := by
        exact ⟨⌊ϵ⁻¹ * 3⌋₊ + 1, Nat.succ_pos _, by rw [div_lt_iff₀] <;> push_cast <;> nlinarith [Nat.lt_floor_add_one (ϵ⁻¹ * 3), mul_inv_cancel₀ hϵ_pos.ne']⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ x ≥ Y, |S (x / K)| < ϵ := by
        have h_tail_zero : Filter.Tendsto (fun x : ℝ => 1 / (K : ℝ) + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds (1 / (K : ℝ))) := by
          simpa using Filter.Tendsto.add (tendsto_const_nhds.add (tendsto_inv_atTop_zero)) (h_tail_zero K hK_pos)
        exact Filter.eventually_atTop.mp (h_tail_zero.eventually (gt_mem_nhds <| by linarith)) |> fun ⟨Y, hY⟩ ↦ ⟨Max.max Y 1, fun x hx ↦ lt_of_le_of_lt (h_bound K hK_pos x <| le_trans (le_max_right _ _) hx) <| hY x <| le_trans (le_max_left _ _) hx⟩
      use Y / K; intros y hy; specialize hY (y * K) (by nlinarith [show (K : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Y (by positivity : (K : ℝ) ≠ 0)]) ; simp_all +decide [ne_of_gt]
    exact Metric.tendsto_atTop.mpr fun ε hε => by simpa using h_eps ε hε
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    convert h_sum_zero using 2 ; erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  simpa [Finset.sum_range_succ] using h_sum_zero.sub (show Filter.Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ) / ⌊x⌋₊) Filter.atTop (nhds 0) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => by positivity) (fun x => by simpa using div_le_div_of_nonneg_right (show |(μ ⌊x⌋₊ : ℝ)| ≤ 1 from mod_cast by { unfold ArithmeticFunction.moebius; aesop }) <| Nat.cast_nonneg _) <| tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop)



set_option pp.fullNames true
#print axioms R_isLittleO
#print axioms M_isLittleO
#print axioms mu_pnt
#print axioms mu_pnt_alt
end XiPrime8845.MobiusPNT

