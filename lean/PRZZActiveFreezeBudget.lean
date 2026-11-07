import PRZZPrefactorMass
import PRZZOptimalOuter

/-! Prune the actual prefactor before paying its analytic cost. In
particular, incompatible cutoff boxes contribute exactly zero, rather
than being charged the positive budget of an unrelated dyadic box.
The spatial-scale summation is not asserted to be bounded here. -/
noncomputable section
open scoped BigOperators
open Set Complex
namespace XiPrime8845.PRZZActiveFreezeBudget
open PRZZPrefactorMass PRZZFreezeScales
set_option maxHeartbeats 4000000

def active (N d j l : ℕ) (D H : ℝ) (F1 F2 : ℝ → ℂ) : Finset PRZZAStar.Index := by
  classical
  exact (localIndices N d j l D H).filter (fun z =>
    F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0)

/-- Exact pruning, with no assumption on the arithmetic coefficients. -/
theorem prune (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) :
    (∑ z ∈ localIndices N d j l D H,
      ‖PRZZAStar.prefactor a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) =
    ∑ z ∈ active N d j l D H F1 F2,
      ‖PRZZAStar.prefactor a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ := by
  classical
  rw [active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h1 : F1 ((d:ℝ)*z.1.1) = 0
  · simp [h1,PRZZAStar.prefactor]
  · by_cases h2 : F2 ((d:ℝ)*z.1.2) = 0
    · simp [h2,PRZZAStar.prefactor]
    · simp [h1,h2]

/-- The same nonzero pair supplies both scale comparisons. It is not
legitimate to use witnesses from two independently enlarged boxes. -/
theorem active_scales (N d j l : ℕ) (D H Q V : ℝ) (F1 F2 : ℝ → ℂ)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (z : PRZZAStar.Index) (hz : z ∈ active N d j l D H F1 F2) :
    Q ≤ 4*(d:ℝ)*(2:ℝ)^j ∧ (d:ℝ)*(2:ℝ)^l ≤ 3*V := by
  have h := Finset.mem_filter.mp hz
  have hp := Finset.mem_filter.mp (Finset.mem_product.mp h.1).1
  have hc := Finset.mem_product.mp hp.1
  have hu := (PRZZDyadic.mem_cell N j z.1.1).mp hc.1
  have hv := (PRZZDyadic.mem_cell N l z.1.2).mp hc.2
  have huhi : (z.1.1:ℝ) ≤ 2*(2:ℝ)^j := by
    have hh : (z.1.1:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast hu.2.2
    rw [pow_succ] at hh
    linarith
  have hvlo : (2:ℝ)^l ≤ z.1.2 := by exact_mod_cast hv.2.1
  have h1 := (hs1 h.2.1).1
  have h2 := (hs2 h.2.2).2
  have hd : (0:ℝ) ≤ d := by positivity
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left huhi hd,
    mul_le_mul_of_nonneg_left hvlo hd]

/-- A surviving source frequency also supplies the lower spatial scale.
This is the missing coupling between M and the Delta cutoff. -/
theorem active_spatial_lower (N d j l : ℕ) (T M Q eps H : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 0 < T)
    (z : PRZZAStar.Index)
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) H F1 F2) :
    (d:ℝ)*T^(1-eps) < M*Q := by
  have h := Finset.mem_filter.mp hz
  have hw := Finset.mem_product.mp (Finset.mem_product.mp h.1).2
  have hh := (Finset.mem_filter.mp hw.1).2
  have hn : z.2.1 ≠ 0 := by intro he; simp [he] at hh
  have hi : (1:ℝ) ≤ |(z.2.1:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hb : (1:ℝ) < PRZZSourceCutoffs.deltaCutoff T M Q eps/d := hi.trans_lt hh.2
  unfold PRZZSourceCutoffs.deltaCutoff at hb
  have ht : 0 < T^(1-eps) := Real.rpow_pos_of_pos hT _
  have hb' := (lt_div_iff₀ hd0).mp hb
  have hb'' := (lt_div_iff₀ ht).mp hb'
  nlinarith

/-- After pruning, the dyadic ratio in the analytic denominator can be
replaced by the actual two cutoff scales, uniformly in j and l. -/
theorem active_floor (N d j l : ℕ) (D H M Q V : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hM : 0 < M) (hV : 0 < V)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (z : PRZZAStar.Index) (hz : z ∈ active N d j l D H F1 F2) :
    Real.pi*M^2*Q/(48*V) ≤ productFloor M j l := by
  obtain ⟨h1,h2⟩ := active_scales N d j l D H Q V F1 F2 hs1 hs2 z hz
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hj : (0:ℝ) < (2:ℝ)^j := by positivity
  have hl : (0:ℝ) < (2:ℝ)^l := by positivity
  have hh : Q*(2:ℝ)^l ≤ 12*V*(2:ℝ)^j := by
    have ha := mul_le_mul_of_nonneg_right h1 hl.le
    have hb := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4*(2:ℝ)^j by positivity)
    nlinarith
  unfold productFloor
  apply (div_le_div_iff₀ (by positivity : 0 < 48*V) (by positivity : 0 < 4*(2:ℝ)^l)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*Real.pi*M^2 by positivity)]

/-- The actual analytic cost no longer sees an incompatible j,l ratio.
Both M and its nonempty-frequency lower bound must still be summed. -/
theorem active_cost (N d j l : ℕ) (D H T M Q V eps : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hV : 0 < V)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (z : PRZZAStar.Index) (hz : z ∈ active N d j l D H F1 F2) :
    sourceCost T M eps j l ≤
      (ratioCap T eps+2*T*(ratioCap T eps)^2)*(2*T)^2/
        (Real.pi*M^2*Q/(48*V))^2 := by
  have hf := active_floor N d j l D H M Q V F1 F2 hd hM hV hs1 hs2 z hz
  have hpos : 0 < Real.pi*M^2*Q/(48*V) := by positivity
  unfold sourceCost
  apply div_le_div_of_nonneg_left (by unfold ratioCap; positivity) (by positivity)
  nlinarith

def mass (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ z ∈ localIndices N d j l D H,
    ‖PRZZAStar.prefactor a F1 F2 d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖

/-- The indicator in the corrected scalar budget is supplied by the
literal cutoff values, not by a hypothesis asserting a row estimate. -/
def charge (N d j l : ℕ) (D H T M eps : ℝ) (F1 F2 : ℝ → ℂ) : ℝ := by
  classical
  exact if (active N d j l D H F1 F2).Nonempty then
    sourceCost T M eps j l*(frequencies d D H).card/d else 0

theorem active_row_bound (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l : ℕ)
      (D H T M Q V S eps : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      sourceCost T M eps j l*mass N d j l D H
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
        alpha beta ≤
      C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
        charge N d j l D H T M eps
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) := by
  classical
  obtain ⟨C,hC,hh⟩ := local_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N d j l D H T M Q V S eps alpha beta hN hd hNT hT hL hS ha hb
  by_cases hn : (active N d j l D H
      (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)).Nonempty
  · rw [charge,if_pos hn]
    have hm := hh js N d j l T Q V S D H alpha beta hN hd hNT hL hS ha hb
    exact (mul_le_mul_of_nonneg_left hm
      (show 0 ≤ sourceCost T M eps j l by unfold sourceCost ratioCap; positivity)).trans_eq (by ring)
  · rw [charge,if_neg hn]
    unfold mass
    rw [prune,Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

/-- The previous concrete four-fold budget with empty actual rows removed
before the local analytic cost is charged. The remaining spatial moment
is explicit; arbitrary finite sets of spatial scales are still allowed. -/
theorem source_weighted_active_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N : ℕ) (T Q V S eps eH : ℝ)
      (alpha beta : ℂ) (ms : Finset ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ M ∈ ms, ∑ d ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
          sourceCost T M eps j l*mass N d j l
            (PRZZSourceCutoffs.deltaCutoff T M Q eps)
            (PRZZSourceCutoffs.poissonCutoff d T M V eH)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
            alpha beta) ≤
      C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
        (∑ M ∈ ms, ∑ d ∈ Finset.Icc 1 N,
          ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
            charge N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps)
              (PRZZSourceCutoffs.poissonCutoff d T M V eH) T M eps
              (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)) := by
  obtain ⟨C,hC,hh⟩ := active_row_bound F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N T Q V S eps eH alpha beta ms hN hNT hT hL hS ha hb
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  exact hh js N d j l _ _ T M Q V S eps alpha beta hN (Finset.mem_Icc.mp hd).1
    hNT hT hL hS ha hb

/-- The sixth-power error fits the published target on the entire
4/7 range, before any logarithmic slack is spent. -/
theorem sixth_power_target (N T : ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hscale : N ≤ T^(4/7:ℝ)) :
    N^6/T^3 ≤ PRZZOptimalPowers.target N T := by
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hp : N^(17/4:ℝ) ≤ T^3 := by
    calc
      _ ≤ (T^(4/7:ℝ))^(17/4:ℝ) := Real.rpow_le_rpow hn.le hscale (by norm_num)
      _ = T^(17/7:ℝ) := by rw [← Real.rpow_mul ht.le]; norm_num
      _ ≤ T^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T^3 := Real.rpow_natCast T 3
  have he : N^6 = N^(7/4:ℝ)*N^(17/4:ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num [Real.rpow_natCast]
  apply (div_le_iff₀ (by positivity : 0 < T^3)).mpr
  rw [he]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- Fixed logarithmic losses on the sixth-power contribution consume only
the declared strict height slack. No row-mass premise is hidden here. -/
theorem sixth_log_absorbed (m : ℕ) (a delta : ℝ) (hmargin : a < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 1 ≤ N → 1 ≤ T → N ≤ T^(4/7:ℝ) →
      T^a*(Real.log T)^m*(N^6/T^3) ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hh⟩ := PRZZOptimalOuter.power_log_absorbed m a delta hmargin
  refine ⟨C,hC,?_⟩
  intro N T hN hT hscale
  exact mul_le_mul (hh T hT) (sixth_power_target N T hN hT hscale)
    (by positivity) (by positivity)

theorem cost_double (T M eps : ℝ) (j l : ℕ) :
    sourceCost T (2*M) eps j l = sourceCost T M eps j l/16 := by
  unfold sourceCost productFloor
  ring

/-- A genuine dyadic spatial family pays a geometric moment, not its
cardinality. The estimate is uniform in the truncation K. The starting
scale remains explicit so that active_spatial_lower can be used first. -/
theorem spatial_cost_sum (T M eps : ℝ) (j l K : ℕ) (hT : 0 < T) :
    (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l) ≤
      (16/15:ℝ)*sourceCost T M eps j l := by
  have he (K : ℕ) :
      (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l)+
        (16/15:ℝ)*sourceCost T ((2:ℝ)^K*M) eps j l =
        (16/15:ℝ)*sourceCost T M eps j l := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ,pow_succ,
        show (2:ℝ)^K*2*M = 2*((2:ℝ)^K*M) by ring,cost_double]
      linarith
  have hn : 0 ≤ sourceCost T ((2:ℝ)^K*M) eps j l := by
    unfold sourceCost ratioCap; positivity
  linarith [he K]

/-- Integer rounding costs only an absolute factor on a surviving
frequency range. Both signs of Delta and the strict h cutoff are kept. -/
theorem frequency_count (d : ℕ) (D H : ℝ) (hD : 1 ≤ D/(d:ℝ)) (hH : 0 ≤ H) :
    ((frequencies d D H).card:ℝ) ≤ 5*(D/(d:ℝ))*H := by
  classical
  let c : ℤ := ⌈D/(d:ℝ)⌉
  have hc : 0 ≤ c := Int.ceil_nonneg (by linarith)
  have hi : ((Finset.Icc (-c) c).card:ℝ) = 2*(c:ℝ)+1 := by
    have hn : (Finset.Icc (-c) c).card = (2*c+1).toNat := by simp [Int.card_Icc]; congr 1; ring
    rw [hn]
    have hh : ((2*c+1).toNat:ℤ) = 2*c+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hh
  have hdelt : (((Finset.Icc (-c) c).filter
      (fun delta : ℤ => 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d)).card:ℝ) ≤ 5*(D/d) := by
    have hh : (((Finset.Icc (-c) c).filter
        (fun delta : ℤ => 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d)).card:ℝ) ≤
        (Finset.Icc (-c) c).card := by exact_mod_cast Finset.card_filter_le _ _
    rw [hi] at hh
    have hceil := Int.ceil_lt_add_one (D/(d:ℝ))
    change (c:ℝ) < _ at hceil
    linarith
  have hh : (((Finset.Icc 1 ⌊H⌋₊).filter (fun h : ℕ => (h:ℝ) < H)).card:ℝ) ≤ H := by
    have hb : ((Finset.Icc 1 ⌊H⌋₊).filter (fun h : ℕ => (h:ℝ) < H)).card ≤ ⌊H⌋₊ := by
      simpa using Finset.card_filter_le (Finset.Icc 1 ⌊H⌋₊) (fun h : ℕ => (h:ℝ) < H)
    exact (by exact_mod_cast hb : (((Finset.Icc 1 ⌊H⌋₊).filter
      (fun h : ℕ => (h:ℝ) < H)).card:ℝ) ≤ ⌊H⌋₊).trans (Nat.floor_le hH)
  unfold frequencies
  rw [Finset.card_product,Nat.cast_mul]
  exact mul_le_mul hdelt hh (by positivity) (by linarith)

/-- For an actual surviving row, substitute the source cutoffs into the
integer count. Its M dependence cancels before the spatial sum is taken. -/
theorem active_source_count (N d j l : ℕ) (T M Q V eps eH : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hV : 0 ≤ V)
    (z : PRZZAStar.Index)
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps)
      (PRZZSourceCutoffs.poissonCutoff d T M V eH) F1 F2) :
    ((frequencies d (PRZZSourceCutoffs.deltaCutoff T M Q eps)
      (PRZZSourceCutoffs.poissonCutoff d T M V eH)).card:ℝ) ≤
      5*T^(eps+eH)*(Q*V/((d:ℝ)^2*T)) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 < T^(1-eps) := Real.rpow_pos_of_pos hT _
  have hlo := active_spatial_lower N d j l T M Q eps _ F1 F2 hd hT z hz
  have hD : 1 ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d := by
    unfold PRZZSourceCutoffs.deltaCutoff
    apply le_of_lt
    apply (lt_div_iff₀ hd0).mpr
    apply (lt_div_iff₀ ht).mpr
    simpa only [one_mul] using hlo
  have hH : 0 ≤ PRZZSourceCutoffs.poissonCutoff d T M V eH := by
    unfold PRZZSourceCutoffs.poissonCutoff; positivity
  calc
    _ ≤ 5*(PRZZSourceCutoffs.deltaCutoff T M Q eps/d)*
        PRZZSourceCutoffs.poissonCutoff d T M V eH := frequency_count d _ _ hD hH
    _ = 5*(PRZZSourceCutoffs.deltaCutoff T M Q eps*
        PRZZSourceCutoffs.poissonCutoff d T M V eH/d) := by ring
    _ = _ := by
      rw [PRZZSourceCutoffs.cutoff_product d T M Q V eps eH hd0 hT hM]
      ring

/-- Sum the actual, empty-row-pruned charge over a dyadic spatial family.
The Delta/h integer count has already been substituted, and K disappears.
The initial spatial scale must next be chosen from the active lower bound. -/
theorem dyadic_charge_sum (N d j l K : ℕ) (T M Q V eps eH : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 ≤ Q) (hV : 0 ≤ V) :
    (∑ k ∈ Finset.range K,
      charge N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
        (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
        T ((2:ℝ)^k*M) eps F1 F2) ≤
      (16/15:ℝ)*sourceCost T M eps j l*
        (5*T^(eps+eH)*(Q*V/((d:ℝ)^2*T))/d) := by
  classical
  let R := 5*T^(eps+eH)*(Q*V/((d:ℝ)^2*T))/d
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb (k : ℕ) :
      charge N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
        (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
        T ((2:ℝ)^k*M) eps F1 F2 ≤ sourceCost T ((2:ℝ)^k*M) eps j l*R := by
    have hc : 0 ≤ sourceCost T ((2:ℝ)^k*M) eps j l := by
      unfold sourceCost ratioCap; positivity
    unfold charge
    split_ifs with hn
    · obtain ⟨z,hz⟩ := hn
      have hh := active_source_count N d j l T ((2:ℝ)^k*M) Q V eps eH
        F1 F2 hd hT (by positivity) hV z hz
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hc)
        (by positivity)).trans_eq (by dsimp [R]; ring)
    · exact mul_nonneg hc hR
  calc
    _ ≤ ∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l*R :=
      Finset.sum_le_sum (fun k _ => hb k)
    _ = (∑ k ∈ Finset.range K, sourceCost T ((2:ℝ)^k*M) eps j l)*R := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (spatial_cost_sum T M eps j l K hT) hR

#print axioms prune
#print axioms active_scales
#print axioms active_spatial_lower
#print axioms active_floor
#print axioms active_cost
#print axioms active_row_bound
#print axioms source_weighted_active_mass
#print axioms sixth_power_target
#print axioms sixth_log_absorbed
#print axioms cost_double
#print axioms spatial_cost_sum
#print axioms frequency_count
#print axioms active_source_count
#print axioms dyadic_charge_sum
end XiPrime8845.PRZZActiveFreezeBudget
