import WuTrimmedLog

/-! Terminal-anchored interior windows. Counting increments, not mollifier
integrals at different heights, telescope. No zero-counting inequality is
assumed or asserted for the actual xi derivative in this module. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.WuWindowTiling
set_option maxHeartbeats 1000000

def ratio (δ : ℝ) : ℝ := (1+δ)/(2-δ)
def boundary (δ X : ℝ) (j : ℕ) : ℝ := X*ratio δ^j
def height (δ X : ℝ) (j : ℕ) : ℝ := boundary δ X j/(2-δ)
def cell (δ X : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ioc (boundary δ X (j+1)) (boundary δ X j)

theorem ratio_mem (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    0 < ratio δ ∧ ratio δ < 1 := by
  unfold ratio
  exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

theorem boundary_pos (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 < X) (j : ℕ) :
    0 < boundary δ X j := mul_pos hX (pow_pos (ratio_mem δ hδ hd).1 j)

theorem boundary_step (δ X : ℝ) (j : ℕ) :
    boundary δ X (j+1) = boundary δ X j*ratio δ := by simp [boundary,pow_succ,mul_assoc]

theorem boundary_antitone (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 ≤ X) :
    Antitone (boundary δ X) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [boundary_step]
  exact mul_le_of_le_one_right (mul_nonneg hX (pow_nonneg (ratio_mem δ hδ hd).1.le _))
    (ratio_mem δ hδ hd).2.le

theorem height_pos (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 < X) (j : ℕ) :
    0 < height δ X j := div_pos (boundary_pos δ X hδ hd hX j) (by linarith)

theorem height_le (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 ≤ X) (j : ℕ) :
    height δ X j ≤ X := by
  have hb : boundary δ X j ≤ X := by
    simpa [boundary] using boundary_antitone δ X hδ hd hX (Nat.zero_le j)
  apply (div_le_iff₀ (by linarith : 0 < 2-δ)).mpr
  nlinarith

/-- Stop above a fixed low-height threshold, for any terminal height X. -/
theorem exists_cut (δ X K : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hK : 0 < K) :
    ∃ n : ℕ, boundary δ X n ≤ K ∧ ∀ j < n, K < boundary δ X j := by
  have ht : Tendsto (boundary δ X) atTop (nhds 0) := by
    change Tendsto (fun j : ℕ => X*ratio δ^j) atTop (nhds 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (ratio_mem δ hδ hd).1.le
        (ratio_mem δ hδ hd).2).const_mul X
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hK)).exists
  have hex : ∃ n, boundary δ X n ≤ K := ⟨n,hn.le⟩
  exact ⟨Nat.find hex,Nat.find_spec hex,fun j hj => lt_of_not_ge (Nat.find_min hex hj)⟩

/-- The original T parameter for this window is height delta X j. -/
theorem endpoints (δ X : ℝ) (hd : δ < 1/2) (j : ℕ) :
    (1+δ)*height δ X j = boundary δ X (j+1) ∧
      (2-δ)*height δ X j = boundary δ X j := by
  have hn : 2-δ ≠ 0 := by linarith
  rw [boundary_step]
  unfold height ratio
  constructor <;> field_simp

theorem cell_eq (δ X : ℝ) (hd : δ < 1/2) (j : ℕ) :
    cell δ X j = Set.Ioc ((1+δ)*height δ X j) ((2-δ)*height δ X j) := by
  rw [(endpoints δ X hd j).1,(endpoints δ X hd j).2]
  rfl

/-- Half-open cells assign a shared endpoint to just one window. -/
theorem cells_disjoint (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 ≤ X)
    (i j : ℕ) (hij : i < j) : Disjoint (cell δ X i) (cell δ X j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hh := boundary_antitone δ X hδ hd hX (Nat.succ_le_of_lt hij)
  exact (not_lt_of_ge (hj.2.trans hh)) hi.1

theorem cells_union (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hX : 0 ≤ X) (n : ℕ) :
    (⋃ j ∈ range n, cell δ X j) = Set.Ioc (boundary δ X n) X := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    rw [Finset.range_add_one]
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    rw [ih]
    change Set.Ioc (boundary δ X (n+1)) (boundary δ X n) ∪
      Set.Ioc (boundary δ X n) X = _
    apply Set.Ioc_union_Ioc_eq_Ioc
    · exact boundary_antitone δ X hδ hd hX (Nat.le_succ n)
    · simpa [boundary] using boundary_antitone δ X hδ hd hX (Nat.zero_le n)

/-- Applies to any cumulative count; no comparison between eta_T families. -/
theorem increments_telescope (δ X : ℝ) (N : ℝ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, (N (boundary δ X j)-N (boundary δ X (j+1)))) =
      N X-N (boundary δ X n) := by
  induction n with
  | zero => simp [boundary]
  | succ n ih => rw [sum_range_succ,ih]; ring

theorem lengths_telescope (δ X : ℝ) (hd : δ < 1/2) (n : ℕ) :
    (∑ j ∈ range n, (1-2*δ)*height δ X j) = X-boundary δ X n := by
  have he (j : ℕ) : (1-2*δ)*height δ X j = boundary δ X j-boundary δ X (j+1) := by
    rw [← (endpoints δ X hd j).1,← (endpoints δ X hd j).2]
    ring
  simp_rw [he]
  exact increments_telescope δ X id n

/-- A quantitative summation gate for local errors on finitely many cells. -/
theorem sum_error_bound (δ X eps : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hX : 1 ≤ X) (heps : 0 ≤ eps) (n : ℕ) (err : ℕ → ℝ)
    (herr : ∀ j ∈ range n, |err j| ≤ eps*((1-2*δ)*height δ X j)*Real.log X) :
    |∑ j ∈ range n, err j| ≤ eps*X*Real.log X := by
  have hs : (∑ j ∈ range n, eps*((1-2*δ)*height δ X j)*Real.log X) =
      eps*(X-boundary δ X n)*Real.log X := by
    rw [← sum_mul,← mul_sum,lengths_telescope δ X hd n]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum herr).trans
  rw [hs]
  have hb : 0 ≤ boundary δ X n :=
    (boundary_pos δ X hδ hd (lt_of_lt_of_le zero_lt_one hX) n).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : X-boundary δ X n ≤ X) heps)
    (Real.log_nonneg hX)

/-- Converts an eventual local length*log(T) error to the finite global budget.
The caller chooses the threshold before X and stops before leaving it. -/
theorem sum_error_of_local (δ X eps T0 : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hX : 1 ≤ X) (heps : 0 ≤ eps) (hT0 : 1 ≤ T0) (n : ℕ) (err : ℝ → ℝ)
    (herr : ∀ T ≥ T0, |err T| ≤ eps*((1-2*δ)*T)*Real.log T)
    (hstop : ∀ j ∈ range n, T0 ≤ height δ X j) :
    |∑ j ∈ range n, err (height δ X j)| ≤ eps*X*Real.log X := by
  apply sum_error_bound δ X eps hδ hd hX heps n _
  intro j hj
  apply (herr _ (hstop j hj)).trans
  apply mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith [hstop j hj]) (height_le δ X hδ hd (by linarith) j))
  exact mul_nonneg heps (mul_nonneg (by linarith) (by linarith [hstop j hj]))

/-- The original PRZZ supplies the same log cap at every sufficiently high
cell, with that cell's own mollifier and shifts. No expanded support occurs. -/
theorem all_window_log_inputs :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ X : ℝ, ∀ j : ℕ, T0 ≤ height δ X j →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
          WuTrimmedLog.logMean δ ρ (height δ X j) ≤ Real.log WitnessMomentBound.countingCap/2 := by
  obtain ⟨ρ0,hρ0,h⟩ := WuTrimmedLog.logMean_eventually_le
  refine ⟨ρ0,hρ0,?_⟩
  intro δ hδ hd
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (h δ hδ hd)
  refine ⟨max T0 1,le_max_right _ _,?_⟩
  intro X j hj ρ hρ hr
  exact hT0 _ ((le_max_left _ _).trans hj) ρ hρ hr

/-- Finite aggregation of a supplied local counting inequality.
The input is deliberately explicit: it is NOT a proof of the analytic gate. -/
theorem aggregate_counting (δ X B : ℝ) (Ngood Ntotal : ℝ → ℝ) (err : ℕ → ℝ) (n : ℕ)
    (hlocal : ∀ j ∈ range n,
      B*(Ntotal (boundary δ X j)-Ntotal (boundary δ X (j+1)))-err j ≤
        Ngood (boundary δ X j)-Ngood (boundary δ X (j+1))) :
    B*(Ntotal X-Ntotal (boundary δ X n))-(∑ j ∈ range n, err j) ≤
      Ngood X-Ngood (boundary δ X n) := by
  have h := sum_le_sum hlocal
  rw [sum_sub_distrib,← mul_sum,increments_telescope,increments_telescope] at h
  exact h

/-- An all-terminal-height transfer theorem, with the finite low-height
remainder retained. The local analytic counting inequality is still an input.
In particular this does not merely prove a bound on a geometric subsequence. -/
theorem global_counting_bound (δ B eps T0 : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hB : 0 ≤ B) (heps : 0 ≤ eps) (hT0 : 1 ≤ T0)
    (Ngood Ntotal err : ℝ → ℝ) (hgood : ∀ x, 0 ≤ Ngood x) (htotal : Monotone Ntotal)
    (hlocal : ∀ T ≥ T0,
      B*(Ntotal ((2-δ)*T)-Ntotal ((1+δ)*T))-err T ≤
        Ngood ((2-δ)*T)-Ngood ((1+δ)*T))
    (herr : ∀ T ≥ T0, |err T| ≤ eps*((1-2*δ)*T)*Real.log T)
    (X : ℝ) (hX : 1 ≤ X) :
    B*Ntotal X-eps*X*Real.log X-B*Ntotal ((2-δ)*T0) ≤ Ngood X := by
  let K := (2-δ)*T0
  have hK : 0 < K := mul_pos (by linarith) (by linarith)
  obtain ⟨n,hn,hbefore⟩ := exists_cut δ X K hδ hd hK
  have hstop : ∀ j ∈ range n, T0 ≤ height δ X j := by
    intro j hj
    apply (le_div_iff₀ (by linarith : 0 < 2-δ)).mpr
    have hh := (hbefore j (mem_range.mp hj)).le
    simpa only [K,mul_comm] using hh
  have ha := aggregate_counting δ X B Ngood Ntotal (fun j => err (height δ X j)) n (by
    intro j hj
    have hh := hlocal _ (hstop j hj)
    rwa [(endpoints δ X hd j).1,(endpoints δ X hd j).2] at hh)
  have he := sum_error_of_local δ X eps T0 hδ hd hX heps hT0 n err herr hstop
  have he' := (le_abs_self (∑ j ∈ range n, err (height δ X j))).trans he
  have hb := mul_le_mul_of_nonneg_left (htotal hn) hB
  have hg := hgood (boundary δ X n)
  dsimp only [K] at hb
  nlinarith

#print axioms ratio_mem
#print axioms boundary_antitone
#print axioms height_le
#print axioms exists_cut
#print axioms endpoints
#print axioms cell_eq
#print axioms cells_disjoint
#print axioms cells_union
#print axioms increments_telescope
#print axioms lengths_telescope
#print axioms sum_error_bound
#print axioms sum_error_of_local
#print axioms all_window_log_inputs
#print axioms aggregate_counting
#print axioms global_counting_bound
end XiPrime8845.WuWindowTiling
