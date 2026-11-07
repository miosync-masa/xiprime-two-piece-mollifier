import PRZZActualSignedBranches

/-! Rounding adapter for the source frequency DH/d in Pratt--Robles,
arXiv:1706.04593v3, Section 3.2.3. The strict source cutoffs are retained.
This does not identify the source choices of D,H or prove their tail bounds. -/
noncomputable section
open Finset
namespace XiPrime8845.PRZZSourceFrequency
open PRZZAStar PRZZActualSignedBranches

theorem indices_empty (N d : ℕ) (D H : ℝ)
    (h : D/(d:ℝ) ≤ 1 ∨ H ≤ 1) : indices N d D H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' := (mem_product.mp hz).2
  have hdelta := (delta_cutoff_iff (D/d) z.2.1).mp (mem_product.mp hz').1
  have hh := (h_cutoff_iff H z.2.2).mp (mem_product.mp hz').2
  rcases h with h | h
  · have hn : z.2.1 ≠ 0 := by intro he; simp [he] at hdelta
    have hi : (1:ℝ) ≤ |(z.2.1:ℝ)| := by
      exact_mod_cast (Int.one_le_abs hn)
    linarith [hdelta.2]
  · have hi : (1:ℝ) ≤ z.2.2 := by exact_mod_cast hh.1
    linarith [hh.2]

theorem literal_zero (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (h : D/(d:ℝ) ≤ 1 ∨ H ≤ 1) :
    literal N d D H T a F1 F2 FM W Phi alpha beta = 0 := by
  simp [literal,indices_empty N d D H h]

/-- The integer envelope costs at most a factor two on a nonempty source
range. This factor is independent of height, modulus and cutoff widths. -/
theorem frequency_rounding (d : ℕ) (D H : ℝ)
    (hD : 1 ≤ D/(d:ℝ)) (hH : 1 ≤ H) :
    1 ≤ frequencyBound d D H ∧
      (frequencyBound d D H:ℝ) ≤ 2*(D/(d:ℝ))*H := by
  have hc : (0:ℤ) ≤ ⌈D/(d:ℝ)⌉ := Int.ceil_nonneg (by linarith)
  have hcast : (⌈D/(d:ℝ)⌉.natAbs:ℝ) = (⌈D/(d:ℝ)⌉:ℝ) := by
    have he : (⌈D/(d:ℝ)⌉.natAbs:ℤ) = ⌈D/(d:ℝ)⌉ := by omega
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
  have hlo : (1:ℝ) ≤ (⌈D/(d:ℝ)⌉.natAbs:ℝ) := by
    rw [hcast]; exact hD.trans (Int.le_ceil _)
  have hhi : (⌈D/(d:ℝ)⌉.natAbs:ℝ) ≤ 2*(D/(d:ℝ)) := by
    rw [hcast]
    have := Int.ceil_lt_add_one (D/(d:ℝ))
    linarith
  have hf : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by simpa using hH)
  constructor
  · unfold frequencyBound
    have hi : 1 ≤ ⌈D/(d:ℝ)⌉.natAbs := by exact_mod_cast hlo
    nlinarith
  · unfold frequencyBound
    push_cast
    exact mul_le_mul hhi (Nat.floor_le (by linarith)) (by positivity) (by linarith)

theorem frequency_source_bound (d : ℕ) (D H Q1 Q2 T lam : ℝ)
    (hD : 1 ≤ D/(d:ℝ)) (hH : 1 ≤ H)
    (hsource : D*H/(d:ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T))) :
    (frequencyBound d D H:ℝ) ≤ (2*lam)*(Q1*Q2/((d:ℝ)^2*T)) := by
  have h := (frequency_rounding d D H hD hH).2
  have he : 2*(D/(d:ℝ))*H = 2*(D*H/(d:ℝ)) := by ring
  rw [he] at h
  nlinarith

theorem empty_or_source_frequency (N d : ℕ) (D H Q1 Q2 T lam : ℝ)
    (hsource : D*H/(d:ℝ) ≤ lam*(Q1*Q2/((d:ℝ)^2*T))) :
    indices N d D H = ∅ ∨
      (1 ≤ frequencyBound d D H ∧
        (frequencyBound d D H:ℝ) ≤ (2*lam)*(Q1*Q2/((d:ℝ)^2*T))) := by
  by_cases h : D/(d:ℝ) ≤ 1 ∨ H ≤ 1
  · exact Or.inl (indices_empty N d D H h)
  · push Not at h
    exact Or.inr ⟨(frequency_rounding d D H h.1.le h.2.le).1,
      frequency_source_bound d D H Q1 Q2 T lam h.1.le h.2.le hsource⟩

theorem log_scale_of_power_bounds (T M L : ℝ) (hT : 0 < T)
    (hlo : T^(-L) ≤ M) (hhi : M ≤ T^L) :
    |Real.log M| ≤ L*Real.log T := by
  have hM : 0 < M := (Real.rpow_pos_of_pos hT _).trans_le hlo
  have ha := Real.log_le_log (Real.rpow_pos_of_pos hT (-L)) hlo
  have hb := Real.log_le_log hM hhi
  rw [Real.log_rpow hT] at ha hb
  exact abs_le.mpr ⟨by linarith, hb⟩

/-- One polynomial-scale bound for M supplies every retained row's
logarithmic scale condition; the row index itself costs only log T. -/
theorem row_log_scale (N l : ℕ) (T M L : ℝ)
    (hM : |Real.log M| ≤ L*Real.log T)
    (hl : (2:ℝ)^l ≤ N) (hNT : (N:ℝ) ≤ T) :
    |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ (L+1)*Real.log T := by
  have hp : (0:ℝ) < (2:ℝ)^l := by positivity
  have ho : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
  rw [abs_of_nonneg (Real.log_nonneg ho)]
  have hh := Real.log_le_log hp (hl.trans hNT)
  linarith

#print axioms row_log_scale
#print axioms log_scale_of_power_bounds
#print axioms empty_or_source_frequency
#print axioms indices_empty
#print axioms literal_zero
#print axioms frequency_rounding
#print axioms frequency_source_bound
end XiPrime8845.PRZZSourceFrequency
