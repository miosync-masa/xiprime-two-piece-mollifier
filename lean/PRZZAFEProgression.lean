import PRZZAFEIndices
import PRZZActualDirectSum

/-! Exact elimination of the finite k index and cutoff removal for the
grouped actual Gamma-kernel sum. No smooth partition or uniform remainder
estimate is inferred from pointwise convergence. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter Topology
namespace XiPrime8845.PRZZAFEProgression
open PRZZAFEIndices PRZZL1Finite PRZZActualDirectSum
set_option maxHeartbeats 2000000

/-- Congruence plus the original quotient bounds is exactly the k fibre.
The gap is signed; negative Delta is not discarded. -/
theorem quotient_iff (u v m delta k : ℤ) (hv : v ≠ 0) :
    m*u-k*v=delta ↔ v ∣ m*u-delta ∧ k=(m*u-delta)/v := by
  constructor
  · intro h
    have he : m*u-delta = k*v := by linarith
    rw [he]
    exact ⟨⟨k,by ring⟩,by simp [hv]⟩
  · rintro ⟨hd,rfl⟩
    have hh := Int.ediv_mul_cancel hd
    linarith

theorem truncated_iff (L : ℕ) (u v m delta : ℤ) (hv : v ≠ 0) :
    (∃ k ∈ Icc (1:ℤ) L, m*u-k*v=delta) ↔
      v ∣ m*u-delta ∧ 1 ≤ (m*u-delta)/v ∧ (m*u-delta)/v ≤ L := by
  constructor
  · rintro ⟨k,hk,he⟩
    obtain ⟨hd,hq⟩ := (quotient_iff u v m delta k hv).mp he
    exact ⟨hd,by simpa [hq] using (mem_Icc.mp hk).1,by simpa [hq] using (mem_Icc.mp hk).2⟩
  · rintro ⟨hd,hlo,hhi⟩
    exact ⟨_,mem_Icc.mpr ⟨hlo,hhi⟩,(quotient_iff u v m delta _ hv).mpr ⟨hd,rfl⟩⟩

/-- Finite progression rewrite retaining the actual weight f(k). -/
theorem k_sum (L : ℕ) (u v m delta : ℤ) (hv : v ≠ 0) (f : ℤ → ℂ) :
    (∑ k ∈ Icc (1:ℤ) L, if m*u-k*v=delta then f k else 0) =
      if v ∣ m*u-delta ∧ 1 ≤ (m*u-delta)/v ∧ (m*u-delta)/v ≤ L then
        f ((m*u-delta)/v) else 0 := by
  classical
  simp_rw [quotient_iff u v m delta _ hv]
  by_cases hd : v ∣ m*u-delta
  · simp [hd,Finset.sum_ite_eq',mem_Icc]
  · simp [hd]

/-- Removes L for the literal grouped mollified Gamma series, not for a
bare coefficient estimate growing like L^2. N and time remain fixed. -/
theorem grouped_cutoff_removed (N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Tendsto (fun L => ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      term a b alpha beta (actualWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2)
      atTop (nhds ((∑' p : ℕ × ℕ,
        directTerm alpha beta (actualWeight alpha beta) t (p.1+1) (p.2+1)) *
        PRZZ.dirichletPolynomial a N (1/2+t*Complex.I) *
        star (PRZZ.dirichletPolynomial b N (1/2+t*Complex.I)))) := by
  simp_rw [← direct_grouped]
  exact ((actual_cutoff_removed alpha beta ha hb hs T t hT hT' ht ht2).mul_const _).mul_const _

/-- Full analytic coefficient mass, including the Gamma kernel and both
mollifier denominators. The upper bound is independent of L, but remains
dependent on the fixed time and shifts through the absolute Gamma series. -/
theorem grouped_analytic_mass (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖term a b alpha beta (actualWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2‖) ≤
    (∑' p : ℕ × ℕ, ‖directTerm alpha beta (actualWeight alpha beta) t (p.1+1) (p.2+1)‖)*
      (∑ n ∈ Icc 1 N, ‖a n/(n:ℂ)^(1/2+t*Complex.I)‖)*
      (∑ r ∈ Icc 1 N, ‖b r/(r:ℂ)^(1/2+t*Complex.I)‖) := by
  rw [mass_exact]
  simp only [indices,sum_product,term,norm_mul,norm_star]
  have he : (∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L,
      ‖directTerm alpha beta (actualWeight alpha beta) t m k‖) ≤
      ∑' p : ℕ × ℕ, ‖directTerm alpha beta (actualWeight alpha beta) t (p.1+1) (p.2+1)‖ := by
    have pos (f : ℕ → ℝ) (M : ℕ) :
        (∑ n ∈ Icc 1 M, f n) = ∑ n ∈ range M, f (n+1) := by
      induction M with
      | zero => simp
      | succ M ih => rw [sum_Icc_succ_top (by omega),sum_range_succ,ih]
    simp_rw [pos]
    simpa only [sum_product] using
      (actual_summable alpha beta ha hb hs T t hT hT' ht ht2).norm.sum_le_tsum
        (range L ×ˢ range L) (fun p hp => norm_nonneg _)
  calc
    _ = (∑ m ∈ Icc 1 L, ∑ k ∈ Icc 1 L,
        ‖directTerm alpha beta (actualWeight alpha beta) t m k‖)*
        (∑ n ∈ Icc 1 N, ‖a n/(n:ℂ)^(1/2+t*Complex.I)‖)*
        (∑ r ∈ Icc 1 N, ‖b r/(r:ℂ)^(1/2+t*Complex.I)‖) := by
      simp only [mul_assoc,← mul_sum,← sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (sum_nonneg (fun n hn => norm_nonneg _)))
      (sum_nonneg (fun n hn => norm_nonneg _))

/-- A telescoping smooth dyadic cutoff; the seed is fixed before M. -/
def piece (F : ℝ → ℂ) (M x : ℝ) : ℂ := F (x/(2*M))-F (x/M)

theorem piece_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (M : ℝ) :
    ContDiff ℝ ∞ (piece F M) :=
  (hF.comp (contDiff_id.div_const _)).sub (hF.comp (contDiff_id.div_const _))

theorem piece_support (F : ℝ → ℂ) (M : ℝ) (hM : 0 < M)
    (hlo : ∀ x ≤ (1/2:ℝ), F x = 1) (hhi : ∀ x, 1 ≤ x → F x = 0) :
    Function.support (piece F M) ⊆ Set.Icc (M/2) (2*M) := by
  intro x hx
  by_contra hh
  have he : piece F M x = 0 := by
    rcases not_and_or.mp hh with h | h
    · have hx' : x < M/2 := lt_of_not_ge h
      rw [piece,hlo _ ((div_le_iff₀ (by positivity)).mpr (by linarith)),
        hlo _ ((div_le_iff₀ hM).mpr (by linarith)),sub_self]
    · have hx' : 2*M < x := lt_of_not_ge h
      rw [piece,hhi _ ((le_div_iff₀ (by positivity)).mpr (by linarith)),
        hhi _ ((le_div_iff₀ hM).mpr (by linarith)),sub_self]
  exact hx he

theorem piece_telescope (F : ℝ → ℂ) (M x : ℝ) (K : ℕ) :
    (∑ j ∈ range K, piece F ((2:ℝ)^j*M) x) = F (x/((2:ℝ)^K*M))-F (x/M) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ,ih,piece]
    rw [show (2:ℝ)^(K+1)*M = 2*((2:ℝ)^K*M) by rw [pow_succ]; ring]
    ring

/-- Partition unity follows from the two seed plateaus, not from a supplied
sum identity. Choosing the finite scale range remains explicit. -/
theorem piece_sum_one (F : ℝ → ℂ) (M x : ℝ) (K : ℕ) (hM : 0 < M)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (hx : M ≤ x) (hK : x ≤ (2:ℝ)^K*M/2) :
    (∑ j ∈ range K, piece F ((2:ℝ)^j*M) x) = 1 := by
  rw [piece_telescope,hlo _ ((div_le_iff₀ (by positivity)).mpr (by linarith)),
    hhi _ ((le_div_iff₀ hM).mpr (by simpa using hx)),sub_zero]

#print axioms piece_smooth
#print axioms grouped_analytic_mass
#print axioms piece_support
#print axioms piece_telescope
#print axioms piece_sum_one
#print axioms quotient_iff
#print axioms truncated_iff
#print axioms k_sum
#print axioms grouped_cutoff_removed
end XiPrime8845.PRZZAFEProgression
