import PRZZTailSourceFamily

/-! Enlarged source domain for Pratt--Robles 1706.04593v3, section 3.2.
The source permits M <= T^(1+epsilon), not just M <= T. A nonempty
positive-integer cutoff supplies M >= 1/3. Empty lattice rows must be
removed before Poisson, not by declaring individual Fourier terms zero. -/
noncomputable section
namespace XiPrime8845.PRZZExtendedTailDomain
set_option maxHeartbeats 2000000

theorem nonempty_scale (F : ℝ → ℂ) (M : ℝ) (m : ℕ)
    (hs : Function.support F ⊆ Set.Icc (M/2) (3*M))
    (hm : 1 ≤ m) (hf : F m ≠ 0) : 1 ≤ 3*M := by
  have hh := (hs hf).2
  have hn : (1:ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem scales (T M u v t q : ℝ) (hT : 36 ≤ T) (hM : 1 ≤ 3*M)
    (hu : 1 ≤ u) (hv : 0 < v) (hvT : v ≤ T)
    (ht : 0 < t) (htT : t ≤ 2*T) (hq : 0 ≤ q) (hqT : q ≤ T) :
    T^(-(4:ℝ)) ≤ (2*Real.pi*u/(t*v))*(M/2)^2 ∧ q/M ≤ T^(2:ℝ) := by
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hh := PRZZTailSourceFamily.quadratic_scale T (3*M) u v t
    (by linarith) hM hu hv hvT ht htT
  rw [Real.rpow_neg hT0.le,Real.rpow_ofNat] at hh
  constructor
  · rw [Real.rpow_neg hT0.le,Real.rpow_ofNat]
    have h1 : (T^3)⁻¹/9 ≤ (2*Real.pi*u/(t*v))*(M/2)^2 := by nlinarith [hh]
    apply le_trans _ h1
    have he : (T^3)⁻¹/9 = (T/9)*(T^4)⁻¹ := by field_simp <;> ring
    rw [he]
    have hp : 0 ≤ (T^4)⁻¹ := by positivity
    nlinarith
  · rw [Real.rpow_ofNat]
    have hh : q/M ≤ 3*T := (div_le_iff₀ hM0).mpr (by nlinarith)
    exact hh.trans (by nlinarith)

theorem window_log (T M b : ℝ) (hM : 1 ≤ 3*M) (hMT : M ≤ T^b)
    (hb : 0 ≤ b) (hlog : 1 ≤ Real.log T) (hT : 0 < T) :
    |Real.log (M/2)|+|Real.log (3*M)| ≤
      (2*b+Real.log 2+3*Real.log 3)*Real.log T := by
  have hM0 : 0 < M := by linarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlo := Real.log_nonneg hM
  rw [Real.log_mul (by norm_num) hM0.ne'] at hlo
  have hhi := Real.log_le_log hM0 hMT
  rw [Real.log_rpow hT] at hhi
  have hab : |Real.log M| ≤ b*Real.log T+Real.log 3 := by
    apply abs_le.mpr; constructor <;> nlinarith
  rw [Real.log_div hM0.ne' (by norm_num),Real.log_mul (by norm_num) hM0.ne']
  have hleft := abs_sub (Real.log M) (Real.log 2)
  have hright := abs_add_le (Real.log 3) (Real.log M)
  rw [abs_of_nonneg h2] at hleft
  rw [abs_of_nonneg h3] at hright
  nlinarith

theorem shift_envelopes (T M b S r : ℝ) (A B : ℂ)
    (hlog : 1 ≤ Real.log T) (hM : 1 ≤ 3*M) (hMT : M ≤ T^b) (hb : 0 ≤ b) (hT : 0 < T)
    (hA : ‖A‖ ≤ S) (hr : 0 < r) (hsep : r ≤ ‖A+B‖) :
    ‖A/(Real.log T:ℂ)‖ ≤ S ∧
    ‖A/(Real.log T:ℂ)‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤
      S*(2*b+Real.log 2+3*Real.log 3) ∧
    1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ (Real.log T)^2/r^2 := by
  have hL : 0 < Real.log T := by linarith
  have hS : 0 ≤ S := (norm_nonneg _).trans hA
  have he : ‖A/(Real.log T:ℂ)‖ = ‖A‖/Real.log T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  refine ⟨?_,?_,?_⟩
  · rw [he]; exact (div_le_self (norm_nonneg _) hlog).trans hA
  · rw [he]
    calc
      _ ≤ (S/Real.log T)*((2*b+Real.log 2+3*Real.log 3)*Real.log T) := by
        gcongr
        exact window_log T M b hM hMT hb hlog hT
      _ = _ := by field_simp
  · simpa using PRZZJetUniform.shift_cost 0 1 r (Real.log T) A B
      (by norm_num) hr hL.ne' hsep

/-- The actual zero-phase cap, with logarithmic shifts and the source
quadratic argument, is substituted into the cutoff gain. No separate
polynomial cap or local scale comparison is assumed. -/
theorem source_absorbed (C D E : ℕ → ℝ) (a b S r eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ d T M Q q h u v t : ℝ, ∀ alpha beta : ℂ,
      0 < d → 36 ≤ T → 1 ≤ Real.log T → 1 ≤ 3*M → M ≤ T^b →
      0 < Q → 0 ≤ q → q ≤ T → q ≤ 3*Q/d →
      1 ≤ u → 0 < v → v ≤ T → 0 < t → t ≤ 2*T →
      ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      PRZZSourceCutoffs.poissonCutoff d T M Q eH ≤ h →
      PRZZEnvelopeMass.cap C D E a (2*Real.pi*u/(t*v)) M 0
        (|Real.log (M/2)|+|Real.log (3*M)|)
        (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) (n+2)*
        (1+8*T^eD)^2*(q/M)*((1+8*T^eD)*q/(M*h))^n ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := PRZZZeroPhaseBudget.absorbed C D E a S
    (S*(2*b+Real.log 2+3*Real.log 3)) r 4 2 eD eH A hc ha hS hr heD he
  refine ⟨n,K,hK,?_⟩
  intro d T M Q q hcut u v t alpha beta hd hT hlog hM hMT hQ hq hqT hbox
    hu hv hvT ht htT halpha hsep hcutoff
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  have hk : 0 < 2*Real.pi*u/(t*v) := by positivity
  obtain ⟨hz,hP,hs⟩ := shift_envelopes T M b S r alpha beta hlog hM hMT hb (by linarith) halpha hr hsep
  have hc0 := PRZZJetUniform.cap_uniform C D E a (2*Real.pi*u/(t*v)) M 0
    (|Real.log (M/2)|+|Real.log (3*M)|) S (S*(2*b+Real.log 2+3*Real.log 3))
    ((Real.log T)^2/r^2) (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    (n+2) hc hk.le (by norm_num) hS hz hP hs
  have hh0 : 0 < hcut := lt_of_lt_of_le
    (by unfold PRZZSourceCutoffs.poissonCutoff; positivity) hcutoff
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0 (sq_nonneg _))
      (by positivity : 0 ≤ q/M)) (by positivity))
  exact h d T M Q q hcut (2*Real.pi*u/(t*v)) hd (by linarith) (by linarith)
    hQ hq hbox hk hcutoff (scales T M u v t q hT hM hu hv hvT ht htT hq hqT).1
    (scales T M u v t q hT hM hu hv hvT ht htT hq hqT).2

/-- Original positive arithmetic indices after extracting the gcd, and
the actual supported time weight, supply the index/time domain. -/
theorem index_time (d N u v : ℕ) (T t : ℝ) (Phi : ℝ → ℂ)
    (hd : 1 ≤ d) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hvN : d*v ≤ N) (hNT : (N:ℝ) ≤ T) (hT : 0 < T)
    (hs : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) (hf : Phi (t/T) ≠ 0) :
    (1:ℝ) ≤ u ∧ (0:ℝ) < v ∧ (v:ℝ) ≤ T ∧ 0 < t ∧ t ≤ 2*T := by
  have hvle : v ≤ N := (Nat.le_mul_of_pos_left v hd).trans hvN
  have htime := hs hf
  have ht1 : T ≤ t := (le_div_iff₀ hT).mp htime.1 |>.trans' (by simp)
  refine ⟨by exact_mod_cast hu,by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hv),
    (by exact_mod_cast hvle : (v:ℝ) ≤ N).trans hNT,hT.trans_le ht1,?_⟩
  exact (div_le_iff₀ hT).mp htime.2

#print axioms index_time
#print axioms shift_envelopes
#print axioms source_absorbed
#print axioms nonempty_scale
#print axioms scales
#print axioms window_log
end XiPrime8845.PRZZExtendedTailDomain
