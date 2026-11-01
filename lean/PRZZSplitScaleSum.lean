import PRZZInflatedOuter

/-! Small blocks need no balanced DI box. Their absolute supported G mass
is subpower. Large blocks use the inflated seven-term estimate. Block
inequalities and the literal arithmetic decomposition remain explicit. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSplitScaleSum
open PRZZGCoefficient PRZZDISeven
set_option maxHeartbeats 2000000

theorem absolute_mass (js : List ℕ) (k : ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, ∀ d N : ℕ,
      sigma ≤ 0 → 1 ≤ d → 1 ≤ N → ∀ s : Finset ℕ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∑ h ∈ s, |sourceG js k sigma d h|) ≤ C*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨C,hC,hg⟩ := PRZZGAbsorption.sourceG_average_power js k (beta/2) eta (beta/2)
    (by positivity) heta (by positivity)
  refine ⟨C,hC,?_⟩
  intro sigma d N hsig hd hN s hs
  have hp (h : ℕ) (hh : h ∈ s) : 0 < (h:ℝ)^(beta/2) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (hs h hh).1
  have hb : (∑ h ∈ s, |sourceG js k sigma d h|) ≤
      (N:ℝ)^(beta/2)*(∑ h ∈ s, |sourceG js k sigma d h|/(h:ℝ)^(beta/2)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro h hh
    have hn : h ≤ N := by nlinarith [(hs h hh).2.1]
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg h)
      (show (h:ℝ) ≤ (N:ℝ) by exact_mod_cast hn) (by positivity : 0 ≤ beta/2)
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (hp h hh)).mpr (by nlinarith [abs_nonneg (sourceG js k sigma d h)])
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left (hg sigma d N hsig hd hN s hs) (by positivity)).trans_eq
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have he : (N:ℝ)^(beta/2)*(N:ℝ)^(beta/2) = (N:ℝ)^beta := by
    rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ = (C*(d:ℝ)^eta)*((N:ℝ)^(beta/2)*(N:ℝ)^(beta/2)) := by ring
    _ = _ := by rw [he]

theorem mixed_sum (js : List ℕ) (k : ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, ∀ d N : ℕ,
      sigma ≤ 0 → 1 ≤ d → 1 ≤ N → ∀ s : Finset ℕ, ∀ X A V Bs Bl c : ℝ,
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl → 1 ≤ c →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ,
      (∀ h ∈ s, X/h ≤ c → ‖z h‖ ≤ Bs) →
      (∀ h ∈ s, c < X/h → ‖z h‖ ≤ Bl*seven h (E h) A (Y h) V) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        C*(Bs+Bl*c^2*envelope X A V)*(d:ℝ)^eta*(N:ℝ)^beta := by
  classical
  obtain ⟨Cs,hCs,hsmall⟩ := absolute_mass js k eta beta heta hbeta
  obtain ⟨Cl,hCl,hlarge⟩ := PRZZInflatedOuter.source_h_sum js k eta beta heta hbeta
  refine ⟨Cs+Cl,by positivity,?_⟩
  intro sigma d N hsig hd hN s X A V Bs Bl c hX hA hV hBs hBl hc hs E Y hscale z hzS hzL
  let q := fun h : ℕ => X/(h:ℝ) ≤ c
  have ha : ‖∑ h ∈ s.filter q, (sourceG js k sigma d h:ℂ)*z h‖ ≤
      Bs*(Cs*(d:ℝ)^eta*(N:ℝ)^beta) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ h ∈ s.filter q, |sourceG js k sigma d h| * Bs := by
        apply sum_le_sum
        intro h hh
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hzS h (mem_filter.mp hh).1 (mem_filter.mp hh).2) (abs_nonneg _)
      _ = Bs*(∑ h ∈ s.filter q, |sourceG js k sigma d h|) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hsmall sigma d N hsig hd hN _ (fun h hh => hs h (mem_filter.mp hh).1)) hBs
  have hb := hlarge sigma d N hsig hd hN (s.filter (fun h => ¬q h)) X A V Bl c
    hX hA hV hBl hc (fun h hh => hs h (mem_filter.mp hh).1) E Y
    (fun h hh => hscale h (mem_filter.mp hh).1 (lt_of_not_ge (mem_filter.mp hh).2)) z
    (fun h hh => hzL h (mem_filter.mp hh).1 (lt_of_not_ge (mem_filter.mp hh).2))
  rw [← sum_filter_add_sum_filter_not s q]
  apply (norm_add_le _ _).trans
  apply (add_le_add ha hb).trans
  have he : 0 ≤ envelope X A V := by unfold envelope; positivity
  have hde : 0 ≤ (d:ℝ)^eta := by positivity
  have hnb : 0 ≤ (N:ℝ)^beta := by positivity
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCs.le hBl) (sq_nonneg c)) he,
    mul_nonneg hCl.le hBs,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs.le hBl) (sq_nonneg c)) he) hde) hnb,
    mul_nonneg (mul_nonneg (mul_nonneg hCl.le hBs) hde) hnb]

#print axioms absolute_mass
#print axioms mixed_sum
end XiPrime8845.PRZZSplitScaleSum
