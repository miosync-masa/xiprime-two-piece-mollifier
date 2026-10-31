import WuXiBands
import Zeta23.XiPrime.ZeroCount
import Zeta23.Assembly

/-! AF's actual xi-prime Riemann--von Mangoldt input, with strip and seam
discharged. Only dyadic counts are normalized here; an arbitrary-window
formula is not inferred from the public dyadic statement. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology
namespace XiPrime8845.WuTotalAsymptotic
open Zeta23 hiding Ncount N0
open Zeta23.XiPrime
set_option maxHeartbeats 2000000

theorem rvm : RiemannVonMangoldt WuXiBands.zeros :=
  xiDeriv_riemannVonMangoldt' xiDerivZerosInStrip_holds

theorem total_growth : Tendsto (fun T => (Ncount 0 T:ℝ)) atTop atTop := by
  have h := (Assembly.tendsto_N_atTop WuXiBands.zeros rvm).comp
    (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  apply tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  have hh := WuXiBands.zeros.N_mono (show 0 ≤ T/2 by positivity)
    (show 2*(T/2) ≤ T by linarith)
  change (WuXiBands.zeros.N (T/2) (2*(T/2)):ℝ) ≤ (WuXiBands.zeros.N 0 T:ℝ)
  exact_mod_cast hh

theorem dyadic_normalized :
    Tendsto (fun T => (Ncount T (2*T):ℝ)/(T*Real.log T)) atTop (nhds (1/(2*Real.pi))) := by
  obtain ⟨C,T₀,h⟩ := rvm.main
  have hi := tendsto_inv_atTop_zero (𝕜:=ℝ)
  have hl := hi.comp Real.tendsto_log_atTop
  have herr : Tendsto (fun T => ((Ncount T (2*T):ℝ)-T/(2*Real.pi)*ell1 T)/(T*Real.log T))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hi.const_mul |C|)
    filter_upwards [eventually_ge_atTop T₀,eventually_gt_atTop (1:ℝ)] with T hT₀ hT
    have hTp : 0 < T := by linarith
    have hLp := Real.log_pos hT
    have hh := h T hT₀
    change |(Ncount T (2*T):ℝ)-T/(2*Real.pi)*ell1 T| ≤ C*Real.log T at hh
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hTp hLp)]
    apply (div_le_iff₀ (mul_pos hTp hLp)).mpr
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hLp.le
    have he : |C| * T⁻¹*(T*Real.log T) = |C| * Real.log T := by field_simp
    rw [he]
    exact hh.trans hc
  have hm : Tendsto (fun T => (T/(2*Real.pi)*ell1 T)/(T*Real.log T))
      atTop (nhds (1/(2*Real.pi))) := by
    have hh := (tendsto_const_nhds (x := 1/(2*Real.pi))).add
      (hl.const_mul ((-Real.log (2*Real.pi)+2*Real.log 2-1)/(2*Real.pi)))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    have ht : T ≠ 0 := by linarith
    have hL := (Real.log_pos hT).ne'
    rw [ell1,l,Real.log_div ht (by positivity : 2*Real.pi ≠ 0)]
    dsimp only [Function.comp_def]
    field_simp
    ring
  simpa only [zero_add,← add_div,sub_add_cancel] using herr.add hm

theorem N0_add (a b d : ℝ) (hab : a ≤ b) (hbd : b ≤ d) :
    N0 a d = N0 a b+N0 b d := by
  have h : WuXiBands.zeros.N0 a d = WuXiBands.zeros.N0 a b+WuXiBands.zeros.N0 b d := by
    unfold ZeroConfig.N0
    rw [WuXiBands.zeros.window_union hab hbd,union_inter_distrib_right]
    apply finsum_mem_union _ ((WuXiBands.zeros.window_finite a b).subset inter_subset_left)
      ((WuXiBands.zeros.window_finite b d).subset inter_subset_left)
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨_,_,hzb⟩,_⟩ ⟨⟨_,hbz,_⟩,_⟩
    exact (not_lt_of_ge hzb) hbz
  exact h

/-- All terminal real heights, not merely a geometric subsequence. -/
theorem cumulative (b : ℝ)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (b-ε)*(Ncount T (2*T):ℝ) ≤ (N0 T (2*T):ℝ)) :
    ∀ ε > 0, ∃ X₀ : ℝ, ∀ X ≥ X₀, (b-ε)*(Ncount 0 X:ℝ) ≤ (N0 0 X:ℝ) := by
  apply Assembly.dyadic (f := fun a d => (N0 a d:ℝ))
    (g := fun a d => (Ncount a d:ℝ)) ?_ ?_
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) total_growth h
  · intro a c d hac hcd
    exact_mod_cast N0_add a c d hac hcd
  · intro a c d hac hcd
    have hh : Ncount a d = Ncount a c+Ncount c d := WuXiBands.zeros.N_add hac hcd
    exact_mod_cast hh

#print axioms rvm
#print axioms total_growth
#print axioms dyadic_normalized
#print axioms N0_add
#print axioms cumulative
end XiPrime8845.WuTotalAsymptotic
