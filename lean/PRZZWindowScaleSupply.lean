import PRZZArithmeticWindowCutoff
import PRZZCentralGridWeilDI

/-! Height envelopes supplied from the actual fixed-window geometry.
No frequency premise is postulated for an empty strict source range. -/
noncomputable section
open scoped ContDiff
open Set Complex
namespace XiPrime8845.PRZZWindowScaleSupply
open PRZZMellinSeparation PRZZSourceCutoffs
set_option maxHeartbeats 5000000

theorem scaled_support (F : ℝ → ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    Function.support (scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) := by
  intro x hx
  have hh := hs hx
  have he : Q*(Q⁻¹*x) = x := by field_simp
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hQ.le,
    mul_le_mul_of_nonneg_left hh.2 hQ.le]

theorem frequency_power (d : ℕ) (T Q V e A : ℝ)
    (hd : 1 ≤ d) (hT : 72 ≤ T) (_hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hQT : Q ≤ 2*T) (hVT : V ≤ 2*T)
    (hf : A ≤ (18*T^e)*(Q*V/((d:ℝ)^2*T))) : A ≤ T^(e+2) := by
  have ht : 0 < T := by linarith
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d:ℝ)^2*T := by positivity
  have hprod : Q*V ≤ 4*T^2 := by nlinarith [mul_le_mul hQT hVT hV (by positivity : 0 ≤ 2*T)]
  have hquot : Q*V/((d:ℝ)^2*T) ≤ 4*T := (div_le_iff₀ hden).mpr (by nlinarith [sq_nonneg ((d:ℝ)-1)])
  calc
    A ≤ 18*T^e*(4*T) := hf.trans (mul_le_mul_of_nonneg_left hquot (by positivity))
    _ ≤ T^e*T^2 := by
      have hh := mul_le_mul_of_nonneg_left (show 72*T ≤ T^2 by nlinarith)
        (Real.rpow_nonneg ht.le e)
      nlinarith only [hh]
    _ = _ := by rw [Real.rpow_add ht]; norm_num [Real.rpow_natCast]

theorem empty_or_envelope (N d : ℕ) (T M Q V eD eH : ℝ)
    (hd : 1 ≤ d) (hT : 72 ≤ T) (hM : 0 < M) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hQT : Q ≤ 2*T) (hVT : V ≤ 2*T)
    (hraw : 1 ≤ poissonCutoff d T M (3*V) eH) :
    PRZZAStar.indices N d (deltaCutoff T M Q eD)
      ((PRZZArithmeticWindowCutoff.cutoff d T M V eH:ℝ)+1) = ∅ ∨
    (1 ≤ PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q eD)
        ((PRZZArithmeticWindowCutoff.cutoff d T M V eH:ℝ)+1) ∧
     (PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q eD)
        ((PRZZArithmeticWindowCutoff.cutoff d T M V eH:ℝ)+1):ℝ) ≤ T^(eD+eH+2) ∧
     (PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q eD)
        ((PRZZArithmeticWindowCutoff.cutoff d T M V eH:ℝ)+1):ℝ) ≤
       (18*T^(eD+eH))*(Q*V/((d:ℝ)^2*T))) := by
  rcases PRZZArithmeticWindowCutoff.empty_or_frequency N d T M Q V eD eH hd
    (by linarith) hM hQ hraw with he | ⟨hpos,hbound⟩
  · exact Or.inl he
  · exact Or.inr ⟨hpos,frequency_power d T Q V (eD+eH) _ hd hT hQ hV hQT hVT hbound,hbound⟩

theorem row_log_scale (N s l : ℕ) (T b : ℝ) (hT : 1 < T)
    (hM : (2:ℝ)^s ≤ T^b) (hl : (2:ℝ)^l ≤ N) (hNT : (N:ℝ) ≤ T) :
    |Real.log ((2:ℝ)^s)|+|Real.log ((2:ℝ)^l)| ≤ (b+1)*Real.log T := by
  have hm1 : (1:ℝ) ≤ (2:ℝ)^s := one_le_pow₀ (by norm_num)
  have hl1 : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
  rw [abs_of_nonneg (Real.log_nonneg hm1),abs_of_nonneg (Real.log_nonneg hl1)]
  have hm := Real.log_le_log (by positivity : 0 < (2:ℝ)^s) hM
  rw [Real.log_rpow (by linarith : 0 < T)] at hm
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^l) (hl.trans hNT)
  nlinarith

theorem sum_shift (S T : ℝ) (A B : ℂ) (hlog : 0 < Real.log T)
    (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) :
    |((A+B)/(Real.log T:ℂ)).re| ≤ (2*S)/Real.log T := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right ((norm_add_le A B).trans (by linarith)) hlog.le

#print axioms scaled_support
#print axioms frequency_power
#print axioms empty_or_envelope
#print axioms row_log_scale
#print axioms sum_shift
end XiPrime8845.PRZZWindowScaleSupply
