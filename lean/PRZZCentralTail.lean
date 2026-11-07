import PRZZFrozenTail
import PRZZCongruencePoisson

/-! Exact finite central block and paired infinite tail of the actual smooth
Poisson weight. Sharp arithmetic quotient masks are not silently removed. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators FourierTransform ContDiff
namespace XiPrime8845.PRZZCentralTail
open PRZZFrozenTail PRZZAStar
set_option maxHeartbeats 3000000

theorem integer_split (f : ℤ → ℂ) (H : ℕ)
    (hp : Summable (fun j : ℕ => f (j+1)))
    (hm : Summable (fun j : ℕ => f (-(j+1)))) :
    (∑' k : ℤ, f k) =
      f 0 + (∑ j ∈ Finset.range H, (f (j+1)+f (-(j+1)))) +
        ∑' j : ℕ, (f ((j+H:ℕ)+1)+f (-((j+H:ℕ)+1))) := by
  have hp0 : Summable (fun j : ℕ => f j) := (summable_nat_add_iff 1).mp hp
  rw [tsum_of_nat_of_neg_add_one hp0 hm, hp0.tsum_eq_zero_add]
  have hh := (hp.add hm).sum_add_tsum_nat_add H
  rw [hp.tsum_add hm] at hh
  push_cast at hh ⊢
  rw [add_assoc, ← hh]
  ring

def mode (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t : ℝ) (h : ℤ) : ℂ :=
  ((q⁻¹:ℝ):ℂ)*𝓕 (frozen F M z alpha beta sigma t) ((h:ℝ)/q)*phase q residue h

def central (F : ℝ → ℂ) (M q residue : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (t : ℝ) (H : ℕ) : ℂ :=
  mode F M q residue z alpha beta sigma t 0 +
    ∑ j ∈ Finset.range H, pair F M q residue z alpha beta sigma 0 j t

theorem mode_summable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M q residue t : ℝ) (z : Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hq : 0 < q) (ht : 0 < t)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hs : sigma ≠ 0) :
    Summable (fun j : ℕ => mode F M q residue z alpha beta sigma t (j+1)) ∧
    Summable (fun j : ℕ => mode F M q residue z alpha beta sigma t (-(j+1))) := by
  have h := (PRZZWeightTail.actual_tail (1/2) 3 (by norm_num) F hF
    (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
    ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma
    (by positivity) (by positivity) hs hsF 0 0 q hq).1
  have hpos := h.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => le_add_of_nonneg_right (norm_nonneg _))
  have hneg := h.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => le_add_of_nonneg_left (norm_nonneg _))
  constructor
  · apply Summable.of_norm
    simpa [mode,frozen,norm_mul,phase_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hq,abs_of_pos (inv_pos.mpr hq)] using hpos.mul_left q⁻¹
  · apply Summable.of_norm
    simpa [mode,frozen,norm_mul,phase_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hq,abs_of_pos (inv_pos.mpr hq),neg_div,add_div,add_comm] using hneg.mul_left q⁻¹

theorem poisson_split (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M q residue t : ℝ) (z : Index) (alpha beta sigma : ℂ) (H : ℕ)
    (hM : 0 < M) (hq : 0 < q) (ht : 0 < t)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) (hs : sigma ≠ 0) :
    (∑' j : ℤ, frozen F M z alpha beta sigma t (residue+q*j)) =
      central F M q residue z alpha beta sigma t H +
        ∑' j : ℕ, pair F M q residue z alpha beta sigma H j t := by
  have hp := PRZZPoissonActualWeight.frozen_poisson F hF (1/2) 3 M t q residue z
    alpha beta sigma (by norm_num) hM ht hq hn hm hs hsF
  change (∑' j : ℤ, frozen F M z alpha beta sigma t (residue+q*j)) = _ at hp
  rw [hp]
  have he := mode_summable F hF hsF M q residue t z alpha beta sigma hM hq ht hn hm hs
  have hh := integer_split (mode F M q residue z alpha beta sigma t) H he.1 he.2
  simpa [mode,central,pair,phase,frozen,Nat.cast_add,Nat.cast_one,Int.cast_add,
    Int.cast_natCast,Int.cast_one,Int.cast_neg,neg_div,add_comm,add_div] using hh

/-- The signed AFE convention is delta=-Delta. -/
def residue (z : Index) : ℝ :=
  ((-z.2.1*(PRZZKloostermanInputs.inverseResidue z.1.2 z.1.1:ℤ):ℤ):ℝ)

theorem signed_mode (F : ℝ → ℂ) (M t : ℝ) (z : Index)
    (alpha beta sigma : ℂ) (h : ℤ) :
    mode F M z.1.2 (residue z) z alpha beta sigma t h =
      (((z.1.2:ℝ)⁻¹:ℝ):ℂ)*𝓕 (frozen F M z alpha beta sigma t) ((h:ℝ)/z.1.2)*
        PRZZKloostermanInputs.e
          (-((h:ℝ)*(z.2.1:ℝ))*PRZZKloostermanInputs.inverseResidue z.1.2 z.1.1/z.1.2) := by
  unfold mode phase residue PRZZKloostermanInputs.e
  push_cast
  congr 2
  ring

/-- Simultaneous substitution in every literal finite arithmetic row.
The actual prefactors, including their conjugations and masks, are unchanged.
This identifies smooth progression sums; it does not remove sharp AFE masks. -/
theorem all_rows (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F : ℝ → ℂ) (alpha beta sigma : ℂ) (J : ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (hs : sigma ≠ 0) :
    (∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
      ∑' j : ℤ, frozen F M z alpha beta sigma T (residue z+(z.1.2:ℝ)*j)) =
      (∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        central F M z.1.2 (residue z) z alpha beta sigma T J) +
      ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        ∑' j : ℕ, pair F M z.1.2 (residue z) z alpha beta sigma J j T := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hn1 : 0 < z.1.1 := by have := (Finset.mem_Icc.mp hn.1).1; omega
  have hn2 : 0 < z.1.2 := by have := (Finset.mem_Icc.mp hn.2).1; omega
  rw [poisson_split F hF hsF M z.1.2 (residue z) T z alpha beta sigma J
    hM (by exact_mod_cast hn2) hT hn1 hn2 hs,mul_add]

/-- Time integration of the exact full-minus-central arithmetic sum.
No integral is split without integrability; this is equality of integrands. -/
theorem all_rows_time (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F w : ℝ → ℂ) (alpha beta sigma : ℂ) (J : ℕ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hM : 0 < M) (hT : 0 < T) (hs : sigma ≠ 0) :
    (∫ t in Icc T (2*T), w t *
      ((∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        ∑' j : ℤ, frozen F M z alpha beta sigma t (residue z+(z.1.2:ℝ)*j))-
       ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        central F M z.1.2 (residue z) z alpha beta sigma t J)) =
      ∫ t in Icc T (2*T), w t * ∑ z ∈ indices N d D H,
        prefactor a F1 F2 d alpha beta z *
          ∑' j : ℕ, pair F M z.1.2 (residue z) z alpha beta sigma J j t := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [all_rows N d D H t M a F1 F2 F alpha beta sigma J hF hsF
    hM (hT.trans_le ht.1) hs,add_sub_cancel_left]

/-- Aggregate the actual signed log-phase replacement with its original
denominators. The gap and small-ratio conditions remain visible. -/
theorem signed_phase_integral {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (m k u v delta : ι → ℝ)
    (hmu : ∀ i ∈ s, m i*u i ≠ 0)
    (hgap : ∀ i ∈ s, m i*u i-k i*v i=delta i)
    (hsmall : ∀ i ∈ s, |delta i/(m i*u i)| ≤ 1/2)
    (w : ℝ → ℂ) (hw : Continuous w) (A B : ℝ) :
    ‖∫ t in Icc A B, w t * ∑ i ∈ s, c i *
      (Complex.exp (I*((t*Real.log (k i*v i/(m i*u i)):ℝ):ℂ))-
        Complex.exp (I*((t*(-delta i)/(m i*u i):ℝ):ℂ)))‖ ≤
      (2*∑ i ∈ s, ‖c i‖*(delta i)^2/(m i*u i)^2) *
        ∫ t in Icc A B, ‖w t‖*|t| := by
  let C := 2*∑ i ∈ s, ‖c i‖*(delta i)^2/(m i*u i)^2
  have hc : Continuous (fun t : ℝ => C*(‖w t‖*|t|)) := by fun_prop
  have hb : ∀ t : ℝ, ‖w t * ∑ i ∈ s, c i *
      (Complex.exp (I*((t*Real.log (k i*v i/(m i*u i)):ℝ):ℂ))-
        Complex.exp (I*((t*(-delta i)/(m i*u i):ℝ):ℂ)))‖ ≤ C*(‖w t‖*|t|) := by
    intro t
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans
    have hh : (∑ i ∈ s, ‖c i *
        (Complex.exp (I*((t*Real.log (k i*v i/(m i*u i)):ℝ):ℂ))-
          Complex.exp (I*((t*(-delta i)/(m i*u i):ℝ):ℂ)))‖) ≤
        ∑ i ∈ s, ‖c i‖*(2*|t| *(delta i)^2/(m i*u i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (PRZZCongruencePoisson.signed_phase_error _ _ _ _ _ t
          (hmu i hi) (hgap i hi) (hsmall i hi)) (norm_nonneg _)
    apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq
    dsimp [C]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    hc.integrableOn_Icc (Filter.Eventually.of_forall hb)).trans_eq
  rw [integral_const_mul]

#print axioms signed_phase_integral
#print axioms all_rows_time
#print axioms signed_mode
#print axioms all_rows
#print axioms integer_split
#print axioms mode_summable
#print axioms poisson_split
end XiPrime8845.PRZZCentralTail
