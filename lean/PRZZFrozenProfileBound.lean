import PRZZExpandedCutoff
import PRZZDualError

/-! Supply the actual frozen paired-tail bound from fixed-profile derivatives.
All scale and shift hypotheses remain visible; no tail bound is a premise. -/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators FourierTransform ContDiff
namespace XiPrime8845.PRZZFrozenProfileBound
open PRZZFrozenTail PRZZFullWeightSmooth PRZZInverseProfile
set_option maxHeartbeats 3000000

theorem actual_tail (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n H : ℕ) (M q residue t R Z P s : ℝ) (z : PRZZAStar.Index)
        (alpha beta sigma : ℂ),
      0 < M → 0 < q → 0 < t → 0 < z.1.1 → 0 < z.1.2 → sigma ≠ 0 →
      0 ≤ R → 0 ≤ Z → ‖alpha+beta‖ ≤ Z →
      ‖alpha+beta‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤ P →
      1/‖sigma‖^2 ≤ s →
      (∀ x ∈ Icc (M/2) (3*M), |((z.2.1:ℝ)*t/z.1.1)/x| ≤ R) →
      let k := 2*Real.pi*z.1.1/(t*z.1.2)
      let B := (3*M-M/2)*(PRZZJetUniform.uniformCap C D E a k M R Z P s (n+2)/(M/2)^(n+2))
      Summable (fun j => pair F M q residue z alpha beta sigma H j t) ∧
      ‖∑' j, pair F M q residue z alpha beta sigma H j t‖ ≤
        ‖Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ))‖ *
        ((z.1.2:ℝ)/M) *
        (2*B*(q*z.1.2)^(n+1)/((2*Real.pi)^(n+2)*((H:ℝ)+1)^n)*PRZZWeightTail.squareMass) := by
  obtain ⟨C,D,E,hpos,h⟩ := PRZZNormalizedTail.uniform_tail (profile F)
    (smooth F hF hsF) (support F hsF) a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n H M q residue t R Z P s z alpha beta sigma hM hq ht hn hv hs hR hZ hz hP hsig hp
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have hn0 : (0:ℝ) < z.1.1 := by exact_mod_cast hn
  let g := weight (profile F) M (2*Real.pi*z.1.1/(t*z.1.2))
    ((z.2.1:ℝ)*t/z.1.1) (alpha+beta) sigma
  let b := fun j : ℕ => (q*(z.1.2:ℝ))⁻¹ *
    (‖𝓕 g (((H+j:ℝ)+1)/(q*z.1.2))‖+‖𝓕 g (-(((H+j:ℝ)+1)/(q*z.1.2)))‖)
  let L := ‖Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ))‖*((z.1.2:ℝ)/M)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hh := h n H M (2*Real.pi*z.1.1/(t*z.1.2))
    ((z.2.1:ℝ)*t/z.1.1) R (q*z.1.2) Z P s (alpha+beta) sigma hM
    (by positivity) hR (by positivity) hs hZ hz hP hsig hp
  dsimp only at hh ⊢
  have hb : Summable b := hh.1.mul_left _
  have hscalar (X Y : ℝ) :
      q⁻¹*(‖Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ))‖/M*X) +
      q⁻¹*(‖Complex.exp ((alpha+beta)*(Real.log (z.1.2:ℝ):ℂ))‖/M*Y) =
      L*((q*(z.1.2:ℝ))⁻¹*(X+Y)) := by
    dsimp only [L]
    field_simp
  have hbound : ∀ j, ‖pair F M q residue z alpha beta sigma H j t‖ ≤ L*b j := by
    intro j
    unfold pair
    apply (norm_add_le _ _).trans
    rw [frozen_profile_fourier F M z alpha beta sigma t _ hM hv hsF,
      frozen_profile_fourier F M z alpha beta sigma t _ hM hv hsF]
    simp only [norm_mul, phase_norm, mul_one, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hM, abs_of_pos (inv_pos.mpr hq)]
    have he : (((H+j:ℝ)+1)/q)/(z.1.2:ℝ) = ((H+j:ℝ)+1)/(q*z.1.2) := by ring
    have he' : (-(((H+j:ℝ)+1)/q))/(z.1.2:ℝ) = -(((H+j:ℝ)+1)/(q*z.1.2)) := by ring
    rw [he,he']
    exact (hscalar _ _).le
  have hsumn : Summable (fun j => ‖pair F M q residue z alpha beta sigma H j t‖) :=
    (hb.mul_left L).of_nonneg_of_le (fun j => norm_nonneg _) hbound
  refine ⟨hsumn.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hsumn).trans
  apply (hsumn.tsum_le_tsum hbound (hb.mul_left L)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hh.2 hL

/-- Preserve the local dyadic v-length, instead of spending a global N.
The supplied coefficient mass can be the actual Gamma/dilated mass theorem. -/
theorem local_weighted_mass (N l : ℕ) (s : Finset (ℕ × ℕ))
    (c : ℕ × ℕ → ℂ) (B : ℕ × ℕ → ℝ) (M K U : ℝ)
    (hM : 0 < M) (hU : 0 ≤ U)
    (hs : ∀ p ∈ s, p.2 ∈ PRZZDyadic.cell N l)
    (hB : ∀ p ∈ s, B p ≤ U) (hc : (∑ p ∈ s, ‖c p‖) ≤ K) :
    (∑ p ∈ s, ‖c p‖*((p.2:ℝ)/M)*B p) ≤ K*((2:ℝ)^(l+1)/M)*U := by
  calc
    _ ≤ ∑ p ∈ s, ‖c p‖*((2:ℝ)^(l+1)/M)*U := by
      apply Finset.sum_le_sum
      intro p hp
      have hv : (p.2:ℝ) ≤ (2:ℝ)^(l+1) := by
        have hh := (PRZZDyadic.mem_cell N l p.2).mp (hs p hp)
        exact_mod_cast hh.2.2.le
      calc
        _ ≤ ‖c p‖*((p.2:ℝ)/M)*U := mul_le_mul_of_nonneg_left (hB p hp) (by positivity)
        _ ≤ _ := by gcongr
    _ = (∑ p ∈ s, ‖c p‖)*((2:ℝ)^(l+1)/M)*U := by rw [Finset.sum_mul,Finset.sum_mul]
    _ ≤ _ := by gcongr

/-- Actual dual Gamma multiplier, complex-power dilation and d-dilated
arithmetic coefficients. The derivative envelope U remains explicit;
all other constants are fixed before height and the dyadic row. -/
theorem dual_weighted_mass (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (js : List ℕ) (N d j l : ℕ) (Q R t M U : ℝ)
        (s : Finset (ℕ × ℕ)) (mass : ℕ × ℕ → ℝ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → t ∈ Icc T (2*T) →
      0 < M → 0 ≤ U →
      s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N) → (∀ p ∈ s, mass p ≤ U) →
      (∑ p ∈ s, ‖(((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*
        star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
        F (Q⁻¹*((d:ℝ)*p.1))*G (R⁻¹*((d:ℝ)*p.2))*
          (PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
            Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ)))) /
          ((p.1:ℂ)*(p.2:ℂ))‖ * ((p.2:ℝ)/M)*mass p) ≤
        ((Real.log N)^(2*PRZZGCoefficient.degree js)*C)*((2:ℝ)^(l+1)/M)*U := by
  obtain ⟨C,hC,h⟩ := PRZZDualError.dual_dilated_pair_mass F G hF hG hsF hsG S hS
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT
  intro A B hA hB js N d j l Q R t M U s mass hN hd hNT ht hM hU hbox hlen hmass
  apply local_weighted_mass N l s _ mass M _ U hM hU
    (fun p hp => (Finset.mem_product.mp (hbox hp)).2) hmass
  simpa only [mul_assoc] using hT A B hA hB js N d j l Q R t s hN hd hNT ht hbox hlen

#print axioms dual_weighted_mass
#print axioms actual_tail
#print axioms local_weighted_mass
end XiPrime8845.PRZZFrozenProfileBound
