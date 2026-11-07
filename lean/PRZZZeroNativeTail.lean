import PRZZZeroOuterHeight
import PRZZZeroSpatialLimit
import PRZZWindowGrids
import PRZZScaledReplacement

/-! Substitute the ORIGINAL real dyadic profiles in the omitted-gap
bound and sum the complete native polynomial M window.  This controls
the Delta complement, not the still separate lower/upper spatial boundary
of zeroMismatch or the height-dependent Gamma dual profile. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroNativeTail
open PRZZMellinSeparation PRZZWRowLimit PRZZZeroOuterHeight
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem profile_cap (P : ℝ → ℝ) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) :
    ∀ x : ℝ, ‖profile (fun y => (P y:ℂ)) x‖ ≤ 1 := by
  intro x
  by_cases hx : 0 ≤ x
  · have hn : 0 ≤ P (x/2)-P x := sub_nonneg.mpr (hm (by linarith))
    rw [profile,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
    linarith [hhi (x/2),hlo x]
  · have hx0 : x ≤ 1/2 := by linarith
    simp [profile,hl x hx0,hl (x/2) (by linarith)]

/-- The true upper support is 2Q, not Q and not the coarse 3Q bound. -/
theorem profile_support (P : ℝ → ℝ) (Q : ℝ) (hQ : 0 < Q)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0) :
    Function.support (scaledCutoff (profile (fun y => (P y:ℂ))) Q) ⊆ Icc (0:ℝ) (2*Q) := by
  intro x hx
  have harg : Q⁻¹*x ≤ 2 := by
    by_contra h
    have h1 : 1 ≤ Q⁻¹*x := by linarith
    have h2 : 1 ≤ (Q⁻¹*x)/2 := by linarith
    exact hx (by simp [scaledCutoff,profile,hr _ h1,hr _ h2])
  have hlo : 0 ≤ Q⁻¹*x := by
    by_contra h
    have h1 : Q⁻¹*x ≤ 1/2 := by linarith
    have h2 : (Q⁻¹*x)/2 ≤ 1/2 := by linarith
    exact hx (by simp [scaledCutoff,profile,hl _ h1,hl _ h2])
  have he : Q*(Q⁻¹*x) = x := by field_simp
  constructor <;> nlinarith [mul_nonneg hQ.le hlo,mul_le_mul_of_nonneg_left harg hQ.le]

theorem native_row_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T M Q1 Q2 : ℝ) (A B : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < M → 0 < Q1 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖tail N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff (profile (fun y => (P y:ℂ))) Q1)
        (scaledCutoff (profile (fun y => (P y:ℂ))) Q2)
        (profile (fun y => (P y:ℂ))) Phi T M Q1 eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := actual_outer_power Phi hPhi hcPhi hsPhi js eps r S rate heps hr hS
  obtain ⟨hf,hc,hsp⟩ := profile_regular (fun y => (P y:ℂ)) hP
    (by intro y hy; simp [hl y hy]) (by intro y hy; simp [hright y hy])
  have hp := profile_cap P hm hlo hhi hl
  refine ⟨C,hC,?_⟩
  intro N T M Q1 Q2 A B hN hT hNT hwide hsep hn hM hQ1 ha hb'
  exact hb N _ _ _ T M Q1 A B hf.continuous hsp (fun y hy => hp y)
    (profile_support P Q1 hQ1 hl hright) (fun x => hp _) (fun x => hp _)
    hN hT hNT hwide hsep hn hM hQ1 ha hb'

def grid (P : ℝ → ℂ) (Phi : ℝ → ℂ) (L N : ℕ) (js : List ℕ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ p ∈ range (Nat.log 2 N+1) ×ˢ range (Nat.log 2 N+1),
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
      tail N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff (profile P) ((2:ℝ)^p.1)) (scaledCutoff (profile P) ((2:ℝ)^p.2))
        (profile P) Phi T ((2:ℝ)^s) ((2:ℝ)^p.1) eps alpha beta

/-- All d,u,v, both arithmetic dyadic grids and every native M piece.
The constant is independent of the growing exhaustion L.  This is a
bound on the explicit omitted-gap grid, NOT yet on zeroMismatch. -/
theorem grid_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (T : ℝ) (A B : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → 2 ≤ T^(eps/2) → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      ‖grid (fun y => (P y:ℂ)) Phi L N js T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := native_row_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps r S (rate+6) heps hr hS
  refine ⟨8*C,by positivity,?_⟩
  intro L N T A B hN hT hNT hwide hsep hn ha hb'
  have hT0 : 0 < T := by linarith
  let s := (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))
  have hsc : (s.card:ℝ) ≤ 2*T^(4:ℝ) := by
    apply (show (s.card:ℝ) ≤ ((PRZZWindowGrids.spatial L T 4).card:ℝ) from by
      exact_mod_cast Finset.card_le_card (by
        intro j hj
        exact mem_filter.mpr ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.le⟩)).trans
    exact PRZZWindowGrids.spatial_card L T 4 hT.le (by norm_num)
  have hkc := PRZZWindowGrids.dyadic_card N T hN hNT
  simp only [card_range] at hkc
  have he : ‖grid (fun y => (P y:ℂ)) Phi L N js T eps
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      ((Nat.log 2 N+1:ℕ):ℝ)^2*(s.card:ℝ)*(C*T^(-(rate+6))) := by
    unfold grid
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ p ∈ range (Nat.log 2 N+1) ×ˢ range (Nat.log 2 N+1),
          ∑ _j ∈ s, C*T^(-(rate+6)) := by
        apply sum_le_sum
        intro p hp
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro j hj
        exact hb N T ((2:ℝ)^j) ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B
          hN hT hNT hwide hsep hn (by positivity) (by positivity) ha hb'
      _ = _ := by simp only [sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_mul]; ring
  calc
    _ ≤ (2*T)^2*(2*T^(4:ℝ))*(C*T^(-(rate+6))) := he.trans (by gcongr)
    _ = (8*C)*(T^(6:ℝ)*T^(-(rate+6))) := by rw [Real.rpow_ofNat,Real.rpow_ofNat]; ring
    _ = _ := by rw [← Real.rpow_add hT0]; congr 2 <;> ring

/-- Every height/shift side condition of the native omitted-gap grid is
supplied here.  The same constant works for ALL L and all bounded shifts. -/
theorem grid_eventually (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ) (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖grid (fun y => (P y:ℂ)) Phi L N js T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-rate) := by
  obtain ⟨C,hC,hb⟩ := grid_power P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi
    js eps r S rate heps hr hS
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    (tendsto_rpow_atTop (show 0 < eps/2 by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (2:ℝ)] with T hsmall hwide hT
  intro L N A B hN hNT hA hB hsep
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hshift (z : ℂ) (hz : ‖z‖ ≤ S) : |(z/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    rw [Complex.div_ofReal_re,abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans hz) hL.le
  have hn : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  exact hb L N T A B hN (by linarith) hNT hwide hsep hn (hshift A hA) (hshift B hB)

#print axioms grid_eventually
#print axioms profile_cap
#print axioms profile_support
#print axioms native_row_power
#print axioms grid_power
end XiPrime8845.PRZZZeroNativeTail
