import PRZZLengthBudget
import PRZZSourceScales

/-! Actual modulus-cell budget. PRZZ p.21 keeps the two Type I terms
separate from the seven Type II terms. No domination by the latter alone
is asserted. The free/complement product scale is retained explicitly. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZModulusScale
open PRZZLengthBudget
set_option maxHeartbeats 2000000

theorem cell_card (N l : ℕ) : (PRZZDyadic.cell N l).card ≤ 2^(l+1) := by
  have hs : PRZZDyadic.cell N l ⊆ Icc 1 (2^(l+1)) := by
    intro q hq
    rw [PRZZDyadic.mem_cell] at hq
    exact mem_Icc.mpr ⟨(mem_Icc.mp hq.1).1,hq.2.2.le⟩
  have hh := card_le_card hs
  simpa using hh

/-- Uniform divisor absorption, followed by the actual modulus dyadic
scale. Constants precede d, N, the dyadic cell and the free endpoint. -/
theorem averaged_scale (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d l M : ℕ, ∀ T eps : ℝ,
      0 < d → (d:ℝ) ≤ T → (N:ℝ) ≤ T → 0 ≤ eps →
      averaged eps N d l M ≤
        C*T^eta*((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l+M) := by
  obtain ⟨C,hC,h⟩ := PRZZTypeICost.divisor_pair_absorbed eta heta
  refine ⟨2*C,by positivity,?_⟩
  intro N d l M T eps hd hdT hNT heps
  let V : ℝ := 2^l
  have hV : 0 < V := by dsimp [V]; positivity
  have hT : 0 < T := (by exact_mod_cast hd : (0:ℝ)<d).trans_le hdT
  have hrow : ∀ q ∈ PRZZDyadic.cell N l,
      Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*(1+(M:ℝ)/q)*(q.divisors.card:ℝ) ≤
      C*T^eta*(2*V)^(1/2+eps)*(1+(M:ℝ)/V) := by
    intro q hq
    rw [PRZZDyadic.mem_cell] at hq
    have hq0 : 0 < q := (mem_Icc.mp hq.1).1
    have hlo : V ≤ (q:ℝ) := by dsimp [V]; exact_mod_cast hq.2.1
    have hhi : (q:ℝ) ≤ 2*V := by
      have hh : (q:ℝ) ≤ (2:ℝ)^(l+1) := by exact_mod_cast hq.2.2.le
      simpa [V,pow_succ,mul_comm] using hh
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg q) hhi (by linarith : 0 ≤ 1/2+eps)
    have hg := h d q hd hq0 T hdT ((by exact_mod_cast (mem_Icc.mp hq.1).2 : (q:ℝ) ≤ N).trans hNT)
    have hr : 1+(M:ℝ)/q ≤ 1+(M:ℝ)/V := by
      exact add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg M) hV hlo) 1
    have hh := mul_le_mul (mul_le_mul hg hp (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by positivity))
      hr (by positivity) (by positivity)
    simp only [Real.rpow_eq_pow]
    nlinarith only [hh]
  have hc : ((PRZZDyadic.cell N l).card:ℝ) ≤ 2*V := by
    have hh : ((PRZZDyadic.cell N l).card:ℝ) ≤ (2:ℝ)^(l+1) := by exact_mod_cast cell_card N l
    simpa [V,pow_succ,mul_comm] using hh
  apply (sum_le_sum hrow).trans
  rw [sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq
  dsimp [V]
  rw [pow_succ]
  field_simp
  <;> ring

/-- The source Type I scaling: complement length L <= c W and
L times the free endpoint <= c U give the two terms, not DI's seven. -/
theorem typeI_scale (L M U V W c p : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hLW : L ≤ c*W) (hprod : L*M ≤ c*U) :
    L*((2*V)^p*(V+M)) ≤ c*((2*V)^p*(V*W+U)) := by
  have hh := mul_le_mul_of_nonneg_right hLW hV
  have hp : 0 ≤ (2*V)^p := Real.rpow_nonneg (by positivity) _
  have hs := mul_le_mul_of_nonneg_left (add_le_add hh hprod) hp
  nlinarith only [hs]

/-- The actual HB dyadic factors supply the free/complement product
condition. No ambient N is substituted for the local product U. -/
theorem actual_product (N d h y K : ℕ) (js : List ℕ)
    (b : PRZZHBBranches.Branch) (hb : b ∈ PRZZHBBranches.branches y K js)
    (k : Fin b.2.length → ℕ) (i : Fin b.2.length) (U : ℝ)
    (hU : ∏ a, (2:ℝ)^(k a) = U) :
    (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) *
      (PRZZFreeLength.endpoint N d h 1 (k i):ℝ) ≤
        (2:ℝ)^((js.length+1)*(2*K))*U := by
  have hm : PRZZFreeLength.endpoint N d h 1 (k i) ≤ 2^(k i+1) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (Nat.sub_le _ _))
  have hmR : (PRZZFreeLength.endpoint N d h 1 (k i):ℝ) ≤ (2:ℝ)^(k i+1) := by exact_mod_cast hm
  apply (mul_le_mul_of_nonneg_left hmR (by positivity)).trans
  rw [mul_comm, mul_prod_erase univ (fun a => (2:ℝ)^(k a+1)) (mem_univ i)]
  rw [PRZZSourceScales.upper_product, hU]
  have hlen := PRZZBranchDegrees.branches_length y K js b hb
  simp only [card_univ,Fintype.card_fin]
  have hU0 : 0 ≤ U := hU ▸ (show 0 ≤ ∏ a, (2:ℝ)^(k a) by positivity)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hU0

#print axioms cell_card
#print axioms averaged_scale
#print axioms typeI_scale
#print axioms actual_product

/-- The actual complementary HB box and effective free endpoint discharge
both Type I scale conditions at once. The modulus is its own dyadic scale,
not the ambient coefficient cutoff. -/
theorem actual_averaged_typeI (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h y K l : ℕ, ∀ js : List ℕ,
      ∀ b ∈ PRZZHBBranches.branches y K js,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length, ∀ U T eps : ℝ,
      (∏ a, (2:ℝ)^(k a)) = U →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a)) < U^(1/4:ℝ) →
      0 < d → (d:ℝ) ≤ T → (N:ℝ) ≤ T → 0 ≤ eps →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) *
        averaged eps N d l (PRZZFreeLength.endpoint N d h 1 (k i)) ≤
      C*T^eta*(2:ℝ)^((js.length+1)*(2*K))*
        (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C,hC,hbound⟩ := averaged_scale eta heta
  refine ⟨C,hC,?_⟩
  intro N d h y K l js b hb k i U T eps hp hs hd hdT hNT heps
  have hbnd := hbound N d l (PRZZFreeLength.endpoint N d h 1 (k i)) T eps hd hdT hNT heps
  have hscale := typeI_scale
    (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))
    (PRZZFreeLength.endpoint N d h 1 (k i)) U ((2:ℝ)^l) (U^(1/4:ℝ))
    ((2:ℝ)^((js.length+1)*(2*K))) (1/2+eps)
    (by positivity) (by positivity) (by positivity)
    (PRZZCellMass.typeI_support y K js b hb k i U hs)
    (actual_product N d h y K js b hb k i U hp)
  rw [show 2*(2:ℝ)^l = 2^(l+1) by ring] at hscale
  have hT : 0 < T := (by exact_mod_cast hd : (0:ℝ)<d).trans_le hdT
  calc
    _ ≤ (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) *
        (C*T^eta*((2:ℝ)^(l+1))^(1/2+eps)*
          ((2:ℝ)^l+PRZZFreeLength.endpoint N d h 1 (k i))) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = C*T^eta*((∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))*
        (((2:ℝ)^(l+1))^(1/2+eps)*
          ((2:ℝ)^l+PRZZFreeLength.endpoint N d h 1 (k i)))) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hscale (by positivity)).trans_eq (by ring)

#print axioms actual_averaged_typeI
end XiPrime8845.PRZZModulusScale
