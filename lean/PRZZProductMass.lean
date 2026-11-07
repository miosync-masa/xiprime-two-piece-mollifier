import PRZZActualSmallReplacement

/-! Hyperbola counting retains the product restriction, rather than paying
L^2. Fixed product windows stabilize in L. Summation of all windows is separate. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace XiPrime8845.PRZZProductMass
open PRZZL1Finite PRZZActualLocalReplacement
set_option maxHeartbeats 2000000

def box (B : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 B ×ˢ Finset.Icc 1 B
def hyperbola (B : ℕ) : Finset (ℕ × ℕ) := (box B).filter (fun p => p.1*p.2 ≤ B)

theorem hyperbola_card (B : ℕ) :
    ((hyperbola B).card:ℝ) ≤ (B:ℝ)*∑ m ∈ Finset.Icc 1 B, 1/(m:ℝ) := by
  have he : (hyperbola B).card = ∑ m ∈ Finset.Icc 1 B, B/m := by
    classical
    simp only [hyperbola,box,card_eq_sum_ones,sum_filter,sum_product]
    apply sum_congr rfl
    intro m hm
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hf : (Finset.Icc 1 B).filter (fun k => m*k ≤ B) = Finset.Icc 1 (B/m) := by
      ext k
      simp only [mem_filter,Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk,hkB⟩,hp⟩
        exact ⟨hk,(Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hp)⟩
      · rintro ⟨hk,hp⟩
        exact ⟨⟨hk,hp.trans (Nat.div_le_self B m)⟩,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hp⟩
    rw [← sum_filter,hf]
    simp
  rw [he]
  push_cast
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hp : ((B/m:ℕ):ℝ)*(m:ℝ) ≤ B := by exact_mod_cast Nat.div_mul_le_self B m
  have hh := (le_div_iff₀ hm0).mpr hp
  simpa [div_eq_mul_inv] using hh

theorem cutoff_product (m k : ℕ) (R : ℝ) (F : ℝ → ℂ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hR : 0 < R)
    (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hf : F ((m:ℝ)*k/R) ≠ 0) (B : ℕ) (hB : 2*R ≤ B) :
    m ≤ B ∧ k ≤ B ∧ m*k ≤ B := by
  have hp : (m:ℝ)*k ≤ B := ((div_le_iff₀ hR).mp (hF hf).2).trans hB
  have hpn : m*k ≤ B := by exact_mod_cast hp
  exact ⟨(Nat.le_mul_of_pos_right m (by omega)).trans hpn,
    (Nat.le_mul_of_pos_left k (by omega)).trans hpn,hpn⟩

/-- Any localized summand, including the complex AFE summand, is exactly
independent of the arithmetic cutoff once it exceeds the product window. -/
theorem cutoff_stable (B L : ℕ) (hBL : B ≤ L) (R : ℝ) (hR : 0 < R)
    (F : ℝ → ℂ) (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hB : 2*R ≤ B) (f : ℕ × ℕ → ℂ) :
    (∑ p ∈ box L, f p*F ((p.1:ℝ)*p.2/R)) =
      ∑ p ∈ box B, f p*F ((p.1:ℝ)*p.2/R) := by
  classical
  symm
  apply sum_subset
  · exact product_subset_product (Icc_subset_Icc le_rfl hBL) (Icc_subset_Icc le_rfl hBL)
  · intro p hp hn
    have hh := mem_product.mp hp
    have hz : F ((p.1:ℝ)*p.2/R) = 0 := by
      by_contra hz
      have hb := cutoff_product p.1 p.2 R F (mem_Icc.mp hh.1).1
        (mem_Icc.mp hh.2).1 hR hF hz B hB
      exact hn (mem_product.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hh.1).1,hb.1⟩,
        mem_Icc.mpr ⟨(mem_Icc.mp hh.2).1,hb.2.1⟩⟩)
    simp [hz]

theorem direct_coefficient (a b : ℂ) (s : ℝ) (m k : ℕ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (ha : s ≤ 1/2+a.re) (hb : s ≤ 1/2+b.re) :
    ‖directTerm a b (fun _ _ => 1) 0 m k‖ ≤ 1/((m:ℝ)*k)^s := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0:ℝ) < m := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  simp only [directTerm,norm_div,norm_one,norm_mul,Complex.ofReal_zero,zero_mul,add_zero,sub_zero]
  rw [← Complex.ofReal_natCast m,← Complex.ofReal_natCast k,
    Complex.norm_cpow_eq_rpow_re_of_pos hm0,Complex.norm_cpow_eq_rpow_re_of_pos hk0]
  simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  rw [Real.mul_rpow hm0.le hk0.le]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hm1 ha)
    (Real.rpow_le_rpow_of_exponent_le hk1 hb) (by positivity) (by positivity)

/-- Uniform in L: the hyperbola, not the square L by L, pays the pair
count. Taking s=1/2-epsilon retains the near-square-root product mass. -/
theorem localized_mass (a b : ℂ) (s R CF : ℝ) (B L : ℕ)
    (hs : 0 ≤ s) (hR : 0 < R) (hCF : 0 ≤ CF)
    (ha : s ≤ 1/2+a.re) (hb : s ≤ 1/2+b.re)
    (F : ℝ → ℂ) (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hFn : ∀ x, ‖F x‖ ≤ CF) (hB : 2*R ≤ B) :
    (∑ p ∈ box L, ‖directTerm a b (fun _ _ => 1) 0 p.1 p.2‖*
      ‖F ((p.1:ℝ)*p.2/R)‖) ≤
      (CF/R^s)*((B:ℝ)*∑ m ∈ Finset.Icc 1 B, 1/(m:ℝ)) := by
  classical
  let q := (box L).filter (fun p => F ((p.1:ℝ)*p.2/R) ≠ 0)
  have hq : q ⊆ hyperbola B := by
    intro p hp
    obtain ⟨hp,hf⟩ := mem_filter.mp hp
    have hh := mem_product.mp hp
    have hc := cutoff_product p.1 p.2 R F (mem_Icc.mp hh.1).1
      (mem_Icc.mp hh.2).1 hR hF hf B hB
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hh.1).1,hc.1⟩,
      mem_Icc.mpr ⟨(mem_Icc.mp hh.2).1,hc.2.1⟩⟩,hc.2.2⟩
  have he : (∑ p ∈ box L, ‖directTerm a b (fun _ _ => 1) 0 p.1 p.2‖*
      ‖F ((p.1:ℝ)*p.2/R)‖) =
      ∑ p ∈ q, ‖directTerm a b (fun _ _ => 1) 0 p.1 p.2‖*‖F ((p.1:ℝ)*p.2/R)‖ := by
    symm
    apply sum_subset (filter_subset _ _)
    intro p hp hn
    have hz : F ((p.1:ℝ)*p.2/R) = 0 := by simpa [q,hp] using hn
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ _p ∈ q, CF/R^s := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hp,hf⟩ := mem_filter.mp hp
      have hh := mem_product.mp hp
      have hprod : R ≤ (p.1:ℝ)*p.2 := PRZZLocalReplacement.cutoff_scale F hF R _ hR hf
      have hd := direct_coefficient a b s p.1 p.2 (mem_Icc.mp hh.1).1 (mem_Icc.mp hh.2).1 ha hb
      have hd' : ‖directTerm a b (fun _ _ => 1) 0 p.1 p.2‖ ≤ 1/R^s := by
        apply hd.trans
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact Real.rpow_le_rpow hR.le hprod hs
      exact (mul_le_mul hd' (hFn _) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ = (CF/R^s)*(q.card:ℝ) := by simp [mul_comm]
    _ ≤ (CF/R^s)*((hyperbola B).card:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Finset.card_le_card hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (hyperbola_card B) (by positivity)

/-- Substitute the hyperbola estimate into the actual four-index mass.
The two mollifier denominators are preserved. -/
theorem actual_mass (a b : ℕ → ℂ) (alpha beta : ℂ) (s R CF : ℝ) (B L N : ℕ)
    (hs : 0 ≤ s) (hR : 0 < R) (hCF : 0 ≤ CF)
    (ha : s ≤ 1/2+alpha.re) (hb : s ≤ 1/2+beta.re)
    (F : ℝ → ℂ) (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hFn : ∀ x, ‖F x‖ ≤ CF) (hB : 2*R ≤ B) :
    (∑ i ∈ PRZZAFEIndices.indices L N,
      ‖coefficient a b alpha beta 0 i*F (product i/R)‖) ≤
      ((CF/R^s)*((B:ℝ)*∑ m ∈ Finset.Icc 1 B, 1/(m:ℝ)))*
      (∑ n ∈ Finset.Icc 1 N, ‖a n/(n:ℂ)^(1/2:ℂ)‖)*
      (∑ n ∈ Finset.Icc 1 N, ‖b n/(n:ℂ)^(1/2:ℂ)‖) := by
  rw [PRZZActualSmallReplacement.mass_factorized]
  have hh := localized_mass alpha beta s R CF B L hs hR hCF ha hb F hF hFn hB
  simp only [box,sum_product] at hh
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (sum_nonneg (fun n hn => norm_nonneg _)))
    (sum_nonneg (fun n hn => norm_nonneg _))

#print axioms actual_mass
#print axioms direct_coefficient
#print axioms localized_mass
#print axioms hyperbola_card
#print axioms cutoff_product
#print axioms cutoff_stable
end XiPrime8845.PRZZProductMass
