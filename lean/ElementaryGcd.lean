import GcdDecomposition
import SmoothMobius

/-! Exact finite entry to the elementary K00 route. No prime number theorem,
uniform arithmetic asymptotic, or zero-counting assertion is assumed here. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Complex Filter Topology

namespace XiPrime8845.ElementaryGcd
open GcdDecomposition PRZZAsymptotic
attribute [local instance] Classical.propDecidable

def reflect (p : ℂ × ℂ) : ℂ × ℂ := (-p.2, -p.1)

theorem reflect_involutive (p : ℂ × ℂ) : reflect (reflect p) = p := by
  simp [reflect]

def reflectedBidisc : Set (ℂ × ℂ) := reflect '' witnessBidisc
def twoBidiscs : Set (ℂ × ℂ) := witnessBidisc ∪ reflectedBidisc

theorem mem_reflectedBidisc (p : ℂ × ℂ) :
    p ∈ reflectedBidisc ↔ reflect p ∈ witnessBidisc := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [reflect_involutive] using hq
  · intro hp
    exact ⟨reflect p, hp, reflect_involutive p⟩

theorem reflectedBidisc_center (p : ℂ × ℂ) :
    p ∈ reflectedBidisc ↔
      ‖p.1 - (R : ℂ)‖ ≤ R/4 ∧ ‖p.2 - (R : ℂ)‖ ≤ R/4 := by
  rw [mem_reflectedBidisc]
  change (‖-p.2 + (R : ℂ)‖ ≤ _ ∧ ‖-p.1 + (R : ℂ)‖ ≤ _) ↔ _
  have hn (z : ℂ) : ‖-z + (R : ℂ)‖ = ‖z - (R : ℂ)‖ := by
    rw [show -z + (R : ℂ) = -(z - R) by ring, norm_neg]
  rw [hn, hn, and_comm]

theorem reflect_mem_twoBidiscs (p : ℂ × ℂ) :
    reflect p ∈ twoBidiscs ↔ p ∈ twoBidiscs := by
  simp only [twoBidiscs, Set.mem_union, mem_reflectedBidisc, reflect_involutive, or_comm]

/-- Convergence on the union gives the dual limit by precomposition, not by
analytically continuing a convergence statement known only on the minus side. -/
theorem uniform_reflected {f : ℝ → (ℂ × ℂ) → ℂ} {F : (ℂ × ℂ) → ℂ}
    (h : TendstoUniformlyOn f F atTop twoBidiscs) :
    TendstoUniformlyOn (fun T p => f T (reflect p)) (fun p => F (reflect p))
      atTop witnessBidisc := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro p hp
  exact hT (reflect p) (Or.inr ⟨p, hp, rfl⟩)

/-- The finite Mobius transform of a complex power; zero is irrelevant below. -/
def generalizedTotient (s : ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℂ) * (x.2 : ℂ)^s

theorem sum_generalizedTotient (s : ℂ) (n : ℕ) (hn : 0 < n) :
    ∑ g ∈ n.divisors, generalizedTotient s g = (n : ℂ)^s := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := generalizedTotient s) (g := fun n => (n : ℂ)^s) |>.mpr
    (fun _ _ => rfl)) n hn

theorem gcd_divisors_filter (N d e : ℕ) (hd : d ∈ Finset.Icc 1 N)
    (_he : e ∈ Finset.Icc 1 N) :
    (Nat.gcd d e).divisors = (Finset.Icc 1 N).filter (fun g => g ∣ d ∧ g ∣ e) := by
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hg0 : Nat.gcd d e ≠ 0 := (Nat.gcd_pos_of_pos_left e hd0).ne'
  ext g
  constructor
  · intro h
    have hh := Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp h).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos hh.1 hd0, (Nat.le_of_dvd hd0 hh.1).trans
      (Finset.mem_Icc.mp hd).2⟩, hh⟩
  · intro h
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd_iff.mpr (Finset.mem_filter.mp h).2, hg0⟩

/-- Pure finite gcd diagonalization, for any complex divisor weight. -/
theorem finite_diagonalization (N : ℕ) (c u v : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      (∑ g ∈ (Nat.gcd d e).divisors, c g) * u d * v e) =
    ∑ g ∈ Finset.Icc 1 N, c g *
      (∑ d ∈ (Finset.Icc 1 N).filter (g ∣ ·), u d) *
      (∑ e ∈ (Finset.Icc 1 N).filter (g ∣ ·), v e) := by
  have hterm (d e : ℕ) (hd : d ∈ Finset.Icc 1 N) (he : e ∈ Finset.Icc 1 N) :
      (∑ g ∈ (Nat.gcd d e).divisors, c g) * u d * v e =
      ∑ g ∈ Finset.Icc 1 N, c g * (if g ∣ d then u d else 0) *
        (if g ∣ e then v e else 0) := by
    rw [gcd_divisors_filter N d e hd he, Finset.sum_filter]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g hg
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun d hd =>
    Finset.sum_congr rfl (fun e he => hterm d e hd he))]
  rw [Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.sum_comm]

theorem arithmetic_term (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (a b alpha beta : ℂ) :
    a * b / (Nat.lcm d e : ℂ) * gcdWeight d e alpha beta =
      (Nat.gcd d e : ℂ)^(1+alpha+beta) *
        (a / (d : ℂ)^(1+alpha)) * (b / (e : ℂ)^(1+beta)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hg0 : (Nat.gcd d e : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left e hd).ne'
  have hl0 : (Nat.lcm d e : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_ne_zero hd.ne' he.ne')
  have hp : (Nat.gcd d e : ℂ) * (Nat.lcm d e : ℂ) = (d : ℂ) * (e : ℂ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  rw [show (1:ℂ)+alpha+beta = 1+(alpha+beta) by ring,
    cpow_add _ _ hg0, cpow_add _ _ hd0, cpow_add _ _ he0]
  simp only [cpow_one, gcdWeight]
  have hda : (d : ℂ)^alpha ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have heb : (e : ℂ)^beta ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl he0)
  field_simp
  linear_combination -(a*b*(Nat.gcd d e : ℂ)^(alpha+beta)) * hp

/-- The literal arithmetic sum, with both ordered coefficient sequences retained.
The inner sums are over multiples of g; no Mobius factorization is presumed. -/
theorem arithmeticSum_diagonal (a b : ℕ → ℂ) (N : ℕ) (alpha beta : ℂ) :
    arithmeticSum a b N alpha beta =
      ∑ g ∈ Finset.Icc 1 N, generalizedTotient (1+alpha+beta) g *
        (∑ d ∈ (Finset.Icc 1 N).filter (g ∣ ·), a d / (d : ℂ)^(1+alpha)) *
        (∑ e ∈ (Finset.Icc 1 N).filter (g ∣ ·), star (b e) / (e : ℂ)^(1+beta)) := by
  rw [← finite_diagonalization]
  unfold arithmeticSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hd' := (Finset.mem_Icc.mp hd).1
  have he' := (Finset.mem_Icc.mp he).1
  rw [sum_generalizedTotient _ _ (Nat.gcd_pos_of_pos_left e hd')]
  exact arithmetic_term d e hd' he' _ _ alpha beta

theorem sum_multiples (N g : ℕ) (hg : 0 < g) (f : ℕ → ℂ) :
    (∑ d ∈ (Finset.Icc 1 N).filter (g ∣ ·), f d) =
      ∑ n ∈ Finset.Icc 1 (N/g), f (g*n) := by
  symm
  apply Finset.sum_bij (fun n _ => g*n)
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hg hn'.1, ?_⟩, dvd_mul_right g n⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp hn'.2
  · intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left hg hnm
  · intro d hd
    obtain ⟨hdN, hgd⟩ := Finset.mem_filter.mp hd
    have hd' := Finset.mem_Icc.mp hdN
    refine ⟨d/g, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hd'.2⟩,
      Nat.mul_div_cancel' hgd⟩
    exact Nat.div_pos (Nat.le_of_dvd hd'.1 hgd) hg
  · intros; rfl

/-- The x=N/g form, retaining the original coefficients at g*n. -/
theorem arithmeticSum_diagonal_quotient (a b : ℕ → ℂ) (N : ℕ) (alpha beta : ℂ) :
    arithmeticSum a b N alpha beta =
      ∑ g ∈ Finset.Icc 1 N, generalizedTotient (1+alpha+beta) g /
        (g : ℂ)^(2+alpha+beta) *
        (∑ n ∈ Finset.Icc 1 (N/g), a (g*n) / (n : ℂ)^(1+alpha)) *
        (∑ m ∈ Finset.Icc 1 (N/g), star (b (g*m)) / (m : ℂ)^(1+beta)) := by
  rw [arithmeticSum_diagonal]
  apply Finset.sum_congr rfl
  intro g hg
  have hg' : 0 < g := (Finset.mem_Icc.mp hg).1
  rw [sum_multiples N g hg', sum_multiples N g hg']
  have hfrac (f : ℕ → ℂ) (z : ℂ) (n : ℕ) :
      f (g*n) / ((g*n : ℕ) : ℂ)^z = (f (g*n)/(n : ℂ)^z)/(g : ℂ)^z := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  simp_rw [hfrac a (1+alpha), hfrac (fun n => star (b n)) (1+beta)]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg'.ne'
  have hpow : (g : ℂ)^(2+alpha+beta) = (g : ℂ)^(1+alpha) * (g : ℂ)^(1+beta) := by
    rw [show (2:ℂ)+alpha+beta = (1+alpha)+(1+beta) by ring, cpow_add _ _ hg0]
  rw [hpow]
  ring

/-- A general weighted finite convolution reindexing, including N=0. -/
theorem weighted_divisor_reindex (N : ℕ) (c b f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (∑ r ∈ n.divisors, c r * b (n/r)) * f n) =
      ∑ r ∈ Finset.Icc 1 N, c r *
        ∑ m ∈ Finset.Icc 1 (N/r), b m * f (r*m) := by
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (∑ r ∈ n.divisors, c r * b (n/r)) * f n =
        ∑ r ∈ Finset.Icc 1 N, if r ∣ n then c r * b (n/r) * f n else 0 := by
    have hd := gcd_divisors_filter N n n hn hn
    simp only [Nat.gcd_self, and_self] at hd
    rw [hd, Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> simp
  rw [Finset.sum_congr rfl ht, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_filter, sum_multiples N r (Finset.mem_Icc.mp hr).1]
  simp only [Nat.mul_div_cancel_left _ (Finset.mem_Icc.mp hr).1,
    ← Finset.mul_sum, mul_assoc]

/-- Exact smooth-supported expansion for any weight. This neither introduces
tau(g) nor estimates the size of the resulting weighted sum. -/
theorem coprime_weighted_expansion (N g : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime g), (μ n : ℂ) * f n) =
      ∑ r ∈ (Finset.Icc 1 N).filter (SmoothMobius.supported g),
        ∑ m ∈ Finset.Icc 1 (N/r), (μ m : ℂ) * f (r*m) := by
  classical
  rw [Finset.sum_filter]
  have ht (n : ℕ) :
      (if n.Coprime g then (μ n : ℂ)*f n else 0) =
        (∑ r ∈ n.divisors, (if SmoothMobius.supported g r then (1:ℂ) else 0) *
          (μ (n/r) : ℂ)) * f n := by
    rw [← Nat.sum_divisorsAntidiagonal (fun r m =>
      (if SmoothMobius.supported g r then (1:ℂ) else 0) * (μ m : ℂ)),
      ← SmoothMobius.restricted_divisor_sum]
    split_ifs <;> simp
  simp_rw [ht]
  rw [weighted_divisor_reindex N
    (fun r => if SmoothMobius.supported g r then (1:ℂ) else 0)
    (fun m => (μ m : ℂ)) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp

/-- Apply the supported expansion directly to the Conrey coefficient at g*n.
The arbitrary weight may include a complex shift and the original profile. -/
theorem conrey_inner_expansion (N g : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (μ (g*n) : ℂ) * f n) =
      (μ g : ℂ) * ∑ r ∈ (Finset.Icc 1 N).filter (SmoothMobius.supported g),
        ∑ m ∈ Finset.Icc 1 (N/r), (μ m : ℂ) * f (r*m) := by
  rw [← coprime_weighted_expansion, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [SmoothMobius.moebius_mul_indicator]
  split_ifs <;> simp [mul_assoc]

#print axioms reflect_involutive
#print axioms reflectedBidisc_center
#print axioms reflect_mem_twoBidiscs
#print axioms uniform_reflected
#print axioms sum_generalizedTotient
#print axioms finite_diagonalization
#print axioms arithmeticSum_diagonal
#print axioms sum_multiples
#print axioms arithmeticSum_diagonal_quotient
#print axioms weighted_divisor_reindex
#print axioms coprime_weighted_expansion
#print axioms conrey_inner_expansion
end XiPrime8845.ElementaryGcd
