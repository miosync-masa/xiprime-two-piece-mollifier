import PRZZDiagonalKernel
import GcdDecomposition

/-! Lossless primitive-diagonal kernel evaluation at its unique gcd
coordinates. Independent coefficient slots retain the density orientation. -/
noncomputable section
open scoped BigOperators
open Complex Finset
namespace XiPrime8845.PRZZPrimitiveKernel
open PRZZDiagonalKernel PRZZDiagonalAssembly PRZZPowerJets
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem primitive_unique (d u v n m : ℕ) (hd : 0 < d)
    (hc : u.Coprime v) (hn : d*u=n) (hm : d*v=m) :
    d=Nat.gcd n m ∧ u=n/Nat.gcd n m ∧ v=m/Nat.gcd n m := by
  have hg : Nat.gcd n m=d := by rw [← hn,← hm,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
  refine ⟨hg.symm,?_,?_⟩
  · rw [hg,← hn,Nat.mul_div_cancel_left u hd]
  · rw [hg,← hm,Nat.mul_div_cancel_left v hd]

theorem primitive_sum (N n m : ℕ) (hn : n ∈ Icc 1 N) (hm : m ∈ Icc 1 N)
    (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if admissible N d u v then atom (d*u) (d*v) (f d u v) n m else 0) =
      f (Nat.gcd n m) (n/Nat.gcd n m) (m/Nat.gcd n m) := by
  classical
  let g := Nat.gcd n m
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left m (mem_Icc.mp hn).1
  have hgn : g ∣ n := Nat.gcd_dvd_left n m
  have hgm : g ∣ m := Nat.gcd_dvd_right n m
  have hnu : g*(n/g)=n := Nat.mul_div_cancel' hgn
  have hmv : g*(m/g)=m := Nat.mul_div_cancel' hgm
  have hcop : (n/g).Coprime (m/g) := Nat.coprime_div_gcd_div_gcd hg0
  have hg : g ∈ Icc 1 N := mem_Icc.mpr
    ⟨hg0,(Nat.gcd_le_left m (mem_Icc.mp hn).1).trans (mem_Icc.mp hn).2⟩
  have hu : n/g ∈ Icc 1 N := mem_Icc.mpr
    ⟨Nat.div_pos (Nat.gcd_le_left m (mem_Icc.mp hn).1) hg0,
      (Nat.div_le_self n g).trans (mem_Icc.mp hn).2⟩
  have hv : m/g ∈ Icc 1 N := mem_Icc.mpr
    ⟨Nat.div_pos (Nat.gcd_le_right n (mem_Icc.mp hm).1) hg0,
      (Nat.div_le_self m g).trans (mem_Icc.mp hm).2⟩
  have hz (d u v : ℕ) (hd : d ∈ Icc 1 N)
      (hoff : d≠g ∨ u≠n/g ∨ v≠m/g) :
      (if admissible N d u v then atom (d*u) (d*v) (f d u v) n m else 0)=0 := by
    by_cases ha : admissible N d u v
    · by_cases he : d*u=n ∧ d*v=m
      · obtain ⟨hd',hu',hv'⟩ := primitive_unique d u v n m (mem_Icc.mp hd).1 ha.1 he.1 he.2
        rcases hoff with hh | hh | hh
        · exact (hh hd').elim
        · exact (hh hu').elim
        · exact (hh hv').elim
      · simp [ha,atom,he]
    · simp [ha]
  rw [sum_eq_single g]
  · rw [sum_eq_single (n/g)]
    · rw [sum_eq_single (m/g)]
      · have ha : admissible N g (n/g) (m/g) :=
          ⟨hcop,by simpa [hnu] using (mem_Icc.mp hn).2,
            by simpa [hmv] using (mem_Icc.mp hm).2⟩
        simp [ha,atom,hnu,hmv,g]
      · intro v hv' hne
        exact hz g (n/g) v hg (Or.inr (Or.inr hne))
      · intro hnot; exact (hnot hv).elim
    · intro u hu' hne
      apply sum_eq_zero; intro v hv'
      exact hz g u v hg (Or.inr (Or.inl hne))
    · intro hnot; exact (hnot hu).elim
  · intro d hd hne
    apply sum_eq_zero; intro u hu'
    apply sum_eq_zero; intro v hv'
    exact hz d u v hd (Or.inl hne)
  · intro hnot; exact (hnot hg).elim

theorem primitiveKernel_eq (N n m : ℕ) (hn : n ∈ Icc 1 N) (hm : m ∈ Icc 1 N)
    (alpha beta : ℂ) :
    primitiveKernel N alpha beta n m =
      power 1 (Nat.gcd n m)*power (1+beta) ((n/Nat.gcd n m:ℕ):ℝ)*
        power (1+alpha) ((m/Nat.gcd n m:ℕ):ℝ)*riemannZeta (1+(alpha+beta)) :=
  primitive_sum N n m hn hm (fun d u v =>
    power 1 d*power (1+beta) u*power (1+alpha) v*riemannZeta (1+(alpha+beta)))

theorem exp_inverse (x : ℝ) (hx : 0 < x) :
    (1:ℂ)/(x:ℂ) = Complex.exp (-(Real.log x:ℂ)) := by
  rw [Complex.exp_neg,← Complex.ofReal_exp,Real.exp_log hx]
  simp

/-- Exact arithmetic weight: n=d*u carries beta, m=d*v carries alpha. -/
theorem primitive_weight (d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (hc : u.Coprime v) (alpha beta : ℂ) :
    power 1 d*power (1+beta) u*power (1+alpha) v =
      1/(Nat.lcm (d*u) (d*v):ℂ)*GcdDecomposition.gcdWeight (d*u) (d*v) beta alpha := by
  have hg : Nat.gcd (d*u) (d*v)=d := by rw [Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
  have hl : Nat.lcm (d*u) (d*v)=d*(u*v) := by rw [Nat.lcm_mul_left,hc.lcm_eq_mul]
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have huR : (0:ℝ) < u := by exact_mod_cast hu
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  rw [GcdDecomposition.gcdWeight_exp _ _ (Nat.mul_pos hd hu) (Nat.mul_pos hd hv),hg,hl]
  have he := exp_inverse ((d*(u*v):ℕ):ℝ) (by positivity : (0:ℝ) < ((d*(u*v):ℕ):ℝ))
  simp only [Complex.ofReal_natCast] at he
  rw [he]
  simp only [power,← Complex.exp_add]
  push_cast
  rw [Real.log_mul hdR.ne' (mul_ne_zero huR.ne' hvR.ne'),Real.log_mul huR.ne' hvR.ne',
    Real.log_mul hdR.ne' huR.ne',Real.log_mul hdR.ne' hvR.ne']
  push_cast
  congr 1
  ring

theorem primitiveKernel_gcd (N n m : ℕ) (hn : n ∈ Icc 1 N) (hm : m ∈ Icc 1 N)
    (alpha beta : ℂ) :
    primitiveKernel N alpha beta n m =
      (1/(Nat.lcm n m:ℂ)*GcdDecomposition.gcdWeight n m beta alpha)*
        riemannZeta (1+(alpha+beta)) := by
  let g := Nat.gcd n m
  have hg : 0 < g := Nat.gcd_pos_of_pos_left m (mem_Icc.mp hn).1
  have hu : 0 < n/g := Nat.div_pos (Nat.gcd_le_left m (mem_Icc.mp hn).1) hg
  have hv : 0 < m/g := Nat.div_pos (Nat.gcd_le_right n (mem_Icc.mp hm).1) hg
  have he := primitive_weight g (n/g) (m/g) hg hu hv
    (Nat.coprime_div_gcd_div_gcd hg) alpha beta
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n m),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)] at he
  rw [primitiveKernel_eq N n m hn hm,he]

#print axioms primitive_unique
#print axioms primitive_sum
#print axioms primitiveKernel_eq
#print axioms exp_inverse
#print axioms primitive_weight
#print axioms primitiveKernel_gcd
end XiPrime8845.PRZZPrimitiveKernel
