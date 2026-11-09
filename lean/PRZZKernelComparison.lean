import PRZZPrimitiveKernel
import PRZZGammaMultiplier
import PRZZDiagonalMass
import ZetaPoleScaling

/-! Compare the actual Gamma diagonal kernel with the density-oriented
gcd kernel. The arithmetic simplification is exact; only the Gamma
multiplier is approximated. No general-profile PRZZ axiom is used. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZKernelComparison
open PRZZDiagonalKernel PRZZPrimitiveKernel PRZZCoefficientPolarization
set_option maxHeartbeats 7000000

theorem density_kernel_eq (N n m : ℕ) (hn : n ∈ Finset.Icc 1 N) (hm : m ∈ Finset.Icc 1 N)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (T : ℝ) (hT : 0 < T) (A B : ℂ) :
    densityGcdKernel T Phi A B n m =
      GcdDecomposition.mass Phi T*primitiveKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) n m+
      GcdDecomposition.heightFactor Phi T ((A+B)/(Real.log T:ℂ))*
        primitiveKernel N (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) n m := by
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  have h := GcdDecomposition.integrated_term Phi hPhi T hT n m
    (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1 b a
  have hp : 1+b+a=1+(a+b) := by ring
  have hq : 1-b-a=1+(-b+-a) := by ring
  have hs : b+a=(A+B)/(Real.log T:ℂ) := by dsimp [a,b]; ring
  rw [hp,hq,hs] at h
  rw [primitiveKernel_gcd N n m hn hm,primitiveKernel_gcd N n m hn hm]
  unfold densityGcdKernel gcdKernel
  have hh := congrArg (fun z : ℂ => (1/(Nat.lcm n m:ℂ))*z) h
  unfold GcdDecomposition.gcdWeight at hh
  unfold GcdDecomposition.gcdWeight
  dsimp [a,b] at hh
  have hp' : 1+B/(Real.log T:ℂ)+A/(Real.log T:ℂ) =
      1+(A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) := by ring
  have hq' : 1-B/(Real.log T:ℂ)-A/(Real.log T:ℂ) =
      1+(-(B/(Real.log T:ℂ)) + -(A/(Real.log T:ℂ))) := by ring
  dsimp only
  rw [hp',hq']
  simp only [← add_div] at hh ⊢
  convert hh using 1 <;> ring_nf
  all_goals simp only [mul_comm,mul_left_comm,mul_assoc]

theorem kernel_difference (N n m : ℕ) (hn : n ∈ Finset.Icc 1 N) (hm : m ∈ Finset.Icc 1 N)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (T : ℝ) (hT : 0 < T) (A B : ℂ) :
    diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
        (fun t => (Phi (t/T):ℂ)) n m-densityGcdKernel T Phi A B n m =
      ((∫ t in Icc T (2*T), (Phi (t/T):ℂ)*PRZZAFEDual.dualMultiplier
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)-
          GcdDecomposition.heightFactor Phi T ((A+B)/(Real.log T:ℂ)))*
            primitiveKernel N (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) n m := by
  rw [density_kernel_eq N n m hn hm Phi hPhi T hT A B]
  unfold diagonalKernel GcdDecomposition.mass
  ring

theorem reciprocal_power (t : ℝ) (ht : 0 < t) (s : ℂ) :
    ((t/(2*Real.pi):ℝ):ℂ)^(-s) = ((2*Real.pi/t:ℝ):ℂ)^s := by
  rw [GcdDecomposition.positive_cpow _ (by positivity),
    GcdDecomposition.positive_cpow _ (by positivity),
    Real.log_div ht.ne' (by positivity : 2*Real.pi ≠ 0),
    Real.log_div (by positivity : 2*Real.pi ≠ 0) ht.ne']
  push_cast
  congr 1
  ring

theorem phi_mass (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 0 < T →
      (∫ t in Icc T (2*T), ‖(Phi (t/T):ℂ)‖) ≤ D*T := by
  have hc : HasCompactSupport Phi := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2))
    intro x hx
    by_contra hh
    exact hx (hPhi.2 hh)
  obtain ⟨D,hD⟩ := hc.exists_bound_of_continuous hPhi.1.continuous
  refine ⟨max D 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro T hT
  have hi : IntegrableOn (fun _ : ℝ => max D 1) (Icc T (2*T)) := continuous_const.integrableOn_Icc
  calc
    _ ≤ ∫ _t in Icc T (2*T), max D 1 := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _)) hi
      filter_upwards [] with t
      simpa only [Complex.norm_real] using (hD (t/T)).trans (le_max_left D 1)
    _ = _ := by simp [show T*2-T=T by ring,hT.le,mul_comm]

theorem gamma_mass_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ‖(∫ t in Icc T (2*T), (Phi (t/T):ℂ)*PRZZAFEDual.dualMultiplier
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)-
          GcdDecomposition.heightFactor Phi T ((A+B)/(Real.log T:ℂ))‖ ≤ C := by
  obtain ⟨D,hD,hphi⟩ := phi_mass Phi hPhi
  let E := 7*Real.exp (2*S+7)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨(D+1)*E,by positivity,?_⟩
  filter_upwards [PRZZZeroGammaBound.multiplier_scaled_difference S hS,
    PRZZGammaCentral.log_scaled_shifts_eventually S,eventually_gt_atTop (1:ℝ)] with T hmult hsmall hT
  intro A B hA hB
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans (hsmall A B hA hB).1)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans (hsmall A B hA hB).2)
  have hg := PRZZMollifiedTime.dualMultiplier_continuous a b
    (by linarith [har.1]) (by linarith [har.2]) (by linarith [hbr.1]) (by linarith [hbr.2])
  have hp : Continuous (fun t : ℝ => (Phi (t/T):ℂ)) :=
    Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (continuous_id.div_const T))
  have hi : IntegrableOn (fun t => (Phi (t/T):ℂ)*PRZZAFEDual.dualMultiplier a b t)
      (Icc T (2*T)) := (hp.mul hg).integrableOn_Icc
  have hj := GcdDecomposition.phase_weight_integrable Phi hPhi T (by linarith) ((A+B)/(Real.log T:ℂ))
  unfold GcdDecomposition.heightFactor
  rw [← integral_sub hi hj]
  apply (norm_integral_le_integral_norm _).trans
  have hI : IntegrableOn (fun t : ℝ => (E/T)*‖(Phi (t/T):ℂ)‖) (Icc T (2*T)) :=
    (continuous_const.mul hp.norm).integrableOn_Icc
  calc
    _ ≤ ∫ t in Icc T (2*T), (E/T)*‖(Phi (t/T):ℂ)‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _)) hI
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : 0 < t := (by linarith : 0 < T).trans_le ht.1
      have he := reciprocal_power t ht0 ((A+B)/(Real.log T:ℂ))
      have hm := hmult A B hA hB t ht
      rw [he] at hm
      have heq : (Phi (t/T):ℂ)*PRZZAFEDual.dualMultiplier a b t-
          ((2*Real.pi/t:ℝ):ℂ)^((A+B)/(Real.log T:ℂ))*(Phi (t/T):ℂ) =
          (Phi (t/T):ℂ)*(PRZZAFEDual.dualMultiplier a b t-
            ((2*Real.pi/t:ℝ):ℂ)^((A+B)/(Real.log T:ℂ))) := by ring
      rw [heq,norm_mul]
      exact (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans_eq (by dsimp [E]; ring)
    _ = (E/T)*(∫ t in Icc T (2*T), ‖(Phi (t/T):ℂ)‖) := integral_const_mul _ _
    _ ≤ (E/T)*(D*T) := mul_le_mul_of_nonneg_left (hphi T (by linarith)) (by positivity)
    _ ≤ (D+1)*E := by field_simp; nlinarith

theorem primitive_norm (N n m : ℕ) (hn : n ∈ Finset.Icc 1 N) (hm : m ∈ Finset.Icc 1 N)
    (T S : ℝ) (hT : 1 < T) (hS : 0 ≤ S) (hNT : (N:ℝ) ≤ T)
    (alpha beta : ℂ) (ha : |alpha.re| ≤ S/Real.log T) (hb : |beta.re| ≤ S/Real.log T) :
    ‖primitiveKernel N alpha beta n m‖ ≤
      Real.exp (2*S)*‖riemannZeta (1+(alpha+beta))‖/(Nat.lcm n m:ℝ) := by
  let d := Nat.gcd n m
  let u := n/d
  let v := m/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left m (Finset.mem_Icc.mp hn).1
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left m (Finset.mem_Icc.mp hn).1) hd
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right n (Finset.mem_Icc.mp hm).1) hd
  have hdu : d*u=n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)
  have hdv : d*v=m := Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)
  have hc : u.Coprime v := Nat.coprime_div_gcd_div_gcd hd
  have hl : Nat.lcm n m=d*u*v := by rw [← hdu,← hdv,Nat.lcm_mul_left,hc.lcm_eq_mul]; ring
  have h := PRZZDiagonalMass.coefficient_envelope N d u v (fun _ => 1) (fun _ => 1)
    (fun _ => 1) alpha beta 1 1 1 S T (by norm_num) (by norm_num) (by norm_num) hS hT hNT
    hd hu hv (by intros; simp) (by intros; simp) (by intros; simp) ha hb
    (hdu ▸ (Finset.mem_Icc.mp hn).2) (hdv ▸ (Finset.mem_Icc.mp hm).2)
  simp only [PRZZDiagonalAssembly.coefficient,one_mul,star_one] at h
  rw [primitiveKernel_eq N n m hn hm,norm_mul]
  have hh := mul_le_mul_of_nonneg_right h (norm_nonneg (riemannZeta (1+(alpha+beta))))
  simpa only [one_pow,one_mul,hl,Nat.cast_mul,div_mul_eq_mul_div] using hh

/-- Entrywise comparison retains the pole size and the summable arithmetic
lcm weight. The constant and the height threshold precede every index. -/
theorem kernel_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N n m : ℕ) (A B : ℂ),
      (N:ℝ) ≤ T → n ∈ Finset.Icc 1 N → m ∈ Finset.Icc 1 N → ‖A‖ ≤ S → ‖B‖ ≤ S →
      ‖diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
          (fun t => (Phi (t/T):ℂ)) n m-densityGcdKernel T Phi A B n m‖ ≤
        C*‖riemannZeta (1-(A+B)/(Real.log T:ℂ))‖/(Nat.lcm n m:ℝ) := by
  obtain ⟨C,hC,h⟩ := gamma_mass_bound Phi hPhi S hS
  refine ⟨C*Real.exp (2*S),by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T h hT
  intro N n m A B hNT hn hm hA hB
  have hL : 0 < Real.log T := Real.log_pos hT
  have hshift (Z : ℂ) (hZ : ‖Z‖ ≤ S) : |(-(Z/(Real.log T:ℂ))).re| ≤ S/Real.log T := by
    simp only [Complex.neg_re,abs_neg,Complex.div_ofReal_re]
    rw [abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm Z).trans hZ) hL.le
  have hp := primitive_norm N n m hn hm T S hT hS hNT
    (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) (hshift B hB) (hshift A hA)
  rw [kernel_difference N n m hn hm Phi hPhi T (by linarith) A B,norm_mul]
  have hz : 1+(-(B/(Real.log T:ℂ)) + -(A/(Real.log T:ℂ))) =
      1-(A+B)/(Real.log T:ℂ) := by ring
  rw [hz] at hp
  exact (mul_le_mul (h A B hA hB) hp (norm_nonneg _) hC.le).trans_eq (by ring)

theorem reflected_zeta_cap (S r : ℝ) (hr : 0 < r) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖riemannZeta (1-(A+B)/(Real.log T:ℂ))‖ ≤ (1+1/r)*Real.log T := by
  have h := Metric.tendstoUniformlyOn_iff.mp
    (ZetaPoleScaling.scaled_zeta_minus_uniform (2*S) r hr) 1 zero_lt_one
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T h hT
  intro A B hA hB hsep
  have hL : 0 < Real.log T := Real.log_pos hT
  have hab : 0 < ‖A+B‖ := hr.trans_le hsep
  have hz := h (A+B) ⟨(norm_add_le _ _).trans (by linarith),hsep⟩
  have h1 : ‖-(1/(A+B))‖ ≤ 1/r := by
    simp only [norm_neg,norm_div,norm_one]
    exact one_div_le_one_div_of_le hr hsep
  have h3 : ‖riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)‖ ≤ 1+1/r := by
    rw [dist_comm] at hz
    calc
      _ = ‖(riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)-(-(1/(A+B))))+
          (-(1/(A+B)))‖ := by ring_nf
      _ ≤ ‖riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)-(-(1/(A+B)))‖+
          ‖-(1/(A+B))‖ := norm_add_le _ _
      _ ≤ 1+1/r := by rw [← dist_eq_norm]; linarith
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL] at h3
  exact (div_le_iff₀ hL).mp h3

theorem kernel_log_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N n m : ℕ) (A B : ℂ),
      (N:ℝ) ≤ T → n ∈ Finset.Icc 1 N → m ∈ Finset.Icc 1 N →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
          (fun t => (Phi (t/T):ℂ)) n m-densityGcdKernel T Phi A B n m‖ ≤
        C*Real.log T/(Nat.lcm n m:ℝ) := by
  obtain ⟨C,hC,h⟩ := kernel_bound Phi hPhi S hS
  refine ⟨C*(1+1/r),by positivity,?_⟩
  filter_upwards [h,reflected_zeta_cap S r hr] with T h hz
  intro N n m A B hNT hn hm hA hB hsep
  exact (h N n m A B hNT hn hm hA hB).trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hz A B hA hB hsep) hC.le)
      (by positivity)).trans_eq (by ring))

theorem lcm_mass (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, 1/(Nat.lcm n m:ℝ)) ≤
      (N:ℝ)*(1+Real.log N) := by
  have hh : (∑ m ∈ Finset.Icc 1 N, 1/(m:ℝ)) ≤ 1+Real.log N := by
    simpa [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log N
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, 1/(m:ℝ) := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro m hm
      apply one_div_le_one_div_of_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
      exact_mod_cast Nat.le_of_dvd
        (Nat.lcm_pos (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1) (Nat.dvd_lcm_right n m)
    _ = (N:ℝ)*(∑ m ∈ Finset.Icc 1 N, 1/(m:ℝ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

/-- A sufficient arithmetic mass bound for main-term identification.
It is deliberately not advertised as the sharp harmonic-cube bound. -/
theorem arithmetic_defect_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ)
      (a b : ℕ → ℂ) (U V : ℝ),
      (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → 0 ≤ U → 0 ≤ V →
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ U) → (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ V) →
      ‖arithmeticPairing N (fun n m =>
          diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
            (fun t => (Phi (t/T):ℂ)) n m-densityGcdKernel T Phi A B n m) a b‖ ≤
        C*U*V*Real.log T*(N:ℝ)*(1+Real.log N) := by
  obtain ⟨C,hC,h⟩ := kernel_log_bound Phi hPhi S r hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T h hT
  intro N A B a b U V hNT hA hB hsep hU hV ha hb
  have hL : 0 < Real.log T := Real.log_pos hT
  have hk := defect_bound N a b _ _ (fun n m => C*Real.log T/(Nat.lcm n m:ℝ))
    (fun n hn m hm => h N n m A B hNT hn hm hA hB hsep)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        ‖a n‖*‖b m‖*(C*Real.log T/(Nat.lcm n m:ℝ)) := hk
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (C*U*V*Real.log T)*(1/(Nat.lcm n m:ℝ)) := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro m hm
      have he := mul_le_mul_of_nonneg_right
        (mul_le_mul (ha n hn) (hb m hm) (norm_nonneg _) hU)
        (show 0 ≤ C*Real.log T/(Nat.lcm n m:ℝ) by positivity)
      exact he.trans_eq (by ring)
    _ = (C*U*V*Real.log T)*(∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        1/(Nat.lcm n m:ℝ)) := by simp only [Finset.mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (lcm_mass N) (by positivity)).trans_eq (by ring)

#print axioms lcm_mass
#print axioms arithmetic_defect_bound
#print axioms reflected_zeta_cap
#print axioms kernel_log_bound
#print axioms primitive_norm
#print axioms kernel_bound
#print axioms density_kernel_eq
#print axioms kernel_difference
#print axioms reciprocal_power
#print axioms phi_mass
#print axioms gamma_mass_bound
end XiPrime8845.PRZZKernelComparison
