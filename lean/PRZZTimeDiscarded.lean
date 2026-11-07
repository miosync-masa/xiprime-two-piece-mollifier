import PRZZTimeAmplitude
import PRZZDeltaDecay
import PRZZSourceBoundaryDecay
import PRZZProductMass

/-! Actual time-amplitude IBP and summation over all product scales.
The gap geometry is explicit. Constants precede height and arithmetic
truncation; no derivative-mass or summability premise is supplied. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex
namespace XiPrime8845.PRZZTimeDiscarded
open PRZZTimeAmplitude
set_option maxHeartbeats 3000000

theorem row_controlled (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      (∀ n, ∃ K : ℝ, 0 ≤ K ∧ ∀ sigma, U n sigma ≤ K*(1+1/‖sigma‖^2)) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T R x y B D C eps : ℝ),
      sigma ≠ 0 → 0 < T → 0 < R → 0 < x → 0 < y → x ≤ B → y ≤ B →
      0 < D → D ≤ |y-x| → 0 ≤ C → B/D ≤ C*T^(1-eps) →
      ‖∫ t : ℝ, exp (I*((t*Real.log (y/x):ℝ):ℂ))*
        amplitude F T (2*Real.pi*R) sigma t‖ ≤
        U n sigma*R^(-2:ℝ)*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨A,E,G,hpos,hm⟩ := mass F hF hsF 2 (by norm_num)
  let V := fun (n : ℕ) (sigma : ℂ) => PRZZFullWeightJets.convolution A
    (fun i => E i+G i/‖sigma‖^2) n
  have hv (n : ℕ) (sigma : ℂ) : 0 ≤ V n sigma := by
    unfold V PRZZFullWeightJets.convolution
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
      (add_nonneg (hpos (n-i)).2.1 (div_nonneg (hpos (n-i)).2.2 (sq_nonneg _)))
  refine ⟨fun n sigma => V n sigma/Real.pi^2,
    fun n sigma => div_nonneg (hv n sigma) (sq_nonneg _),?_,?_⟩
  · intro n
    let K := PRZZFullWeightJets.convolution A (fun i => E i+G i) n
    have hK : 0 ≤ K := by
      unfold K PRZZFullWeightJets.convolution
      exact Finset.sum_nonneg (fun i hi => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
        (add_nonneg (hpos (n-i)).2.1 (hpos (n-i)).2.2))
    refine ⟨K/Real.pi^2,by positivity,?_⟩
    intro sigma
    have hh : V n sigma ≤ K*(1+1/‖sigma‖^2) := by
      unfold V K PRZZFullWeightJets.convolution
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have he := (hpos (n-i)).2.1
      have hg := (hpos (n-i)).2.2
      have hq : 0 ≤ 1/‖sigma‖^2 := by positivity
      have ht : E (n-i)+G (n-i)/‖sigma‖^2 ≤ (E (n-i)+G (n-i))*(1+1/‖sigma‖^2) := by
        simp only [div_eq_mul_inv,one_mul] at hq ⊢
        nlinarith [mul_nonneg he hq]
      exact (mul_le_mul_of_nonneg_left ht
        (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)).trans_eq (by ring)
    exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
  intro n sigma T R x y B D C eps hs hT hR hx hy hxb hyb hD hgap hC hscale
  have hvn := hv n sigma
  have hB : 0 < B := hx.trans_le hxb
  have hmass := hm n T (2*Real.pi*R) sigma hT (by positivity) hs
  rw [← mass_window F hsupp T (2*Real.pi*R) sigma hT n] at hmass
  have hb := PRZZDeltaDecay.discarded_bound (amplitude F T (2*Real.pi*R) sigma)
    (smooth F hF hsupp T _ sigma hT (by positivity) hs)
    (compact F hsupp T _ sigma hT) n x y B D hx hy hxb hyb hD hgap
  apply hb.trans
  calc
    _ ≤ (V n sigma*(2*Real.pi*R/(2*T))^(-2:ℝ)*T/T^n)*
        (C*T^(1-eps))^n := by
      apply mul_le_mul hmass (pow_le_pow_left₀ (by positivity) hscale n)
        (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow,← Real.rpow_natCast (T^(1-eps)) n,← Real.rpow_mul hT.le]
      have ht : T^(3-(n:ℝ)*eps) = T^3/T^n*T^((1-eps)*(n:ℝ)) := by
        rw [show 3-(n:ℝ)*eps = (3-(n:ℝ))+(1-eps)*(n:ℝ) by ring,
          Real.rpow_add hT,Real.rpow_sub hT,Real.rpow_natCast]
        norm_num [Real.rpow_natCast]
      rw [ht]
      norm_num [Real.rpow_neg (by positivity : 0 ≤ 2*Real.pi*R/(2*T)),
        Real.rpow_neg hR.le,Real.rpow_two]
      field_simp
      <;> ring

theorem row (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T R x y B D C eps : ℝ),
      sigma ≠ 0 → 0 < T → 0 < R → 0 < x → 0 < y → x ≤ B → y ≤ B →
      0 < D → D ≤ |y-x| → 0 ≤ C → B/D ≤ C*T^(1-eps) →
      ‖∫ t : ℝ, exp (I*((t*Real.log (y/x):ℝ):ℂ))*
        amplitude F T (2*Real.pi*R) sigma t‖ ≤
        U n sigma*R^(-2:ℝ)*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨U,hU,hcap,h⟩ := row_controlled F hF hsF hsupp
  exact ⟨U,hU,h⟩

/-- Summing R=(m+1)(k+1) costs a fixed p-series constant, never L^2.
Any finite mask is permitted. The coefficient cap J is kept explicit. -/
theorem summed_controlled (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      (∀ n, ∃ K : ℝ, 0 ≤ K ∧ ∀ sigma, U n sigma ≤ K*(1+1/‖sigma‖^2)) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T C eps J : ℝ),
      sigma ≠ 0 → 0 < T → 0 ≤ C → 0 ≤ J →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (x y B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ J) →
      (∀ p ∈ s, 0 < x p ∧ 0 < y p ∧ x p ≤ B p ∧ y p ≤ B p ∧
        0 < D p ∧ D p ≤ |y p-x p| ∧ B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)‖ ≤
        J*U n sigma*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨U,hU,hcap,h⟩ := row_controlled F hF hsF hsupp
  let Z := ∑' p, PRZZSourceBoundaryDecay.majorant p
  have hZ : 0 ≤ Z := tsum_nonneg (fun p => by unfold PRZZSourceBoundaryDecay.majorant; positivity)
  refine ⟨fun n sigma => U n sigma*Z,fun n sigma => mul_nonneg (hU n sigma) hZ,?_,?_⟩
  · intro n
    obtain ⟨K,hK,hk⟩ := hcap n
    refine ⟨K*Z,mul_nonneg hK hZ,?_⟩
    intro sigma
    exact (mul_le_mul_of_nonneg_right (hk sigma) hZ).trans_eq (by ring)
  intro n sigma T C eps J hs hT hC hJ s c x y B D hc hg
  have hUn := hU n sigma
  have hi (p : ℕ × ℕ) (hp : p ∈ s) : Integrable (fun t : ℝ => c p*
      (exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have hh := (smooth F hF hsupp T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1)))
        sigma hT (by positivity) hs).continuous
      fun_prop
    · exact ((compact F hsupp T _ sigma hT).mul_left).mul_left
  rw [integral_finsetSum s hi]
  apply (norm_sum_le _ _).trans
  have hpw (p : ℕ × ℕ) : (((p.1:ℝ)+1)*((p.2:ℝ)+1))^(-2:ℝ) =
      PRZZSourceBoundaryDecay.majorant p := by
    exact Real.mul_rpow (by positivity) (by positivity)
  calc
    _ ≤ ∑ p ∈ s, (J*U n sigma*C^n*T^(3-(n:ℝ)*eps))*
        PRZZSourceBoundaryDecay.majorant p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hx,hy,hxb,hyb,hD,hgap,hscale⟩ := hg p hp
      rw [integral_const_mul,norm_mul]
      have hh := h n sigma T (((p.1:ℝ)+1)*((p.2:ℝ)+1)) (x p) (y p) (B p) (D p)
        C eps hs hT (by positivity) hx hy hxb hyb hD hgap hC hscale
      rw [hpw] at hh
      exact (mul_le_mul (hc p hp) hh (norm_nonneg _) hJ).trans_eq (by ring)
    _ = (J*U n sigma*C^n*T^(3-(n:ℝ)*eps))*
        ∑ p ∈ s, PRZZSourceBoundaryDecay.majorant p := by rw [Finset.mul_sum]
    _ ≤ (J*U n sigma*C^n*T^(3-(n:ℝ)*eps))*Z := by
      apply mul_le_mul_of_nonneg_left
        (PRZZSourceBoundaryDecay.majorant_summable.sum_le_tsum s
          (fun p _ => by unfold PRZZSourceBoundaryDecay.majorant; positivity))
      positivity
    _ = _ := by ring

theorem summed (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T C eps J : ℝ),
      sigma ≠ 0 → 0 < T → 0 ≤ C → 0 ≤ J →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (x y B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ J) →
      (∀ p ∈ s, 0 < x p ∧ 0 < y p ∧ x p ≤ B p ∧ y p ≤ B p ∧
        0 < D p ∧ D p ≤ |y p-x p| ∧ B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)‖ ≤
        J*U n sigma*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨U,hU,hcap,h⟩ := summed_controlled F hF hsF hsupp
  exact ⟨U,hU,h⟩

/-- The actual AFE coefficient is bounded without an L-dependent count.
The remaining two mollifier coefficients are not discarded. -/
theorem actual_coefficient_cap (a b : ℕ → ℂ) (alpha beta : ℂ)
    (i : PRZZAFEIndices.Index) (hm : 1 ≤ i.1.1) (hk : 1 ≤ i.1.2)
    (hn : 1 ≤ i.2.1) (hr : 1 ≤ i.2.2)
    (ha : 0 ≤ 1/2+alpha.re) (hb : 0 ≤ 1/2+beta.re) :
    ‖PRZZActualLocalReplacement.coefficient a b alpha beta 0 i‖ ≤
      ‖a i.2.1‖*‖b i.2.2‖ := by
  have hd := PRZZProductMass.direct_coefficient alpha beta 0 i.1.1 i.1.2 hm hk ha hb
  simp only [Real.rpow_zero,div_one] at hd
  have den (m : ℕ) (hm : 1 ≤ m) : 1 ≤ ‖(m:ℂ)^(1/2:ℂ)‖ := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < m)]
    norm_num only [Complex.div_ofNat_re,Complex.one_re]
    exact Real.one_le_rpow hm1 (by norm_num)
  have hna : ‖a i.2.1/(i.2.1:ℂ)^(1/2:ℂ)‖ ≤ ‖a i.2.1‖ := by
    rw [norm_div]; exact div_le_self (norm_nonneg _) (den _ hn)
  have hnb : ‖b i.2.2/(i.2.2:ℂ)^(1/2:ℂ)‖ ≤ ‖b i.2.2‖ := by
    rw [norm_div]; exact div_le_self (norm_nonneg _) (den _ hr)
  simp only [PRZZActualLocalReplacement.coefficient,PRZZL1Finite.term,
    Complex.ofReal_zero,zero_mul,add_zero,norm_mul,norm_star]
  exact (mul_le_mul (mul_le_mul hd hna (norm_nonneg _) (by norm_num)) hnb
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Arbitrary polynomial losses are beaten by choosing the time IBP
order first. This does not hide the remaining shift-dependent constant. -/
theorem order (eps b A : ℝ) (he : 0 < eps) :
    ∃ n : ℕ, ∀ T : ℝ, 1 ≤ T → T^b*T^(3-(n:ℝ)*eps) ≤ T^(-A) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((b+3+A)/eps)
  refine ⟨n,?_⟩
  intro T hT
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  rw [← Real.rpow_add ht]
  apply Real.rpow_le_rpow_of_exponent_le hT
  have hh := (div_lt_iff₀ he).mp hn
  nlinarith

/-- Actual frozen four-index coefficients for a fixed mollifier pair.
All product indices and any discarded-gap mask are summed uniformly. -/
theorem actual_block (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      ∀ (n u v : ℕ) (a b : ℕ → ℂ) (alpha beta sigma : ℂ) (T C eps : ℝ),
      1 ≤ u → 1 ≤ v → 0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      sigma ≠ 0 → 0 < T → 0 ≤ C →
      ∀ (s : Finset (ℕ × ℕ)) (B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ((p.1:ℝ)+1)*u ≤ B p ∧ ((p.2:ℝ)+1)*v ≤ B p ∧
        0 < D p ∧ D p ≤ |((p.2:ℝ)+1)*v-((p.1:ℝ)+1)*u| ∧
        B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s,
        PRZZActualLocalReplacement.coefficient a b alpha beta 0 ((p.1+1,p.2+1),(u,v))*
        (exp (I*((t*Real.log ((((p.2:ℝ)+1)*v)/(((p.1:ℝ)+1)*u)):ℝ):ℂ))*
          amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)‖ ≤
        (‖a u‖*‖b v‖)*U n sigma*C^n*T^(3-(n:ℝ)*eps) := by
  obtain ⟨U,hU,h⟩ := summed F hF hsF hsupp
  refine ⟨U,hU,?_⟩
  intro n u v a b alpha beta sigma T C eps hu hv ha hb hs hT hC s B D hg
  apply h n sigma T C eps (‖a u‖*‖b v‖) hs hT hC (by positivity) s
    (fun p => PRZZActualLocalReplacement.coefficient a b alpha beta 0 ((p.1+1,p.2+1),(u,v)))
    (fun p => ((p.1:ℝ)+1)*u) (fun p => ((p.2:ℝ)+1)*v) B D
  · intro p hp
    exact actual_coefficient_cap a b alpha beta ((p.1+1,p.2+1),(u,v))
      (by dsimp; omega) (by dsimp; omega) hu hv ha hb
  · intro p hp
    have hu0 : (0:ℝ) < u := by exact_mod_cast hu
    have hv0 : (0:ℝ) < v := by exact_mod_cast hv
    exact ⟨by positivity,by positivity,hg p hp⟩

/-- With a fixed separated shift, the complete product sum is smaller
than any prescribed negative power. U and the order precede T and s.
Logarithmically varying shifts require a separate uniformization. -/
theorem negligible (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (hsupp : Function.support F ⊆ Icc (1:ℝ) 2)
    (sigma : ℂ) (hs : sigma ≠ 0) (C eps b A : ℝ) (hC : 0 ≤ C) (he : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (x y B D : ℕ × ℕ → ℝ),
      (∀ p ∈ s, ‖c p‖ ≤ T^b) →
      (∀ p ∈ s, 0 < x p ∧ 0 < y p ∧ x p ≤ B p ∧ y p ≤ B p ∧
        0 < D p ∧ D p ≤ |y p-x p| ∧ B p/D p ≤ C*T^(1-eps)) →
      ‖∫ t : ℝ, ∑ p ∈ s, c p*(exp (I*((t*Real.log (y p/x p):ℝ):ℂ))*
        amplitude F T (2*Real.pi*(((p.1:ℝ)+1)*((p.2:ℝ)+1))) sigma t)‖ ≤ K*T^(-A) := by
  obtain ⟨U,hU,h⟩ := summed F hF hsF hsupp
  obtain ⟨n,hn⟩ := order eps b A he
  have hUn := hU n sigma
  refine ⟨U n sigma*C^n+1,by positivity,?_⟩
  intro T hT s c x y B D hc hg
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hh := h n sigma T C eps (T^b) hs hT0 hC (by positivity) s c x y B D hc hg
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_left (hn T hT)
    (show 0 ≤ U n sigma*C^n by positivity)
  have ht : 0 ≤ T^(-A) := Real.rpow_nonneg hT0.le _
  nlinarith only [hh',ht]

#print axioms row_controlled
#print axioms summed_controlled
#print axioms actual_block
#print axioms negligible
#print axioms actual_coefficient_cap
#print axioms order
#print axioms row
#print axioms summed
end XiPrime8845.PRZZTimeDiscarded
