import PRZZWitnessMass
import PRZZSmoothWeights
import PRZZCutoffJets

/-! Uniform logarithmic profile cutoffs via a finite span of fixed smooth
cutoffs. Constants are chosen before the varying profile parameters and
the dilation scale. Sharp arithmetic support is not differentiated. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZProfileSmooth
open PRZZMellinSeparation
set_option maxHeartbeats 5000000

def logCut (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ := F x*(Real.log x:ℂ)^j
def window (F : ℝ → ℂ) (k : ℕ) (a b x : ℝ) : ℂ :=
  F x*((a-b*Real.log x)^k:ℝ)
def coeff (k : ℕ) (a b : ℝ) (j : ℕ) : ℂ :=
  ((k.choose j:ℝ)*a^j*(-b)^(k-j):ℝ)

theorem expansion (F : ℝ → ℂ) (k : ℕ) (a b x : ℝ) :
    window F k a b x =
      ∑ j ∈ range (k+1), coeff k a b j*logCut F (k-j) x := by
  simp only [window,sub_eq_add_neg,add_pow,Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  simp only [coeff,logCut]
  push_cast
  ring

theorem coeff_bound (k j : ℕ) (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖coeff k a b j‖ ≤ (k.choose j:ℝ) := by
  have hp := pow_le_one₀ (n := j) (abs_nonneg a) ha
  have hq := pow_le_one₀ (n := k-j) (abs_nonneg b) hb
  simp only [coeff,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,
    abs_of_nonneg (show (0:ℝ) ≤ (k.choose j:ℝ) by positivity)]
  calc
    _ ≤ (k.choose j:ℝ)*1*1 := by gcongr
    _ = _ := by ring

theorem logCut_support (F : ℝ → ℂ) (j : ℕ) :
    Function.support (logCut F j) ⊆ Function.support F := by
  intro x hx hf
  exact hx (by simp [logCut,hf])

theorem logCut_compact (F : ℝ → ℂ) (j : ℕ) (hF : HasCompactSupport F) :
    HasCompactSupport (logCut F j) := hF.mul_right

set_option backward.isDefEq.respectTransparency false in
theorem logCut_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (j : ℕ) :
    ContDiff ℝ ∞ (logCut F j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCut F j =ᶠ[𝓝 (0:ℝ)] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds hlo] with y hy
      have hf : F y = 0 := by
        by_contra hn
        exact (not_le.mpr hy) (hs hn).1
      simp [logCut,hf]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y:ℂ)^j) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)).pow j
    exact hF.contDiffAt.mul hl

theorem window_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (k : ℕ) (a b : ℝ) :
    ContDiff ℝ ∞ (window F k a b) := by
  have he : window F k a b = fun x =>
      ∑ j ∈ range (k+1), coeff k a b j*logCut F (k-j) x := funext (expansion F k a b)
  rw [he]
  exact ContDiff.sum (fun j hj => contDiff_const.mul (logCut_smooth F hF lo hi hlo hs _))

theorem jet_expansion (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi)
    (k n : ℕ) (a b Q x : ℝ) :
    iteratedDeriv n (scaledCutoff (window F k a b) Q) x =
      ∑ j ∈ range (k+1), coeff k a b j*
        iteratedDeriv n (scaledCutoff (logCut F (k-j)) Q) x := by
  have hj (j : ℕ) : ContDiff ℝ ∞ (scaledCutoff (logCut F j) Q) :=
    (logCut_smooth F hF lo hi hlo hs j).comp (contDiff_const.mul contDiff_id)
  have low : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
  have he : scaledCutoff (window F k a b) Q = fun y =>
      ∑ j ∈ range (k+1), coeff k a b j*scaledCutoff (logCut F (k-j)) Q y := by
    funext y
    exact expansion F k a b _
  rw [he,iteratedDeriv_fun_sum (fun j hj' =>
    (contDiffAt_const.mul (hj (k-j)).contDiffAt).of_le low)]
  apply sum_congr rfl; intro j hj'
  exact iteratedDeriv_const_mul _ ((hj (k-j)).contDiffAt.of_le low)

/-- Every ordinary derivative, with one constant before a,b,Q,x.
The logarithmic degree is fixed; all derivative orders are allowed. -/
theorem ordinary_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b Q x : ℝ, |a| ≤ 1 → |b| ≤ 1 → 0 < Q →
      ‖iteratedDeriv n (scaledCutoff (window F k a b) Q) x‖ ≤ C/Q^n := by
  have hc : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_Icc (a := lo) (b := hi))
    intro x hx
    by_contra hf
    exact hx (hs hf)
  choose C hC h using fun j => PRZZCutoffJets.ordinary_uniform (logCut F j)
    (logCut_smooth F hF lo hi hlo hs j) (logCut_compact F j hc) n
  refine ⟨∑ j ∈ range (k+1), (k.choose j:ℝ)*C (k-j),
    sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hC _)),?_⟩
  intro a b Q x ha hb hQ
  rw [jet_expansion F hF lo hi hlo hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ range (k+1), (k.choose j:ℝ)*(C (k-j)/Q^n) := by
      apply sum_le_sum; intro j hj
      rw [norm_mul]
      exact mul_le_mul (coeff_bound k j a b ha hb) (h (k-j) Q x hQ)
        (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by simp only [mul_div_assoc,Finset.sum_div]

theorem scaled_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b Q x : ℝ, |a| ≤ 1 → |b| ≤ 1 →
      ‖(x:ℂ)^n*iteratedDeriv n (scaledCutoff (window F k a b) Q) x‖ ≤ C := by
  have hc : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_Icc (a := lo) (b := hi))
    intro x hx
    by_contra hf
    exact hx (hs hf)
  choose C hC h using fun j => PRZZCutoffJets.scaled_uniform (logCut F j)
    (logCut_smooth F hF lo hi hlo hs j) (logCut_compact F j hc) n
  refine ⟨∑ j ∈ range (k+1), (k.choose j:ℝ)*C (k-j),
    sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hC _)),?_⟩
  intro a b Q x ha hb
  rw [jet_expansion F hF lo hi hlo hs,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro j hj
  have he : (x:ℂ)^n*(coeff k a b j*iteratedDeriv n (scaledCutoff (logCut F (k-j)) Q) x) =
      coeff k a b j*((x:ℂ)^n*iteratedDeriv n (scaledCutoff (logCut F (k-j)) Q) x) := by ring
  rw [he,norm_mul]
  exact mul_le_mul (coeff_bound k j a b ha hb) (h (k-j) Q x) (norm_nonneg _) (Nat.cast_nonneg _)

theorem cutoff_bounds (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (k : ℕ) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ a b N x : ℝ,
      |a| ≤ 1 → |b| ≤ 1 → 0 < N →
      ‖scaledCutoff (window F k a b) N x‖ ≤ C0 ∧
      ‖(x:ℂ)*deriv (scaledCutoff (window F k a b) N) x‖ ≤ C1 := by
  obtain ⟨C0,h0,h⟩ := ordinary_uniform F hF lo hi hlo hs k 0
  obtain ⟨C1,h1,h'⟩ := scaled_uniform F hF lo hi hlo hs k 1
  refine ⟨C0,C1,h0,h1,?_⟩
  intro a b N x ha hb hN
  constructor
  · simpa using h a b N x ha hb hN
  · simpa using h' a b N x ha hb

/-- The actual Type I source derivative receives common cutoff constants;
no derivative norm for the varying profile is an assumed input. -/
theorem source_bound_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (k : ℕ) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ a b N kappa x : ℝ,
      |a| ≤ 1 → |b| ≤ 1 → 0 < N → ∀ z : ℂ, ∀ j : ℕ, ∀ P L : ℝ,
      0 < x → 0 ≤ P → 0 ≤ L → ‖(x:ℂ)^z‖ ≤ P → |Real.log x| ≤ L →
      ‖(x:ℂ)*deriv (PRZZTypeIWeights.sourceWeight z j kappa
        (scaledCutoff (window F k a b) N)) x‖ ≤
        P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1) := by
  obtain ⟨C0,C1,h0,h1,h⟩ := cutoff_bounds F hF lo hi hlo hs k
  refine ⟨C0,C1,h0,h1,?_⟩
  intro a b N kappa x ha hb hN z j P L hx hP hL hp hl
  have hf := window_smooth F hF lo hi hlo hs k a b
  have hd := PRZZTypeIWeights.source_hasDerivAt z j kappa x
    (scaledCutoff (window F k a b) N) (deriv (scaledCutoff (window F k a b) N)) hx
      ((PRZZSmoothWeights.scaled_hasDerivAt _ hf N (kappa*x)).differentiableAt.hasDerivAt)
  rw [hd.deriv]
  exact PRZZTypeIWeights.source_derivative_bound z j kappa x _ _ P L C0 C1
    hx hP hL h0 h1 hp hl (h a b N (kappa*x) ha hb hN).1
      (by simpa only [Complex.ofReal_mul] using (h a b N (kappa*x) ha hb hN).2)

theorem coupled_expansion (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (F : ℝ → ℂ) (k : ℕ) (a b N kappa : ℝ) :
    PRZZMellinTypeII.coupled C D U V rho r beta nu alpha
      (scaledCutoff (window F k a b) N) kappa =
      ∑ j ∈ range (k+1), coeff k a b j*
        PRZZMellinTypeII.coupled C D U V rho r beta nu alpha
          (scaledCutoff (logCut F (k-j)) N) kappa := by
  unfold PRZZMellinTypeII.coupled scaledCutoff
  simp_rw [expansion,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro q hq
  ring

/-- DI is genuinely applied to finitely many fixed cutoffs. The resulting
constant precedes the varying profile parameters, not just the scale. -/
theorem coupled_bound_uniform
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps : ℝ) (heps : 0 < eps) (F : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs : Function.support F ⊆ Icc lo hi) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 →
      ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Finset.Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ d ∈ Finset.Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Finset.Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ N kappa : ℝ, 0 < N → 0 < kappa →
      ‖PRZZMellinTypeII.coupled C D U V rho r beta nu alpha
        (scaledCutoff (window F k a b) N) kappa‖ ≤
        K*(R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho) := by
  choose K hK h using fun j => PRZZSmoothMellin.coupled_bound_smooth hDI eps heps
    (logCut F j) lo hi hlo ((logCut_support F j).trans hs)
      (logCut_smooth F hF lo hi hlo hs j)
  let B := ∑ j ∈ range (k+1), (k.choose j:ℝ)*K (k-j)
  have hB : 0 ≤ B := sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hK _).le)
  refine ⟨B+1,by positivity,?_⟩
  intro a b ha hb C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha
    hr hbeta hnu halpha N kappa hN hkappa
  let X := R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hX : 0 ≤ X := by dsimp [X,PRZZKloostermanInputs.diBound]; positivity
  rw [coupled_expansion]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ range (k+1), (k.choose j:ℝ)*(K (k-j)*X) := by
      apply sum_le_sum; intro j hj
      rw [norm_mul]
      exact mul_le_mul (coeff_bound k j a b ha hb)
        (h (k-j) C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
          r beta nu alpha hr hbeta hnu halpha N kappa hN hkappa)
        (norm_nonneg _) (Nat.cast_nonneg _)
    _ = B*X := by dsimp [B]; simp only [Finset.sum_mul,mul_assoc]
    _ ≤ (B+1)*X := by nlinarith

#print axioms expansion
#print axioms coeff_bound
#print axioms logCut_support
#print axioms logCut_compact
#print axioms logCut_smooth
#print axioms window_smooth
#print axioms jet_expansion
#print axioms ordinary_uniform
#print axioms scaled_uniform
#print axioms cutoff_bounds
#print axioms source_bound_uniform
#print axioms coupled_expansion
#print axioms coupled_bound_uniform
end XiPrime8845.PRZZProfileSmooth
