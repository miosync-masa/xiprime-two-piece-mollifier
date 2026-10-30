import WuGammaJets

/-! Exact finite transfer from eta/H to the certified differential polynomial.
The error retains the seven individual zeta derivatives; it is not a
pointwise bound for zeta or a zero-counting statement. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.WuStirlingTransfer
open WuAuxiliary WuStirling WuGammaJets ZetaMomentIntegral
set_option maxHeartbeats 2000000

theorem U_expansion (T : ℝ) (s : ℂ) :
    U T s = ∑ n ∈ range 7, ∑ j ∈ range (n+1),
      (rCoeff n:ℂ)*(n.choose j:ℂ)*(1/2:ℂ)^j*scaledZeta (n-j) T s := by
  simp only [U,ZetaMomentPolynomial.differentialPolynomial,WitnessMomentBound.qReal_cast]
  norm_num [sum_range_succ,rCoeff,NumericalGate.qCoeff,Nat.choose]
  ring

theorem difference_expansion (T : ℝ) (s : ℂ)
    (hs : 0 < s.re) (h1 : s ≠ 1) (hL : Real.log T ≠ 0) :
    V T s-U T s = ∑ n ∈ range 7, ∑ j ∈ range (n+1),
      (rCoeff n:ℂ)*(n.choose j:ℂ)*(jet j T s-(1/2:ℂ)^j)*scaledZeta (n-j) T s := by
  rw [V_expansion T s hs h1 hL,U_expansion,← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intros
  ring

def gammaConstant : ℝ := ∑ j ∈ range 7, jetConstant j
def coefficientMass : ℝ := ∑ n ∈ range 7, ∑ j ∈ range (n+1),
  |rCoeff n| * (n.choose j:ℝ)
def transferConstant : ℝ := coefficientMass*gammaConstant

theorem transferConstant_nonneg : 0 ≤ transferConstant := by
  unfold transferConstant coefficientMass gammaConstant
  exact mul_nonneg (sum_nonneg (fun n _ => sum_nonneg (fun j _ => by positivity)))
    (sum_nonneg (fun j _ => jetConstant_nonneg j))

/-- Uniform on a fixed strip, at the actual height, not at fixed g/ordinate. -/
theorem difference_bound (T t σ : ℝ) (hT : 4 ≤ T) (hL : 1 ≤ Real.log T)
    (ht : t ∈ Set.Icc T (2*T)) (hσ : σ ∈ Set.Icc (7/16) 3) :
    ‖V T ((σ:ℂ)+(t:ℂ)*Complex.I)-U T ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (transferConstant/Real.log T)*
        ∑ k ∈ range 7, ‖scaledZeta k T ((σ:ℂ)+(t:ℂ)*Complex.I)‖ := by
  let s : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  have hr : 0 < s.re := by dsimp [s]; simp only [Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]; linarith [hσ.1]
  have h1 : s ≠ 1 := by
    intro hh
    have hh' := congrArg Complex.im hh
    simp [s] at hh'
    linarith [ht.1]
  have hLp : 0 < Real.log T := by linarith
  have hjet (j : ℕ) (hj : j ≤ 6) :
      ‖jet j T s-(1/2:ℂ)^j‖ ≤ gammaConstant/Real.log T := by
    have hs : ‖s-center t‖ ≤ radius j := by
      have he : s-center t = ((σ-2:ℝ):ℂ) := by dsimp [s,center]; push_cast; ring
      rw [he,Complex.norm_real,Real.norm_eq_abs]
      have hj' : (j:ℝ) ≤ 6 := by exact_mod_cast hj
      rw [abs_le]
      dsimp [radius]
      constructor <;> linarith [hσ.1,hσ.2]
    exact (jet_bound j hj T t hT hL ht s hs).trans
      (div_le_div_of_nonneg_right (single_le_sum (fun k _ => jetConstant_nonneg k)
        (show j ∈ range 7 by simpa using Nat.lt_succ_of_le hj)) hLp.le)
  have hz (k : ℕ) (hk : k ≤ 6) :
      ‖scaledZeta k T s‖ ≤ ∑ j ∈ range 7, ‖scaledZeta j T s‖ :=
    single_le_sum (s:=range 7) (a:=k) (f:=fun j => ‖scaledZeta j T s‖)
      (fun _ _ => norm_nonneg _) (mem_range.mpr (by omega))
  change ‖V T s-U T s‖ ≤ _
  rw [difference_expansion T s hr h1 hLp.ne']
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ range 7, ∑ j ∈ range (n+1),
        (|rCoeff n| * (n.choose j:ℝ))*(gammaConstant/Real.log T)*
          (∑ k ∈ range 7, ‖scaledZeta k T s‖) := by
      apply sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      have hn6 : n ≤ 6 := by have := mem_range.mp hn; omega
      have hjn : j ≤ n := by have := mem_range.mp hj; omega
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hjet j (hjn.trans hn6)) (by positivity))
        (hz (n-j) (by omega)) (norm_nonneg _)
        (mul_nonneg (by positivity) (div_nonneg
          (sum_nonneg (fun k _ => jetConstant_nonneg k)) hLp.le))
    _ = _ := by
      simp only [← sum_mul]
      unfold transferConstant coefficientMass
      ring

/-- The moving left line enters the common strip eventually. -/
theorem leftPoint_strip :
    ∀ᶠ T : ℝ in atTop, 4 ≤ T ∧ 1 ≤ Real.log T ∧
      (1/2-PRZZAsymptotic.R/Real.log T) ∈ Set.Icc (7/16) 3 := by
  have hlim : Tendsto (fun T : ℝ => PRZZAsymptotic.R/Real.log T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul PRZZAsymptotic.R
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16))] with T hT hL he
  have hR := PRZZAsymptotic.radius_pos
  have hn : 0 ≤ PRZZAsymptotic.R/Real.log T := div_nonneg hR.le (by linarith)
  exact ⟨hT,hL,by constructor <;> linarith⟩

theorem difference_left_bound :
    ∀ᶠ T : ℝ in atTop, ∀ t ∈ Set.Icc T (2*T),
      ‖V T (leftPoint T t)-U T (leftPoint T t)‖ ≤
        (transferConstant/Real.log T)*∑ k ∈ range 7, ‖scaledZeta k T (leftPoint T t)‖ := by
  filter_upwards [leftPoint_strip] with T hT
  intro t ht
  exact difference_bound T t _ hT.1 hT.2.1 ht hT.2.2

#print axioms U_expansion
#print axioms difference_expansion
#print axioms transferConstant_nonneg
#print axioms difference_bound
#print axioms leftPoint_strip
#print axioms difference_left_bound
end XiPrime8845.WuStirlingTransfer

