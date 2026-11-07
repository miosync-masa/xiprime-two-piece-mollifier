import PRZZUnfrozenPoisson

/-! Supply the full analytic mass of the actual joint Poisson defect.
The sharp k cutoff costs no extra multiplicity: k is unique for fixed m.
The resulting bound is uniform in the sharp AFE truncation L. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex MeasureTheory
namespace XiPrime8845.PRZZPoissonAnalyticMass
open PRZZUnfrozenPoisson
set_option maxHeartbeats 5000000

theorem retained_card (L : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (hM : 0 < M) (hv : 0 < z.1.2) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ((retained L F M z).card:ℝ) ≤ 3*M := by
  classical
  have hm (p : ℤ × ℤ) (hp : p ∈ retained L F M z) :
      p.1 ∈ Finset.Icc (1:ℤ) ⌊3*M⌋ := by
    have hh := Finset.mem_filter.mp hp
    have hhi := (hsF hh.2.2).2
    have hupper : (p.1:ℝ) ≤ 3*M := by
      have hmul := mul_le_mul_of_nonneg_left hhi hM.le
      field_simp at hmul
      linarith
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_product.mp hh.1).1).1,
      Int.le_floor.mpr hupper⟩
  have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1) (retained L F M z) := by
    intro a ha b hb he
    dsimp only at he
    have hga := (Finset.mem_filter.mp ha).2.1
    have hgb := (Finset.mem_filter.mp hb).2.1
    have hv0 : (z.1.2:ℤ) ≠ 0 := by exact_mod_cast hv.ne'
    have hk : a.2*(z.1.2:ℤ) = b.2*(z.1.2:ℤ) := by rw [he] at hga; linarith
    exact Prod.ext he (mul_right_cancel₀ hv0 hk)
  have hsub : (retained L F M z).image (fun p => p.1) ⊆ Finset.Icc (1:ℤ) ⌊3*M⌋ := by
    intro m hm'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm'
    exact hm p hp
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  have he : (Finset.Icc (1:ℤ) ⌊3*M⌋).card = ⌊3*M⌋.toNat := by simp [Int.card_Icc]
  rw [he] at hcard
  have hc : (⌊3*M⌋.toNat:ℝ) = (⌊3*M⌋:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity : 0 ≤ 3*M))
  exact (by exact_mod_cast hcard : ((retained L F M z).card:ℝ) ≤ ⌊3*M⌋.toNat).trans
    (hc.le.trans (Int.floor_le _))

theorem base_bound (L : ℕ) (F : ℝ → ℂ) (M B eta : ℝ) (z : PRZZAStar.Index)
    (alpha beta : ℂ) (hM : 0 < M) (hv : 0 < z.1.2) (hB : 0 ≤ B) (heta : 0 ≤ eta)
    (hF : ∀ x, ‖F x‖ ≤ B) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hshift : |alpha.re+beta.re| ≤ eta) (p : ℤ × ℤ) (hp : p ∈ retained L F M z) :
    ‖base F M z alpha beta p.1‖ ≤ B*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta := by
  have hh := Finset.mem_filter.mp hp
  have hm1 : (1:ℝ) ≤ p.1 := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_product.mp hh.1).1).1
  have hm0 : (0:ℝ) < p.1 := by linarith
  have hv1 : (1:ℝ) ≤ z.1.2 := by exact_mod_cast hv
  have hv0 : (0:ℝ) < z.1.2 := by linarith
  have hs := hsF hh.2.2
  have hlo : M/2 ≤ (p.1:ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hs.1 hM.le
    field_simp at ht
    linarith
  have hhi : (p.1:ℝ) ≤ 3*M := by
    have ht := mul_le_mul_of_nonneg_left hs.2 hM.le
    field_simp at ht
    linarith
  have hslo := (abs_le.mp hshift).1
  have hshi := (abs_le.mp hshift).2
  have he : Real.exp ((alpha.re+beta.re+1)*(Real.log (z.1.2:ℝ)-Real.log (p.1:ℝ))) =
      (z.1.2:ℝ)^(alpha.re+beta.re+1)*(p.1:ℝ)^(-(alpha.re+beta.re+1)) := by
    rw [Real.rpow_def_of_pos hv0,Real.rpow_def_of_pos hm0,← Real.exp_add]
    congr 1
    ring
  have hinv : (p.1:ℝ)^(-1:ℝ) ≤ 2/M := by
    rw [Real.rpow_neg_one]
    calc
      (p.1:ℝ)⁻¹ = 1/(p.1:ℝ) := by rw [one_div]
      _ ≤ 1/(M/2) := one_div_le_one_div_of_le (by positivity) hlo
      _ = _ := by ring
  have hvp : (z.1.2:ℝ)^(alpha.re+beta.re+1) ≤ (z.1.2:ℝ)^(1+eta) :=
    Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)
  have hmp : (p.1:ℝ)^(-(alpha.re+beta.re+1)) ≤ (p.1:ℝ)^(-1+eta) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  rw [base_norm,he]
  calc
    _ ≤ B*((z.1.2:ℝ)^(1+eta)*(p.1:ℝ)^(-1+eta)) :=
      mul_le_mul (hF _) (mul_le_mul hvp hmp (by positivity) (by positivity)) (by positivity) hB
    _ = B*(z.1.2:ℝ)^(1+eta)*((p.1:ℝ)^(-1:ℝ)*(p.1:ℝ)^eta) := by
      rw [Real.rpow_add hm0]; ring
    _ ≤ B*(z.1.2:ℝ)^(1+eta)*((2/M)*(3*M)^eta) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hinv (Real.rpow_le_rpow hm0.le hhi heta) (by positivity) (by positivity)) (by positivity)
    _ = _ := by ring

/-- Actual L-uniform mass supplier. The extra v and M^eta factors are
displayed: the earlier coefficient-only freezing budget did not include
these spatial amplitudes. Constants precede all scales and shifts. -/
theorem analytic_mass_bound (F : ℝ → ℂ) (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (L : ℕ) (M eta : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ),
      0 < M → 0 ≤ eta → 0 < z.1.1 → 0 < z.1.2 → |alpha.re+beta.re| ≤ eta →
      analyticMass L F M z alpha beta ≤
        24*B*(z.1.2:ℝ)^2*(z.1.2:ℝ)^(1+eta)*(3*M)^eta/
          (Real.pi^2*M^4*(z.1.1:ℝ)^2) := by
  obtain ⟨B,hb⟩ := hcF.exists_bound_of_continuous hF
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro L M eta z alpha beta hM heta hu hv hshift
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  let R := Real.pi*M^2*z.1.1/(2*z.1.2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hpos : 0 ≤ max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/R^2 := by positivity
  have ht (p : ℤ × ℤ) (hp : p ∈ retained L F M z) :
      ‖base F M z alpha beta p.1‖/(numerator z p.1)^2 ≤
        max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/R^2 := by
    have hh := Finset.mem_filter.mp hp
    have hm0 : (0:ℝ) < p.1 := by
      have h1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hh.1).1).1
      exact_mod_cast (show (0:ℤ) < p.1 by omega)
    have hlo : M/2 ≤ (p.1:ℝ) := by
      have hs := mul_le_mul_of_nonneg_left (hsF hh.2.2).1 hM.le
      field_simp at hs
      linarith
    have hr : R ≤ numerator z p.1 := by
      dsimp [R,numerator]
      calc
        _ = 2*Real.pi*(M/2)^2*z.1.1/z.1.2 := by ring
        _ ≤ _ := by gcongr
    apply (div_le_div_of_nonneg_right
      (base_bound L F M (max B 0) eta z alpha beta hM hv (le_max_right _ _) heta
        (fun x => (hb x).trans (le_max_left _ _)) hsF hshift p hp) (by positivity)).trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc
    _ ≤ ∑ _p ∈ retained L F M z,
        max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/R^2 := Finset.sum_le_sum ht
    _ = (retained L F M z).card*(max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/R^2) := by simp
    _ ≤ 3*M*(max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/R^2) :=
      mul_le_mul_of_nonneg_right (retained_card L F M z hM hv hsF) hpos
    _ = _ := by dsimp [R]; field_simp; ring

/-- The actual spatial mass in the exact denominator used by the
computed row budget. The additional v^(1+eta) M^eta weight is explicit. -/
theorem dyadic_mass_bound (F : ℝ → ℂ) (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (L N j l : ℕ) (M eta : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ),
      0 < M → 0 ≤ eta → 0 < z.1.1 → 0 < z.1.2 → |alpha.re+beta.re| ≤ eta →
      z.1 ∈ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l →
      analyticMass L F M z alpha beta ≤
        6*B*(z.1.2:ℝ)^(1+eta)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2 := by
  obtain ⟨B,hb⟩ := hcF.exists_bound_of_continuous hF
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro L N j l M eta z alpha beta hM heta hu hv hshift hcell
  have hR := PRZZFreezeScales.floor_pos M j l hM
  have ht (p : ℤ × ℤ) (hp : p ∈ retained L F M z) :
      ‖base F M z alpha beta p.1‖/(numerator z p.1)^2 ≤
        max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2 := by
    have hh := Finset.mem_filter.mp hp
    have hlo : M/2 ≤ (p.1:ℝ) := by
      have hs := mul_le_mul_of_nonneg_left (hsF hh.2.2).1 hM.le
      field_simp at hs
      linarith
    have hr := PRZZFreezeScales.product_floor N j l z.1 M p.1 hM hlo hcell
    change PRZZFreezeScales.productFloor M j l ≤ numerator z p.1 at hr
    apply (div_le_div_of_nonneg_right
      (base_bound L F M (max B 0) eta z alpha beta hM hv (le_max_right _ _) heta
        (fun x => (hb x).trans (le_max_left _ _)) hsF hshift p hp) (by positivity)).trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc
    _ ≤ ∑ _p ∈ retained L F M z,
        max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2 :=
      Finset.sum_le_sum ht
    _ = (retained L F M z).card*
        (max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2) := by simp
    _ ≤ 3*M*(max B 0*(z.1.2:ℝ)^(1+eta)*(2/M)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2) :=
      mul_le_mul_of_nonneg_right (retained_card L F M z hM hv hsF) (by positivity)
    _ = _ := by field_simp; ring

/-- Paying the spatial v factor changes N^6 to N^7, which still fits
the PRZZ target throughout the stated 4/7 range. -/
theorem seventh_power_target (N T : ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hscale : N ≤ T^(4/7:ℝ)) : N^7/T^3 ≤ PRZZOptimalPowers.target N T := by
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hp : N^(21/4:ℝ) ≤ T^3 := by
    calc
      _ ≤ (T^(4/7:ℝ))^(21/4:ℝ) := Real.rpow_le_rpow hn.le hscale (by norm_num)
      _ = T^3 := by rw [← Real.rpow_mul ht.le]; norm_num [Real.rpow_natCast]
  have he : N^7 = N^(7/4:ℝ)*N^(21/4:ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num [Real.rpow_natCast]
  apply (div_le_iff₀ (by positivity : 0 < T^3)).mpr
  rw [he]
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- Substitute the supplied analytic mass into the actual joint error
integral and the concrete source cutoff into kappa. The coefficient norm
is exactly the one used in the computed finite budget, with the necessary
extra spatial weight explicitly retained. -/
theorem row_time_budget (F : ℝ → ℂ) (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L N d j l : ℕ) (T M Q eps eta : ℝ)
      (z : PRZZAStar.Index) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi →
      0 < d → 0 < T → 0 < M → 0 < Q → 0 ≤ eta →
      |alpha.re+beta.re| ≤ eta → 0 < z.1.1 → 0 < z.1.2 →
      Function.support F1 ⊆ Icc (Q/2) (3*Q) → F1 ((d:ℝ)*z.1.1) ≠ 0 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d → 8 ≤ T^(1-eps) →
      z.1 ∈ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l →
      ‖∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
        errorSum L F M z alpha beta sigma t‖ ≤
      E*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*M)^eta*
        PRZZPrefactorMass.sourceCost T M eps j l*
        ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,D,hC,hD,herr⟩ := error_time_bound Z
  obtain ⟨B,hB,hmass⟩ := dyadic_mass_bound F hF hcF hsF
  refine ⟨6*B*(C+D)+1,by positivity,?_⟩
  intro L N d j l T M Q eps eta z alpha beta sigma a F1 F2 phi
    hz hs hphi hd hT hM hQ heta hshift hu hv hs1 hf1 hdelta hheight hcell
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  have hA : 0 < T^(1-eps) := Real.rpow_pos_of_pos hT _
  have hQu : Q ≤ 2*(d:ℝ)*z.1.1 := by linarith [(hs1 hf1).1]
  have hsmall := PRZZSourceLattice.source_delta T M Q d z.1.1 eps z.2.1 hT hM hd0 hu0 hQu hheight hdelta
  let kap := 2*|(z.2.1:ℝ)|/(M*z.1.1)
  have hkap0 : 0 ≤ kap := by dsimp [kap]; positivity
  have hkap : kap ≤ PRZZFreezeScales.ratioCap T eps := by
    have hh : |(z.2.1:ℝ)| *(T^(1-eps)*d) ≤ M*Q := by
      apply (le_div_iff₀ (mul_pos hA hd0)).mp
      simpa [PRZZSourceCutoffs.deltaCutoff,div_div] using hdelta
    have hq := mul_le_mul_of_nonneg_left hQu hM.le
    have he : |(z.2.1:ℝ)| *T^(1-eps) ≤ 2*M*z.1.1 := by nlinarith
    dsimp [kap,PRZZFreezeScales.ratioCap]
    apply (div_le_div_iff₀ (mul_pos hM hu0) hA).mpr
    nlinarith
  have hkq : kap+2*T*kap^2 ≤ PRZZFreezeScales.ratioCap T eps+
      2*T*(PRZZFreezeScales.ratioCap T eps)^2 := by gcongr
  have hrc : 0 ≤ PRZZFreezeScales.ratioCap T eps := by
    unfold PRZZFreezeScales.ratioCap; positivity
  have hcost : 0 ≤ PRZZPrefactorMass.sourceCost T M eps j l := by
    unfold PRZZPrefactorMass.sourceCost; positivity
  have hb := hmass L N j l M eta z alpha beta hM heta hu hv hshift hcell
  have hmass0 : 0 ≤ analyticMass L F M z alpha beta := by unfold analyticMass; positivity
  have hcd : C+D/‖sigma‖^2 ≤ (C+D)*(1+1/‖sigma‖^2) := by
    calc
      _ ≤ (C+D/‖sigma‖^2)+(D+C/‖sigma‖^2) := le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  have hstep : (C+D/‖sigma‖^2)*(kap+2*T*kap^2)*(2*T)^2*analyticMass L F M z alpha beta ≤
      (6*B*(C+D))*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*M)^eta*
        PRZZPrefactorMass.sourceCost T M eps j l := by
    calc
      _ ≤ ((C+D)*(1+1/‖sigma‖^2))*(PRZZFreezeScales.ratioCap T eps+
          2*T*(PRZZFreezeScales.ratioCap T eps)^2)*(2*T)^2*
          (6*B*(z.1.2:ℝ)^(1+eta)*(3*M)^eta/(PRZZFreezeScales.productFloor M j l)^2) := by
        gcongr
      _ = _ := by unfold PRZZPrefactorMass.sourceCost; ring
  let c := arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))
  have hi := herr L F (fun t => c*phi t) M T z alpha beta sigma hz hs
    (continuous_const.mul hphi) hM hT hu hv hsF hsmall
  have he : (∫ t in Icc T (2*T), ‖c*phi t‖) =
      ‖c‖*(∫ t in Icc T (2*T), ‖phi t‖) := by
    simp only [norm_mul]
    rw [integral_const_mul]
  rw [he] at hi
  have hm : ‖c‖ = ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖ :=
    arithmetic_mass_eq a F1 F2 d beta alpha z
  rw [hm] at hi
  apply hi.trans
  have hw := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
      (∫ t in Icc T (2*T), ‖phi t‖) by positivity)
  apply le_trans hw
  let W := (1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*M)^eta*
    PRZZPrefactorMass.sourceCost T M eps j l*
    ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
    (∫ t in Icc T (2*T), ‖phi t‖)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hc := mul_le_mul_of_nonneg_right
    (show 6*B*(C+D) ≤ 6*B*(C+D)+1 by linarith) hW
  convert hc using 1 <;> dsimp only [W] <;> ring

/-- The budget controls the literal AFE row minus its actual Poisson
central and infinite tail expression, including the sharp boundary correction.
The equality to the freezing error is proved, not an estimate premise. -/
theorem afe_poisson_remainder_budget (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L B J N d j l : ℕ) (T M Q eps eta : ℝ)
      (z : PRZZAStar.Index) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ),
      L ≤ B → ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi →
      0 < d → 0 < T → 0 < M → 0 < Q → 0 ≤ eta →
      |alpha.re+beta.re| ≤ eta → 0 < z.1.1 → 0 < z.1.2 → z.1.1.Coprime z.1.2 →
      Function.support F1 ⊆ Icc (Q/2) (3*Q) → F1 ((d:ℝ)*z.1.1) ≠ 0 →
      |(z.2.1:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d → 8 ≤ T^(1-eps) →
      |(z.2.1:ℝ)| ≤ M*z.1.1/4 → 3*M ≤ B →
      3*M*z.1.1+|(z.2.1:ℝ)| ≤ (B:ℝ)*z.1.2 →
      z.1 ∈ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l →
      ‖∫ t in Icc T (2*T), phi t*(afeRow L F F1 F2 M z alpha beta sigma a d t-
        arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
          (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
            (∑' k, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J k t)-
            PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t))‖ ≤
      E*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*M)^eta*
        PRZZPrefactorMass.sourceCost T M eps j l*
        ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨E,hE,h⟩ := row_time_budget F hF.continuous hcF hsF Z
  refine ⟨E,hE,?_⟩
  intro L B J N d j l T M Q eps eta z alpha beta sigma a F1 F2 phi
    hLB hz hs hphi hd hT hM hQ heta hshift hu hv hcop hs1 hf1 hdelta hheight
    hsmall hB hkB hcell
  have he : (∫ t in Icc T (2*T), phi t*(afeRow L F F1 F2 M z alpha beta sigma a d t-
      arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
        (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
          (∑' k, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J k t)-
          PRZZWeightedSourcePoisson.boundary L B F M z alpha beta sigma t))) =
      ∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
        errorSum L F M z alpha beta sigma t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [afe_row_eq L F F1 F2 M z alpha beta sigma a d t hd hu hv,
      poisson_eq L B J hLB F hF hsF M t z alpha beta sigma hM (hT.trans_le ht.1)
        hu hv hcop hs hsmall hB hkB]
    ring
  rw [he]
  exact h L N d j l T M Q eps eta z alpha beta sigma a F1 F2 phi
    hz hs hphi hd hT hM hQ heta hshift hu hv hs1 hf1 hdelta hheight hcell

/-- Every actually retained source frequency supplies the upper M scale
needed to pay the extra spatial amplitude. No M-height envelope is assumed. -/
theorem active_spatial_weight (N d j l : ℕ) (T M Q V eps eH eta : ℝ)
    (F1 F2 : ℝ → ℂ) (z : PRZZAStar.Index)
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hNT : (N:ℝ) ≤ T) (hM : 0 < M)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hs2 : Function.support F2 ⊆ Icc (V/2) (3*V))
    (hz : z ∈ PRZZActiveFreezeBudget.active N d j l
      (PRZZSourceCutoffs.deltaCutoff T M Q eps) (PRZZSourceCutoffs.poissonCutoff d T M V eH) F1 F2) :
    (z.1.2:ℝ)^(1+eta)*(3*M)^eta ≤ 6*(N:ℝ)*T^((2+eH)*eta) := by
  have hh := Finset.mem_filter.mp hz
  have hp := Finset.mem_filter.mp (Finset.mem_product.mp hh.1).1
  have hc := Finset.mem_product.mp hp.1
  have hvcell := (PRZZDyadic.mem_cell N l z.1.2).mp hc.2
  have hvN : (z.1.2:ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hvcell.1).2
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast (Finset.mem_Icc.mp hvcell.1).1
  have hdn : (d:ℝ)*z.1.2 ≤ N := by exact_mod_cast hp.2.2.2
  have hV : V ≤ 2*N := by linarith [(hs2 hh.2.2).1]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have ht : 0 < T := by linarith
  have hw := Finset.mem_product.mp (Finset.mem_product.mp hh.1).2
  have hhc := (Finset.mem_filter.mp hw.2).2
  have hh1 : (1:ℝ) ≤ z.2.2 := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hw.2).1).1
  have hH : 1 < PRZZSourceCutoffs.poissonCutoff d T M V eH := hh1.trans_lt hhc
  have hm : M ≤ 2*T^(1+eH) := by
    have hm' : (d:ℝ)*M < V*T^eH := by
      simpa only [one_mul] using (lt_div_iff₀ (mul_pos hd0 hM)).mp hH
    have hdM : M ≤ (d:ℝ)*M := by nlinarith
    calc
      _ ≤ V*T^eH := hdM.trans hm'.le
      _ ≤ (2*T)*T^eH := mul_le_mul_of_nonneg_right (hV.trans (by linarith)) (by positivity)
      _ = _ := by rw [Real.rpow_add ht]; simp only [Real.rpow_one]; ring
  have hvp : (z.1.2:ℝ)^(1+eta) ≤ (N:ℝ)*T^eta := by
    rw [Real.rpow_add hv0,Real.rpow_one]
    exact mul_le_mul hvN (Real.rpow_le_rpow hv0.le (hvN.trans hNT) heta) (by positivity) (by positivity)
  have hmp : (3*M)^eta ≤ 6*T^((1+eH)*eta) := by
    calc
      _ ≤ (6*T^(1+eH))^eta := Real.rpow_le_rpow (by positivity) (by linarith) heta
      _ = (6:ℝ)^eta*T^((1+eH)*eta) := by rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul ht.le]
      _ ≤ 6*T^((1+eH)*eta) := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6) heta1) (by positivity)
  calc
    _ ≤ ((N:ℝ)*T^eta)*(6*T^((1+eH)*eta)) := mul_le_mul hvp hmp (by positivity) (by positivity)
    _ = _ := by rw [show (2+eH)*eta = eta+(1+eH)*eta by ring,Real.rpow_add ht]; ring

#print axioms retained_card
#print axioms base_bound
#print axioms analytic_mass_bound
#print axioms dyadic_mass_bound
#print axioms seventh_power_target
#print axioms row_time_budget
#print axioms afe_poisson_remainder_budget
#print axioms active_spatial_weight
end XiPrime8845.PRZZPoissonAnalyticMass
