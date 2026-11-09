import PRZZProfileSmooth

/-! The real logarithmic witness profiles on their original dyadic scale.
The sharp indicator stays in the arithmetic support. Uniform constants
cover all seven basis profiles before Y,Q and the evaluation point. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter Topology
namespace XiPrime8845.PRZZProfileScale
open PRZZMellinSeparation PRZZWitnessMass
set_option maxHeartbeats 5000000

def parameterA (Y Q : ℝ) : ℝ := Real.log (Y/Q)/Real.log Y
def parameterB (Y : ℝ) : ℝ := 1/Real.log Y
def amplitude (Y : ℝ) (i : Fin 7) : ℝ := 3/(if i.val < 4 then 1 else (Real.log Y)^2)
def raw (Y : ℝ) (i : Fin 7) (x : ℝ) : ℂ :=
  (amplitude Y i:ℂ)*((Real.log (Y/x)/Real.log Y:ℝ):ℂ)^profileDegree i
def cutoffRaw (F : ℝ → ℂ) (Y Q : ℝ) (i : Fin 7) (x : ℝ) : ℂ :=
  scaledCutoff F Q x*raw Y i x

theorem weight_on_support (theta T : ℝ) (i : Fin 7) (n : ℕ)
    (hn : 1 ≤ n) (hN : (n:ℝ) ≤ PRZZ.length theta T) :
    profileWeight theta T i n = raw (PRZZ.length theta T) i n := by
  have hs : 1 ≤ n ∧ (n:ℝ) ≤ PRZZ.length theta T := ⟨hn,hN⟩
  simp only [profileWeight,if_pos hs,raw,amplitude]
  push_cast
  ring

theorem parameters_unit (Y Q : ℝ) (hL : 1 ≤ Real.log Y) (hQ : 1 ≤ Q) (hQY : Q ≤ Y) :
    |parameterA Y Q| ≤ 1 ∧ |parameterB Y| ≤ 1 := by
  have hQ0 : 0 < Q := by linarith
  have hY : 0 < Y := by linarith
  have hL0 : 0 < Real.log Y := by linarith
  have ha0 : 0 ≤ parameterA Y Q := by
    exact div_nonneg (Real.log_nonneg ((one_le_div hQ0).mpr hQY)) hL0.le
  have ha1 : parameterA Y Q ≤ 1 := by
    apply (div_le_one hL0).mpr
    exact Real.log_le_log (div_pos hY hQ0) (div_le_self hY.le hQ)
  have hb0 : 0 ≤ parameterB Y := by unfold parameterB; positivity
  have hb1 : parameterB Y ≤ 1 := (div_le_one hL0).mpr hL
  exact ⟨by rwa [abs_of_nonneg ha0],by rwa [abs_of_nonneg hb0]⟩

theorem amplitude_bound (Y : ℝ) (i : Fin 7) (hL : 1 ≤ Real.log Y) :
    ‖(amplitude Y i:ℂ)‖ ≤ 3 := by
  have hd : 1 ≤ (if i.val < 4 then (1:ℝ) else (Real.log Y)^2) := by
    split_ifs <;> nlinarith
  have hd0 : 0 < (if i.val < 4 then (1:ℝ) else (Real.log Y)^2) := by linarith
  have ha0 : 0 ≤ 3/(if i.val < 4 then (1:ℝ) else (Real.log Y)^2) := by positivity
  simp only [amplitude,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg ha0]
  apply (div_le_iff₀ hd0).mpr
  nlinarith

theorem raw_window (F : ℝ → ℂ) (Y Q : ℝ) (i : Fin 7) (y : ℝ)
    (hY : 0 < Y) (hQ : 0 < Q) (hy : 0 < y) :
    F y*raw Y i (Q*y) = (amplitude Y i:ℂ)*
      PRZZProfileSmooth.window F (profileDegree i) (parameterA Y Q) (parameterB Y) y := by
  have he : Y/(Q*y) = (Y/Q)/y := by field_simp
  have hl : Real.log (Y/(Q*y))/Real.log Y = parameterA Y Q-parameterB Y*Real.log y := by
    rw [he,Real.log_div (div_ne_zero hY.ne' hQ.ne') hy.ne']
    unfold parameterA parameterB
    ring
  simp only [raw,PRZZProfileSmooth.window,hl,Complex.ofReal_pow]
  ring

theorem cutoffRaw_eq (F : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs : Function.support F ⊆ Icc lo hi) (Y Q : ℝ) (i : Fin 7)
    (hY : 0 < Y) (hQ : 0 < Q) :
    cutoffRaw F Y Q i = fun x => (amplitude Y i:ℂ)*
      scaledCutoff (PRZZProfileSmooth.window F (profileDegree i)
        (parameterA Y Q) (parameterB Y)) Q x := by
  funext x
  by_cases hf : F (Q⁻¹*x)=0
  · simp [cutoffRaw,scaledCutoff,PRZZProfileSmooth.window,hf]
  · have hy : 0 < Q⁻¹*x := hlo.trans_le (hs hf).1
    have he := raw_window F Y Q i (Q⁻¹*x) hY hQ hy
    have hqx : Q*(Q⁻¹*x)=x := by field_simp
    rw [hqx] at he
    exact he

theorem cutoffRaw_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (Y Q : ℝ) (i : Fin 7)
    (hY : 0 < Y) (hQ : 0 < Q) : ContDiff ℝ ∞ (cutoffRaw F Y Q i) := by
  rw [cutoffRaw_eq F lo hi hlo hs Y Q i hY hQ]
  exact contDiff_const.mul ((PRZZProfileSmooth.window_smooth F hF lo hi hlo hs
    (profileDegree i) (parameterA Y Q) (parameterB Y)).comp (contDiff_const.mul contDiff_id))

/-- A common constant for every witness basis, height and admissible
dyadic scale. No supremum is taken after choosing height. -/
theorem ordinary_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y Q x : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y →
      ‖iteratedDeriv n (cutoffRaw F Y Q i) x‖ ≤ C/Q^n := by
  choose D hD h using fun i : Fin 7 => PRZZProfileSmooth.ordinary_uniform
    F hF lo hi hlo hs (profileDegree i) n
  have hsum : 0 ≤ ∑ i, D i := sum_nonneg (fun i hi => hD i)
  refine ⟨3*∑ i, D i,by positivity,?_⟩
  intro Y Q x i hL hQ hQY
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨ha,hb⟩ := parameters_unit Y Q hL hQ hQY
  have hf : ContDiff ℝ ∞ (scaledCutoff (PRZZProfileSmooth.window F (profileDegree i)
      (parameterA Y Q) (parameterB Y)) Q) :=
    (PRZZProfileSmooth.window_smooth F hF lo hi hlo hs (profileDegree i)
      (parameterA Y Q) (parameterB Y)).comp (contDiff_const.mul contDiff_id)
  have low : (n:WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
  rw [cutoffRaw_eq F lo hi hlo hs Y Q i hY0 hQ0,
    iteratedDeriv_const_mul _ (hf.contDiffAt.of_le low),norm_mul]
  have hDi : D i ≤ ∑ j, D j := single_le_sum (fun j hj => hD j) (mem_univ i)
  calc
    _ ≤ 3*(D i/Q^n) := mul_le_mul (amplitude_bound Y i hL)
      (h i _ _ Q x ha hb hQ0) (norm_nonneg _) (by norm_num)
    _ ≤ (3*∑ j, D j)/Q^n := by rw [mul_div_assoc]; gcongr

theorem scaled_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y Q x : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y →
      ‖(x:ℂ)^n*iteratedDeriv n (cutoffRaw F Y Q i) x‖ ≤ C := by
  choose D hD h using fun i : Fin 7 => PRZZProfileSmooth.scaled_uniform
    F hF lo hi hlo hs (profileDegree i) n
  have hsum : 0 ≤ ∑ i, D i := sum_nonneg (fun i hi => hD i)
  refine ⟨3*∑ i, D i,by positivity,?_⟩
  intro Y Q x i hL hQ hQY
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨ha,hb⟩ := parameters_unit Y Q hL hQ hQY
  have hf : ContDiff ℝ ∞ (scaledCutoff (PRZZProfileSmooth.window F (profileDegree i)
      (parameterA Y Q) (parameterB Y)) Q) :=
    (PRZZProfileSmooth.window_smooth F hF lo hi hlo hs (profileDegree i)
      (parameterA Y Q) (parameterB Y)).comp (contDiff_const.mul contDiff_id)
  have low : (n:WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
  rw [cutoffRaw_eq F lo hi hlo hs Y Q i hY0 hQ0,
    iteratedDeriv_const_mul _ (hf.contDiffAt.of_le low)]
  have he : ∀ z : ℂ, (x:ℂ)^n*((amplitude Y i:ℂ)*z) =
      (amplitude Y i:ℂ)*((x:ℂ)^n*z) := by intro z; ring
  rw [he,norm_mul]
  have hDi : D i ≤ ∑ j, D j := single_le_sum (fun j hj => hD j) (mem_univ i)
  exact (mul_le_mul (amplitude_bound Y i hL) (h i _ _ Q x ha hb)
    (norm_nonneg _) (by norm_num)).trans (by gcongr)

theorem cutoff_bounds_actual (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ (Y Q x : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y →
      ‖cutoffRaw F Y Q i x‖ ≤ C0 ∧ ‖(x:ℂ)*deriv (cutoffRaw F Y Q i) x‖ ≤ C1 := by
  obtain ⟨C0,h0,h⟩ := ordinary_uniform F hF lo hi hlo hs 0
  obtain ⟨C1,h1,h'⟩ := scaled_uniform F hF lo hi hlo hs 1
  refine ⟨C0,C1,h0,h1,?_⟩
  intro Y Q x i hL hQ hQY
  exact ⟨by simpa using h Y Q x i hL hQ hQY,by simpa using h' Y Q x i hL hQ hQY⟩

/-- The complex power and logarithmic factors of the actual Type I source
retain their explicit costs. Both cutoff constants are height-uniform. -/
theorem source_bound_actual (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ (Y Q kappa x : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y → ∀ z : ℂ, ∀ j : ℕ, ∀ P L : ℝ,
      0 < x → 0 ≤ P → 0 ≤ L → ‖(x:ℂ)^z‖ ≤ P → |Real.log x| ≤ L →
      ‖(x:ℂ)*deriv (PRZZTypeIWeights.sourceWeight z j kappa (cutoffRaw F Y Q i)) x‖ ≤
        P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1) := by
  obtain ⟨C0,C1,h0,h1,h⟩ := cutoff_bounds_actual F hF lo hi hlo hs
  refine ⟨C0,C1,h0,h1,?_⟩
  intro Y Q kappa x i hL hQ hQY z j P L hx hP hL' hp hl
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  have hf := cutoffRaw_smooth F hF lo hi hlo hs Y Q i hY0 hQ0
  have hd := PRZZTypeIWeights.source_hasDerivAt z j kappa x (cutoffRaw F Y Q i)
    (deriv (cutoffRaw F Y Q i)) hx ((hf.differentiable (by simp)).differentiableAt.hasDerivAt)
  rw [hd.deriv]
  exact PRZZTypeIWeights.source_derivative_bound z j kappa x _ _ P L C0 C1
    hx hP hL' h0 h1 hp hl (h Y Q (kappa*x) i hL hQ hQY).1
      (by simpa only [Complex.ofReal_mul] using (h Y Q (kappa*x) i hL hQ hQY).2)

/-- First-derivative bounds are supplied, rather than assumed, to the
existing discrete variation adapter used in Weil partial summation. -/
theorem variation_uniform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Y Q : ℝ) (i : Fin 7) (start H : ℕ),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y → (H:ℝ) ≤ 2*Q →
      PRZZTypeI.variation (fun j => cutoffRaw F Y Q i (start+j+1)) H ≤ B := by
  obtain ⟨C0,h0,h⟩ := ordinary_uniform F hF lo hi hlo hs 0
  obtain ⟨C1,h1,h'⟩ := ordinary_uniform F hF lo hi hlo hs 1
  refine ⟨C0+2*C1,by positivity,?_⟩
  intro Y Q i start H hL hQ hQY hH
  have hY0 : 0 < Y := by linarith
  have hQ0 : 0 < Q := by linarith
  have hf := cutoffRaw_smooth F hF lo hi hlo hs Y Q i hY0 hQ0
  apply PRZZTypeIWeights.variation_le _ H C0 C1 Q hQ0 h1 hH
  · simpa using h Y Q ((start:ℝ)+((H-1:ℕ):ℝ)+1) i hL hQ hQY
  · intro j hj
    let x : ℝ := start+j+1
    have hh := PRZZTypeIWeights.sampled_step (cutoffRaw F Y Q i)
      (deriv (cutoffRaw F Y Q i)) x (x+1) (C1/Q)
      (fun y hy => ((hf.differentiable (by simp)).differentiableAt.hasDerivAt))
      (fun y hy => by simpa using h' Y Q y i hL hQ hQY) x le_rfl le_rfl
    simpa [x,Nat.cast_add,add_assoc] using hh

/-- A genuine WeilIncomplete application with a common profile variation
constant. The condition H<=2Q is retained explicitly. -/
theorem weil_bound_actual (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (eps : ℝ) (heps : 0 < eps) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y Q : ℝ) (i : Fin 7) (q : ℕ) (a : ℤ) (start H : ℕ),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y → 1 ≤ q → (H:ℝ) ≤ 2*Q →
      ‖PRZZTypeI.weightedSum q a start H (fun j => cutoffRaw F Y Q i (start+j+1))‖ ≤
        C*Real.rpow (q:ℝ) (1/2+eps)*(a.natAbs.gcd q)*(1+(H:ℝ)/q) := by
  obtain ⟨C,hC,h⟩ := PRZZTypeI.weighted_bound hWeil eps heps
  obtain ⟨B,hB,hvar⟩ := variation_uniform F hF lo hi hlo hs
  refine ⟨C*(B+1),by positivity,?_⟩
  intro Y Q i q a start H hL hQ hQY hq hH
  have hb := h q hq a start H (fun j => cutoffRaw F Y Q i (start+j+1))
  have hv := hvar Y Q i start H hL hQ hQY hH
  have hpow : 0 ≤ Real.rpow (q:ℝ) (1/2+eps) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hbase : 0 ≤ C*Real.rpow (q:ℝ) (1/2+eps)*(a.natAbs.gcd q)*(1+(H:ℝ)/q) := by positivity
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (hv.trans (by linarith : B ≤ B+1)) hbase
  convert hh using 1 <;> ring

theorem log_length_eventually (theta : ℝ) (htheta : 0 < theta) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log (PRZZ.length theta T) :=
  (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop htheta)).eventually (eventually_ge_atTop 1)

theorem coupled_raw_eq (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (F : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hs : Function.support F ⊆ Icc lo hi)
    (Y Q kappa : ℝ) (i : Fin 7) (hY : 0 < Y) (hQ : 0 < Q) :
    PRZZMellinTypeII.coupled C D U V rho r beta nu alpha (cutoffRaw F Y Q i) kappa =
      (amplitude Y i:ℂ)*PRZZMellinTypeII.coupled C D U V rho r beta nu alpha
        (scaledCutoff (PRZZProfileSmooth.window F (profileDegree i)
          (parameterA Y Q) (parameterB Y)) Q) kappa := by
  rw [cutoffRaw_eq F lo hi hlo hs Y Q i hY hQ]
  unfold PRZZMellinTypeII.coupled
  rw [mul_sum]
  apply sum_congr rfl; intro q hq
  ring

/-- The actual seven smooth profiles receive a single DI constant before
height and the dyadic scale. This is a block supplier, not the full moment. -/
theorem coupled_bound_actual
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps : ℝ) (heps : 0 < eps) (F : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs : Function.support F ⊆ Icc lo hi) (hF : ContDiff ℝ ∞ F) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y M : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ M → M ≤ Y →
      ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Finset.Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ d ∈ Finset.Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Finset.Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ kappa : ℝ, 0 < kappa →
      ‖PRZZMellinTypeII.coupled C D U V rho r beta nu alpha (cutoffRaw F Y M i) kappa‖ ≤
        K*(R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho) := by
  choose K hK h using fun i : Fin 7 => PRZZProfileSmooth.coupled_bound_uniform
    hDI eps heps F lo hi hlo hs hF (profileDegree i)
  let Z := ∑ i, K i
  have hZ : 0 ≤ Z := sum_nonneg (fun i hi => (hK i).le)
  refine ⟨3*Z+1,by positivity,?_⟩
  intro Y M i hL hM hMY C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    r beta nu alpha hr hb hn hal kappa hk
  have hY0 : 0 < Y := by linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨ha,hb'⟩ := parameters_unit Y M hL hM hMY
  let X := R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hX : 0 ≤ X := by dsimp [X,PRZZKloostermanInputs.diBound]; positivity
  have hKi : K i ≤ Z := single_le_sum (fun j hj => (hK j).le) (mem_univ i)
  rw [coupled_raw_eq C D U V rho r beta nu alpha F lo hi hlo hs Y M kappa i hY0 hM0,norm_mul]
  calc
    _ ≤ 3*(K i*X) := mul_le_mul (amplitude_bound Y i hL)
      (h i _ _ ha hb' C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
        r beta nu alpha hr hb hn hal M kappa hM0 hk) (norm_nonneg _) (by norm_num)
    _ ≤ (3*Z+1)*X := by nlinarith

#print axioms weight_on_support
#print axioms parameters_unit
#print axioms amplitude_bound
#print axioms raw_window
#print axioms cutoffRaw_eq
#print axioms cutoffRaw_smooth
#print axioms ordinary_uniform
#print axioms scaled_uniform
#print axioms cutoff_bounds_actual
#print axioms source_bound_actual
#print axioms variation_uniform
#print axioms weil_bound_actual
#print axioms log_length_eventually
#print axioms coupled_raw_eq
#print axioms coupled_bound_actual
end XiPrime8845.PRZZProfileScale
