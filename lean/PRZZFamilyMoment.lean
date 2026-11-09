import PRZZExhaustiveAFEError
import PRZZWitnessBasis
import PRZZDiagonalKernel
import PRZZKernelComparison

/-! Exact finite-family assembly at the original time moment. Both slots
are independent, so the seven witness vectors give 49 ordered pairs.
This file does not infer mixed analytic bounds from seven diagonal ones.
Integrability is supplied by continuity on the actual compact time window. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZFamilyMoment
open PRZZCoefficientPolarization PRZZDiagonalKernel
set_option maxHeartbeats 5000000

theorem polynomial_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z : ι → ℂ) (N : ℕ) (s : ℂ) :
    PRZZ.dirichletPolynomial (family basis z) N s =
      ∑ i, z i*PRZZ.dirichletPolynomial (basis i) N s := by
  classical
  simp only [PRZZ.dirichletPolynomial,family,Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,mul_div_assoc]

theorem density_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z w : ι → ℂ) (N : ℕ) (g : ℝ → ℂ) (t : ℝ) :
    density N g (family basis z) (family basis w) t =
      ∑ i, ∑ j, (z i*star (w j))*density N g (basis i) (basis j) t := by
  classical
  simp only [density,polynomial_family,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

theorem pairing_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z w : ι → ℂ) (N : ℕ) (g : ℝ → ℂ) (hg : Continuous g) (T : ℝ) :
    pairing (volume.restrict (Icc T (2*T))) N g (family basis z) (family basis w) =
      ∑ i, ∑ j, (z i*star (w j))*
        pairing (volume.restrict (Icc T (2*T))) N g (basis i) (basis j) := by
  classical
  have hi (i j : ι) : IntegrableOn
      (fun t => (z i*star (w j))*density N g (basis i) (basis j) t) (Icc T (2*T)) := by
    apply Continuous.integrableOn_Icc
    exact continuous_const.mul ((hg.mul (PRZZMollifiedTime.polynomial_continuous _ _)).mul
      (PRZZMollifiedTime.polynomial_continuous _ _).star)
  unfold pairing
  simp_rw [density_family]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl; intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]

theorem arithmetic_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z w : ι → ℂ) (N : ℕ) (K : ℕ → ℕ → ℂ) :
    arithmeticPairing N K (family basis z) (family basis w) =
      ∑ i, ∑ j, (z i*star (w j))*arithmeticPairing N K (basis i) (basis j) := by
  classical
  have he (n m : ℕ) : family basis z n*star (family basis w m)*K n m =
      ∑ i, ∑ j, z i*basis i n*(star (w j)*star (basis j m))*K n m := by
    unfold family
    rw [star_sum,Finset.sum_mul]
    simp only [Finset.mul_sum,star_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  unfold arithmeticPairing
  simp_rw [he]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ i, ∑ m ∈ Finset.Icc 1 N,
        ∑ j, z i*basis i n*(star (w j)*star (basis j m))*K n m := by
      apply Finset.sum_congr rfl; intro n hn; rw [Finset.sum_comm]
    _ = ∑ i, ∑ n ∈ Finset.Icc 1 N, ∑ j, ∑ m ∈ Finset.Icc 1 N,
        z i*basis i n*(star (w j)*star (basis j m))*K n m := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro n hn; rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro n hn
      apply Finset.sum_congr rfl; intro m hm
      ring

theorem error_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z w : ι → ℂ) (N : ℕ) (g : ℝ → ℂ) (hg : Continuous g)
    (T : ℝ) (K : ℕ → ℕ → ℂ) :
    pairing (volume.restrict (Icc T (2*T))) N g (family basis z) (family basis w)-
        arithmeticPairing N K (family basis z) (family basis w) =
      ∑ i, ∑ j, (z i*star (w j))*(
        pairing (volume.restrict (Icc T (2*T))) N g (basis i) (basis j)-
          arithmeticPairing N K (basis i) (basis j)) := by
  rw [pairing_family basis z w N g hg T,arithmetic_family]
  simp only [mul_sub,Finset.sum_sub_distrib]

/-- The left side is exactly the moment used by moment_bound, including
all AFE residuals, not an independently supplied row-budget model. -/
theorem moment_eq (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ) :
    PRZZExhaustiveAFEError.moment N a alpha beta T phi =
      pairing (volume.restrict (Icc T (2*T))) N
        (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
          riemannZeta (PRZZAFEDual.rightArg beta t))) a a := by
  unfold PRZZExhaustiveAFEError.moment pairing density PRZZMollifiedTime.mollifierWeight
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by ring)

theorem moment_error_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z : ι → ℂ) (N : ℕ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ)
    (hg : Continuous (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
      riemannZeta (PRZZAFEDual.rightArg beta t)))) :
    PRZZExhaustiveAFEError.moment N (family basis z) alpha beta T phi-
        PRZZCoupledAFE.diagonalMain N (family basis z) alpha beta T phi =
      ∑ i, ∑ j, (z i*star (z j))*(
        pairing (volume.restrict (Icc T (2*T))) N
          (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
            riemannZeta (PRZZAFEDual.rightArg beta t))) (basis i) (basis j)-
        arithmeticPairing N (diagonalKernel N alpha beta T phi) (basis i) (basis j)) := by
  rw [moment_eq,diagonalMain_eq]
  exact error_family basis z z N _ hg T _

/-- Concrete 7 by 7 assembly for the height-dependent witness basis.
No coefficient or profile is frozen at a reference height. -/
theorem witness_error_49 (theta T : ℝ) (N : ℕ) (alpha beta : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) :
    PRZZExhaustiveAFEError.moment N (PRZZ.coefficient PRZZ.witness theta T) alpha beta T phi-
        PRZZCoupledAFE.diagonalMain N (PRZZ.coefficient PRZZ.witness theta T) alpha beta T phi =
      ∑ i : Fin 7, ∑ j : Fin 7,
        (PRZZWitnessBasis.coordinates i*star (PRZZWitnessBasis.coordinates j))*(
          pairing (volume.restrict (Icc T (2*T))) N
            (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
              riemannZeta (PRZZAFEDual.rightArg beta t)))
            (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)-
          arithmeticPairing N (diagonalKernel N alpha beta T phi)
            (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)) := by
  rw [PRZZWitnessBasis.witness_expansion]
  exact moment_error_family _ _ _ _ _ _ _
    (hphi.mul (PRZZIntegratedDefect.zeta_continuous alpha beta ha hb))

/-- The remaining analytic contract is explicitly all 49 ordered pairs,
not seven self-pairings. This lemma only assembles supplied pair bounds. -/
theorem witness_error_bound (theta T : ℝ) (N : ℕ) (alpha beta : ℂ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (B : ℝ) (_hB : 0 ≤ B)
    (hpair : ∀ i j : Fin 7,
      ‖pairing (volume.restrict (Icc T (2*T))) N
          (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
            riemannZeta (PRZZAFEDual.rightArg beta t)))
          (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)-
        arithmeticPairing N (diagonalKernel N alpha beta T phi)
          (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)‖ ≤ B) :
    ‖PRZZExhaustiveAFEError.moment N (PRZZ.coefficient PRZZ.witness theta T) alpha beta T phi-
        PRZZCoupledAFE.diagonalMain N (PRZZ.coefficient PRZZ.witness theta T) alpha beta T phi‖ ≤
      49*B := by
  rw [witness_error_49 theta T N alpha beta phi hphi ha hb]
  calc
    _ ≤ ∑ i : Fin 7, ∑ j : Fin 7, B := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro j hj
      simp only [norm_mul,norm_star]
      calc
        _ ≤ 1*1*B := mul_le_mul
          (mul_le_mul (PRZZWitnessBasis.coordinates_unit i) (PRZZWitnessBasis.coordinates_unit j)
            (norm_nonneg _) (by norm_num)) (hpair i j) (norm_nonneg _) (by norm_num)
        _ = B := by ring
    _ = _ := by simp; ring

/-- Exact insertion into the original exhaustive AFE error equality.
The collective fields retain every central/tail/boundary/freeze/outside
row, both branches, zeroPair and gammaDefect. No residual is dropped. -/
theorem component_error_family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z : ι → ℂ) (L J N : ℕ) (F : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ)
    (hg : Continuous (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
      riemannZeta (PRZZAFEDual.rightArg beta t)))) :
    let a := family basis z
    PRZZExhaustiveAFEError.moment N a alpha beta T phi-
        PRZZAllPoissonAFE.model L J N F a alpha beta T phi =
      (∑ i, ∑ j, (z i*star (z j))*(
        pairing (volume.restrict (Icc T (2*T))) N
          (fun t => phi t*(riemannZeta (PRZZAFEDual.leftArg alpha t)*
            riemannZeta (PRZZAFEDual.rightArg beta t))) (basis i) (basis j)-
        arithmeticPairing N (diagonalKernel N alpha beta T phi) (basis i) (basis j)))-
      (((∫ t in Icc T (2*T), phi t*PRZZExhaustiveAFEError.field L J N F a alpha beta t)+
        ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
          PRZZExhaustiveAFEError.field L J N F a (-beta) (-alpha) t)-
        PRZZZeroCoupled.zeroPair N a alpha beta T phi)-
      ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  dsimp only
  rw [PRZZExhaustiveAFEError.original_error_eq,moment_error_family basis z N alpha beta T phi hg]

/-- The actual witness main term, with the correct shift placement.
Its Gamma defect is evaluated uniformly, not passed in as a premise. -/
theorem witness_mainterm_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ (theta : ℝ) (A B : ℂ),
      0 < theta → (PRZZ.cutoff theta T:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCoupledAFE.diagonalMain (PRZZ.cutoff theta T)
          (PRZZ.coefficient PRZZ.witness theta T) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          T (fun t => (Phi (t/T):ℂ))-PRZZ.densityGcdMainTerm PRZZ.witness PRZZ.witness
            theta T Phi A B‖ ≤
        C*Real.log T*(PRZZ.cutoff theta T:ℝ)*(1+Real.log (PRZZ.cutoff theta T)) := by
  obtain ⟨C,hC,h⟩ := PRZZKernelComparison.arithmetic_defect_bound Phi hPhi S r hS hr
  refine ⟨C*84*84,by positivity,?_⟩
  filter_upwards [h,Filter.eventually_ge_atTop (2:ℝ)] with T h hT
  intro theta A B htheta hNT hA hB hsep
  have hc (n : ℕ) : ‖PRZZ.coefficient PRZZ.witness theta T n‖ ≤ 84 := by
    rw [PRZZWitnessBasis.witness_expansion]
    exact PRZZWitnessBasis.family_coefficient_bound theta T htheta hT
      PRZZWitnessBasis.coordinates (fun i => (PRZZWitnessBasis.coordinates_unit i).trans (by norm_num)) n
  have hh := h (PRZZ.cutoff theta T) A B _ _ 84 84 hNT hA hB hsep
    (by norm_num) (by norm_num) (fun n _ => hc n) (fun n _ => hc n)
  rw [diagonalMain_eq,densityGcdMainTerm_eq]
  simpa only [arithmeticPairing,mul_sub,Finset.sum_sub_distrib,mul_assoc] using hh

/-- The evaluated main-kernel defect fits the original optimal error
scale for every positive tau. No moment estimate is a premise here. -/
theorem witness_mainterm_absorbed (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (S r tau : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htau : 0 < tau) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ (theta : ℝ) (A B : ℂ),
      0 < theta → 1 ≤ PRZZ.cutoff theta T → (PRZZ.cutoff theta T:ℝ) ≤ T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCoupledAFE.diagonalMain (PRZZ.cutoff theta T)
          (PRZZ.coefficient PRZZ.witness theta T) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          T (fun t => (Phi (t/T):ℂ))-PRZZ.densityGcdMainTerm PRZZ.witness PRZZ.witness
            theta T Phi A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target (PRZZ.cutoff theta T) T := by
  obtain ⟨C,hC,h⟩ := witness_mainterm_bound Phi hPhi S r hS hr
  obtain ⟨D,hD,hd⟩ := PRZZOptimalOuter.power_log_absorbed 2 0 tau htau
  refine ⟨2*C*D,by positivity,?_⟩
  filter_upwards [h,Filter.eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with T h hT hL
  intro theta A B htheta hN hNT hA hB hsep
  let N := PRZZ.cutoff theta T
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hlogN : Real.log N ≤ Real.log T := Real.log_le_log hN0 hNT
  have hlog : Real.log T*(1+Real.log N) ≤ 2*(Real.log T)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log T by linarith) (sub_nonneg.mpr hlogN)]
  have hp := hd T hT.le
  simp only [Real.rpow_zero,one_mul] at hp
  have hpow : (N:ℝ) ≤ (N:ℝ)^(7/4:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1:ℝ) ≤ 7/4)
  have htarget : (N:ℝ) ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact hpow.trans (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*Real.log T*(N:ℝ)*(1+Real.log N) := h theta A B htheta hNT hA hB hsep
    _ = C*(N:ℝ)*(Real.log T*(1+Real.log N)) := by ring
    _ ≤ C*(N:ℝ)*(2*(D*T^tau)) := mul_le_mul_of_nonneg_left
      (hlog.trans (mul_le_mul_of_nonneg_left hp (by norm_num))) (by positivity)
    _ ≤ C*(PRZZOptimalPowers.target N T)*(2*(D*T^tau)) := by gcongr
    _ = _ := by ring

#print axioms witness_mainterm_absorbed
#print axioms component_error_family
#print axioms witness_mainterm_bound
#print axioms witness_error_49
#print axioms witness_error_bound
#print axioms polynomial_family
#print axioms density_family
#print axioms pairing_family
#print axioms arithmetic_family
#print axioms error_family
#print axioms moment_eq
#print axioms moment_error_family
end XiPrime8845.PRZZFamilyMoment
