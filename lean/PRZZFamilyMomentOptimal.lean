import PRZZBasisPairedBody
import PRZZCappedGammaDefect
import PRZZCappedMainTerm

/-! Actual mixed moments, not a literal proxy: both central branches,
the evaluated body tail, zero correction, Gamma defect and the complete
AFE replacement are assembled before the height-dependent finite family.
All analytic constants precede height and both profile coordinate vectors. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZFamilyMomentOptimal
open PRZZCoefficientPolarization
set_option maxHeartbeats 16000000

def error (Phi : ℝ → ℝ) (N : ℕ) (T : ℝ) (A B : ℂ) (c e : ℕ → ℂ) : ℂ :=
  PRZZMixedPoisson.moment N c e (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
    (fun t => (Phi (t/T):ℂ))-
  arithmeticPairing N (densityGcdKernel T Phi A B) c e

theorem basis_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (S r eps eH eta tau gamma delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (htau : 0 < tau) (hgamma : 0 < gamma)
    (hmargin : 6*eps+2*eta < delta) (hcost : tau+eps+eH+gamma ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (N : ℕ)
      (i j : Fin 7) (A B : ℂ),
      0 < theta → 1 ≤ N → (N:ℝ)+1 ≤ T → (N:ℝ) ≤ T^(4/7:ℝ) →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi N T A B (PRZZWitnessBasis.basis theta T i) (PRZZWitnessBasis.basis theta T j)‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  let Psi : ℝ → ℂ := fun x => (Phi x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hPsi : ContDiff ℝ ∞ Psi := Complex.ofRealCLM.contDiff.comp hPhi.1
  have hsPsi : Function.support Psi ⊆ Icc (1:ℝ) 2 := by
    intro x hx
    exact hPhi.2 (fun hz => hx (by simp [Psi,hz]))
  have hcPsi : HasCompactSupport Psi := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2))
    intro x hx; by_contra hn; exact hx (hsPsi hn)
  obtain ⟨hW,hcW,hsW⟩ := PRZZWRowLimit.profile_regular F hP hFl hFr
  let W := PRZZWRowLimit.profile F
  obtain ⟨Ca,hCa,ha⟩ := PRZZCappedMainTerm.zero_removed_reduction P Phi hP hm hlo hhi hl hright
    hPhi 6 (by norm_num) S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨Ct,hCt,ht⟩ := PRZZCappedBodyTail.nonzero_reduction F Psi hP hFl hFr hPsi.continuous
    hcPsi hsPsi 6 S r eps eH delta (by norm_num) hS hr heps.le heps1 he
  obtain ⟨Cg,hCg,hg⟩ := PRZZCappedGammaDefect.mixed_absorbed Psi hPsi.continuous hcPsi
    6 S r (by norm_num) hS hr
  obtain ⟨Cb,hCb,hb⟩ := PRZZBasisPairedBody.bound hWeil hDI K hK W W Psi
    hW hW hsW hsW hPsi hcPsi hsPsi eps eH tau gamma S r 4 heps.le (by linarith)
    htau hgamma hS hr (by norm_num)
  refine ⟨Ca+Ct+Cb+Cg,by positivity,?_⟩
  filter_upwards [ha,ht,hg,hb,eventually_ge_atTop (72:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 S))]
    with T ha ht hg hb hT hlog
  intro theta N i j A B htheta hN hNT1 hscale hY hNY hA hB hsep
  have hNT : (N:ℝ) ≤ T := by linarith
  have hc (i : Fin 7) : ∀ n ∈ Finset.Icc 1 N, ‖PRZZWitnessBasis.basis theta T i n‖ ≤ 6 :=
    fun n hn => PRZZWitnessBasis.basis_coefficient_bound i theta T htheta (by linarith) n
  let c := PRZZWitnessBasis.basis theta T i
  let e := PRZZWitnessBasis.basis theta T j
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  let R := PRZZMixedPoisson.lift (fun f => PRZZClassZeroCorrection.nonzeroResidual
    F F Psi (Nat.log 2 N+2) 0 N f T eps a b) c e
  let G := PRZZMixedPoisson.lift (fun f => ∫ t in Icc T (2*T), (Phi (t/T):ℂ)*
    PRZZZeroCross.gammaDefect N f a b t) c e
  let B0 := PRZZBasisPairedBody.paired W W Psi theta T i j N
    (PRZZCentralGridIdentity.spatial (PRZZLiteralExhaustion.spatialLength T) T) eps eH A B
  have h1 : ‖error Phi N T A B c e-R-G‖ ≤ Ca*T^delta*PRZZOptimalPowers.target N T :=
    ha c e N 0 A B (hc i) (hc j) hN hscale hA hB hsep
  have h2 : ‖R-B0‖ ≤ Ct*T^delta*PRZZOptimalPowers.target N T :=
    ht c e 0 N A B (hc i) (hc j) hN hNT hA hB hsep
  have h3 := hb theta (PRZZLiteralExhaustion.spatialLength T) N _ i j A B hN hT hNT1
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hY hNY
    (PRZZBasisPairedBody.strict_spatial_subset _ T) hA hB hsep
  change ‖B0‖ ≤ _ at h3
  have htar : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have h3' : ‖B0‖ ≤ Cb*T^delta*PRZZOptimalPowers.target N T := h3.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) hcost) hCb.le) htar)
  have h4 := hg c e N A B (hc i) (hc j) hN hNT hA hB hsep
  unfold PRZZMellinSeparation.scaledCutoff at h4
  simp only [inv_mul_eq_div] at h4
  change ‖G‖ ≤ _ at h4
  have h4' : ‖G‖ ≤ Cg*T^delta*PRZZOptimalPowers.target N T := h4.trans (by
    have hp : 1 ≤ T^delta := Real.one_le_rpow (by linarith) (by linarith)
    calc
      _ = Cg*1*PRZZOptimalPowers.target N T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCg.le) htar)
  have heq : error Phi N T A B c e = (error Phi N T A B c e-R-G)+(R-B0)+B0+G := by ring
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) h3')) h4')).trans_eq (by ring)

theorem finite_pair_bound (basis : Fin 7 → ℕ → ℂ) (N : ℕ) (T : ℝ)
    (g : ℝ → ℂ) (hg : Continuous g) (ker : ℕ → ℕ → ℂ)
    (z w : Fin 7 → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) (hw : ∀ i, ‖w i‖ ≤ 2)
    (U : ℝ) (_hU : 0 ≤ U)
    (hb : ∀ i j, ‖pairing (volume.restrict (Icc T (2*T))) N g (basis i) (basis j)-
      arithmeticPairing N ker (basis i) (basis j)‖ ≤ U) :
    ‖pairing (volume.restrict (Icc T (2*T))) N g (family basis z) (family basis w)-
      arithmeticPairing N ker (family basis z) (family basis w)‖ ≤ 196*U := by
  rw [PRZZFamilyMoment.error_family basis z w N g hg T ker]
  calc
    _ ≤ ∑ _i : Fin 7, ∑ _j : Fin 7, 4*U := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro i hi
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro j hj
      rw [norm_mul]
      have hc : ‖z i*star (w j)‖ ≤ 4 := by
        rw [norm_mul,norm_star]
        exact (mul_le_mul (hz i) (hw j) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      exact mul_le_mul hc (hb i j) (norm_nonneg _) (by norm_num)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem family_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (S r eps eH eta tau gamma delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (htau : 0 < tau) (hgamma : 0 < gamma)
    (hmargin : 6*eps+2*eta < delta) (hcost : tau+eps+eH+gamma ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (N : ℕ)
      (z w : Fin 7 → ℂ) (A B : ℂ),
      0 < theta → 1 ≤ N → (N:ℝ)+1 ≤ T → (N:ℝ) ≤ T^(4/7:ℝ) →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi N T A B (family (PRZZWitnessBasis.basis theta T) z)
        (family (PRZZWitnessBasis.basis theta T) w)‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := basis_bound hWeil hDI K hK P Phi hP hm hlo hhi hl hright
    hPhi S r eps eH eta tau gamma delta hS hr heps heps1 he heta heta1 htau hgamma hmargin hcost
  refine ⟨196*C,by positivity,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T h hsmall
  intro theta N z w A B htheta hN hNT hscale hY hNY hz hw hA hB hsep
  have hN0 : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hT0 : 0 < T := by linarith
  have hg : Continuous (fun t : ℝ => (Phi (t/T):ℂ)*
      (riemannZeta (PRZZAFEDual.leftArg (A/(Real.log T:ℂ)) t)*
        riemannZeta (PRZZAFEDual.rightArg (B/(Real.log T:ℂ)) t))) :=
    (Complex.continuous_ofReal.comp (hPhi.1.continuous.comp (continuous_id.div_const T))).mul
      (PRZZIntegratedDefect.zeta_continuous _ _ (hsmall.2 A hA) (hsmall.2 B hB))
  have hh := finite_pair_bound (PRZZWitnessBasis.basis theta T) N T _ hg (densityGcdKernel T Phi A B)
    z w hz hw (C*T^delta*PRZZOptimalPowers.target N T) (by unfold PRZZOptimalPowers.target; positivity)
    (fun i j => h theta N i j A B htheta hN hNT hscale hY hNY hA hB hsep)
  change ‖error Phi N T A B _ _‖ ≤ _ at hh
  exact hh.trans_eq (by ring)

/-- Every positive final loss is available; none is fixed by the Weil/DI
loss parameters. The two coordinate vectors and the basis may vary with T. -/
theorem moment_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (N : ℕ)
      (z w : Fin 7 → ℂ) (A B : ℂ),
      0 < theta → 1 ≤ N → (N:ℝ)+1 ≤ T → (N:ℝ) ≤ T^(4/7:ℝ) →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi N T A B (family (PRZZWitnessBasis.basis theta T) z)
        (family (PRZZWitnessBasis.basis theta T) w)‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  let u := min tau 1
  have hu : 0 < u := lt_min htau (by norm_num)
  have hut : u ≤ tau := min_le_left _ _
  have hu1 : u ≤ 1 := min_le_right _ _
  exact family_bound hWeil hDI K hK P Phi hP hm hlo hhi hl hright hPhi
    S r (u/64) (u/32) (u/64) (u/8) (u/8) tau hS hr
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)

theorem witness_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (N : ℕ) (A B : ℂ),
      0 < theta → 1 ≤ N → (N:ℝ)+1 ≤ T → (N:ℝ) ≤ T^(4/7:ℝ) →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi N T A B (PRZZ.coefficient PRZZ.witness theta T)
        (PRZZ.coefficient PRZZ.witness theta T)‖ ≤ C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := moment_bound hWeil hDI K hK P Phi hP hm hlo hhi hl hright hPhi tau S r htau hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro theta N A B htheta hN hNT hscale hY hNY hA hB hsep
  rw [PRZZWitnessBasis.witness_expansion]
  exact h theta N _ _ A B htheta hN hNT hscale hY hNY
    (fun i => (PRZZWitnessBasis.coordinates_unit i).trans (by norm_num))
    (fun i => (PRZZWitnessBasis.coordinates_unit i).trans (by norm_num)) hA hB hsep

set_option backward.isDefEq.respectTransparency false in
/-- The actual floor cutoff and tau=2.5e-7 give an error o(T), uniformly
over the displayed bounded separated shift family. This is still the
compact-window moment, not an asserted replacement of the public axiom. -/
theorem witness_uniform_normalized (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi (PRZZ.cutoff (4/7-1/1000000) T) T A B
        (PRZZ.coefficient PRZZ.witness (4/7-1/1000000) T)
        (PRZZ.coefficient PRZZ.witness (4/7-1/1000000) T)‖/T < eps := by
  let theta : ℝ := 4/7-1/1000000
  have htheta : 0 < theta := by dsimp [theta]; norm_num
  have hgap : 0 < 1-theta := by dsimp [theta]; norm_num
  obtain ⟨C,hC,h⟩ := witness_bound hWeil hDI K hK P Phi hP hm hlo hhi hl hright hPhi
    (1/4000000) S r (by norm_num) hS hr
  have hz := PRZZWitnessMass.normalized_cutoff_target.const_mul C
  intro eps heps
  filter_upwards [h,hz.eventually (eventually_lt_nhds (by simpa using heps)),
    (tendsto_rpow_atTop htheta).eventually (eventually_ge_atTop (2:ℝ)),
    (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop htheta)).eventually (eventually_ge_atTop (1:ℝ)),
    (tendsto_rpow_atTop hgap).eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (2:ℝ)]
    with T h herr hY hlogY hgapT hT
  intro A B hA hB hsep
  have hT0 : 0 < T := by linarith
  have hfloor : (PRZZ.cutoff theta T:ℝ) ≤ T^theta := Nat.floor_le (by positivity)
  have hN : 1 ≤ PRZZ.cutoff theta T := by
    unfold PRZZ.cutoff
    apply Nat.le_floor
    convert! (by norm_num : (1:ℝ) ≤ 2).trans hY using 1 <;> norm_num
  have hsum : (PRZZ.cutoff theta T:ℝ)+1 ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hgapT (Real.rpow_nonneg hT0.le theta)
    rw [← Real.rpow_add hT0] at hh
    rw [show theta+(1-theta) = 1 by ring,Real.rpow_one] at hh
    linarith
  have hscale : (PRZZ.cutoff theta T:ℝ) ≤ T^(4/7:ℝ) := hfloor.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [theta]; norm_num))
  have hb := h theta (PRZZ.cutoff theta T) A B htheta hN hsum hscale hlogY hfloor hA hB hsep
  apply (div_le_div_of_nonneg_right hb hT0.le).trans_lt
  convert herr using 1 <;> dsimp only [theta] <;> ring

#print axioms witness_bound
#print axioms witness_uniform_normalized
#print axioms finite_pair_bound
#print axioms family_bound
#print axioms moment_bound
#print axioms basis_bound
end XiPrime8845.PRZZFamilyMomentOptimal
