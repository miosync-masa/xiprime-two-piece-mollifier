import PRZZEmptyMomentMass

/-! Substitute the proved spatial moment into actual AFE-to-Poisson row
defects under time integration. Central modes, the infinite Fourier tail
and both sharp spatial boundary corrections are retained in the literal
subtracted expression. No decomposition or residual bound is a premise. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZActualPoissonError
open PRZZUnfrozenPoisson PRZZPrefactorMass PRZZActiveFreezeBudget PRZZEmptyMomentMass
set_option maxHeartbeats 7000000

def cover (L : ℕ) (M : ℝ) (z : PRZZAStar.Index) : ℕ :=
  L+⌈3*M⌉₊+⌈(3*M*z.1.1+|(z.2.1:ℝ)|)/z.1.2⌉₊

theorem cover_bounds (L : ℕ) (M : ℝ) (z : PRZZAStar.Index) (hv : 0 < z.1.2) :
    L ≤ cover L M z ∧ 3*M ≤ cover L M z ∧
      3*M*z.1.1+|(z.2.1:ℝ)| ≤ (cover L M z:ℝ)*z.1.2 := by
  have hv0 : (0:ℝ) < z.1.2 := by exact_mod_cast hv
  have h1 : 3*M ≤ (⌈3*M⌉₊:ℝ) := Nat.le_ceil _
  have h2 : (3*M*z.1.1+|(z.2.1:ℝ)|)/z.1.2 ≤
      (⌈(3*M*z.1.1+|(z.2.1:ℝ)|)/z.1.2⌉₊:ℝ) := Nat.le_ceil _
  refine ⟨by unfold cover; omega,?_,?_⟩
  · unfold cover
    push_cast
    have hL : (0:ℝ) ≤ L := by positivity
    have hn : (0:ℝ) ≤ ⌈(3*M*z.1.1+|(z.2.1:ℝ)|)/z.1.2⌉₊ := by positivity
    linarith
  · apply (div_le_iff₀ hv0).mp
    unfold cover
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) L,
      Nat.cast_nonneg (α := ℝ) ⌈3*M⌉₊]

def poissonPart (L J : ℕ) (F : ℝ → ℂ) (M : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (a : ℕ → ℂ) (d : ℕ) (F1 F2 : ℝ → ℂ) (t : ℝ) : ℂ :=
  arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
    (PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t J+
      (∑' k, PRZZFrozenTail.pair F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma J k t)-
      PRZZWeightedSourcePoisson.boundary L (cover L M z) F M z alpha beta sigma t)

def rowIntegral (L J : ℕ) (F : ℝ → ℂ) (M T : ℝ) (z : PRZZAStar.Index)
    (alpha beta sigma : ℂ) (a : ℕ → ℂ) (d : ℕ) (F1 F2 phi : ℝ → ℂ) : ℂ :=
  ∫ t in Icc T (2*T), phi t*(afeRow L F F1 F2 M z alpha beta sigma a d t-
    poissonPart L J F M z alpha beta sigma a d F1 F2 t)

theorem active_data (N d j l : ℕ) (D : ℝ) (F1 F2 : ℝ → ℂ)
    (z : PRZZAStar.Index) (hz : z ∈ active N d j l D 2 F1 F2) :
    0 < z.1.1 ∧ 0 < z.1.2 ∧ z.1.1.Coprime z.1.2 ∧
      F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ |(z.2.1:ℝ)| ≤ D/d ∧
      z.1 ∈ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l := by
  have hh := Finset.mem_filter.mp hz
  have hp := Finset.mem_filter.mp (Finset.mem_product.mp hh.1).1
  have hc := Finset.mem_product.mp hp.1
  have hu := (PRZZDyadic.mem_cell N j z.1.1).mp hc.1
  have hv := (PRZZDyadic.mem_cell N l z.1.2).mp hc.2
  have hf := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp hh.1).2).1).2.2
  exact ⟨by have := (Finset.mem_Icc.mp hu.1).1; omega,
    by have := (Finset.mem_Icc.mp hv.1).1; omega,hp.2.1,hh.2.1,hf.le,hp.1⟩

theorem active_small_gap (N d j l : ℕ) (T M Q eps : ℝ) (F1 F2 : ℝ → ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q)) (hheight : 8 ≤ T^(1-eps))
    (z : PRZZAStar.Index)
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2) :
    |(z.2.1:ℝ)| ≤ M*z.1.1/4 := by
  obtain ⟨hu,hv,hcop,hf,hdelta,hcell⟩ := active_data N d j l _ F1 F2 z hz
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hu0 : (0:ℝ) < z.1.1 := by exact_mod_cast hu
  exact PRZZSourceLattice.source_delta T M Q d z.1.1 eps z.2.1 hT hM hd0 hu0
    (by linarith [(hs1 hf).1]) hheight hdelta

/-- The actual difference of the literal AFE row and the full Poisson
expression is the previously estimated freezing integral. All cover and
small-gap hypotheses are supplied by the original cutoff geometry. -/
theorem row_identity (L J N d j l : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (T M Q eps : ℝ)
    (z : PRZZAStar.Index) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hs : sigma ≠ 0)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q)) (hheight : 8 ≤ T^(1-eps))
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2) :
    rowIntegral L J F M T z alpha beta sigma a d F1 F2 phi =
      ∫ t in Icc T (2*T), arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
        errorSum L F M z alpha beta sigma t := by
  obtain ⟨hu,hv,hcop,hf,hdelta,hcell⟩ := active_data N d j l _ F1 F2 z hz
  have hsmall := active_small_gap N d j l T M Q eps F1 F2 hd hT hM hs1 hheight z hz
  obtain ⟨hLB,hB,hkB⟩ := cover_bounds L M z hv
  unfold rowIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  unfold poissonPart
  rw [afe_row_eq L F F1 F2 M z alpha beta sigma a d t hd hu hv,
    poisson_eq L (cover L M z) J hLB F hF hsF M t z alpha beta sigma hM (hT.trans_le ht.1)
      hu hv hcop hs hsmall hB hkB]
  ring

theorem row_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L J N d j l : ℕ) (T M Q eps eta : ℝ)
      (z : PRZZAStar.Index) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi →
      0 < d → 0 < T → 0 < M → 0 < Q → 0 ≤ eta → |alpha.re+beta.re| ≤ eta →
      Function.support F1 ⊆ Icc (Q/2) (3*Q) → 8 ≤ T^(1-eps) →
      z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2 →
      ‖rowIntegral L J F M T z alpha beta sigma a d F1 F2 phi‖ ≤
        E*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*M)^eta*sourceCost T M eps j l*
          ‖PRZZAStar.prefactor a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨E,hE,h⟩ := PRZZPoissonAnalyticMass.row_time_budget F hF.continuous hcF hsF Z
  refine ⟨E,hE,?_⟩
  intro L J N d j l T M Q eps eta z alpha beta sigma a F1 F2 phi
    hz hs hphi hd hT hM hQ heta hshift hs1 hheight ha
  obtain ⟨hu,hv,hcop,hf,hdelta,hcell⟩ := active_data N d j l _ F1 F2 z ha
  rw [row_identity L J N d j l F hF hsF T M Q eps z alpha beta sigma a F1 F2 phi
    hd hT hM hs hs1 hheight ha]
  exact h L N d j l T M Q eps eta z alpha beta sigma a F1 F2 phi
    hz hs hphi hd hT hM hQ heta hshift hu hv hs1 hf hdelta hheight hcell

def residualMass (L J : ℕ) (F : ℝ → ℂ) (phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℝ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
        ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
          ‖rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
            (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi‖
      else 0

/-- Simultaneous substitution into every literal residual integral.
There is no residual-bound or coefficient-mass hypothesis. -/
theorem mass_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L J N K : ℕ) (js : List ℕ) (T M Q V eps eH eta : ℝ)
      (G1 G2 phi : ℝ → ℂ) (alpha beta sigma : ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi → 0 < T → 0 < M → 0 < Q →
      0 ≤ eta → |alpha.re+beta.re| ≤ eta → Function.support G1 ⊆ Icc (1/2:ℝ) 3 → 8 ≤ T^(1-eps) →
      residualMass L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma ≤
        (E*(1+1/‖sigma‖^2)*(∫ t in Icc T (2*T), ‖phi t‖))*
          emptyMoment js N K T M Q V eps eH eta G1 G2 beta alpha := by
  classical
  obtain ⟨E,hE,h⟩ := row_bound F hF hcF hsF Z
  refine ⟨E,hE,?_⟩
  intro L J N K js T M Q V eps eH eta G1 G2 phi alpha beta sigma
    hz hs hphi hT hM hQ heta hshift hs1 hheight
  unfold residualMass emptyMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases he : PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1
  · simp only [if_pos he]
    unfold rowMoment
    calc
      _ ≤ ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
          E*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*((2:ℝ)^k*M))^eta*sourceCost T ((2:ℝ)^k*M) eps j l*
            ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
              (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V)
              d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*(∫ t in Icc T (2*T), ‖phi t‖) := by
        apply Finset.sum_le_sum
        intro z ha
        exact h L J N d j l T ((2:ℝ)^k*M) Q eps eta z alpha beta sigma _ _ _ phi
          hz hs hphi (by have := (Finset.mem_Icc.mp hd).1; omega) hT (by positivity) hQ heta hshift
          (PRZZFreezeScales.scaled_support G1 Q hQ hs1) hheight ha
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z ha
        ring
  · simp [he]

def totalError (L J : ℕ) (F : ℝ → ℂ) (phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℂ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
        ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
          rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
            (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi
      else 0

theorem total_norm_le (L J : ℕ) (F phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) :
    ‖totalError L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma‖ ≤
      residualMass L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma := by
  classical
  unfold totalError residualMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  split_ifs
  · exact norm_sum_le _ _
  · simp

/-- Exact identity for the entire finite family of original row defects.
No unidentified decomposition equality is supplied as a hypothesis. -/
theorem total_identity (L J N K : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (phi : ℝ → ℂ) (js : List ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hs : sigma ≠ 0)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    totalError L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma =
      ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
        ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
          if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
            ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
              (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
              ∫ t in Icc T (2*T),
                arithmetic (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
                  (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V)
                  d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*phi t*
                    errorSum L F ((2:ℝ)^k*M) z alpha beta sigma t
          else 0 := by
  classical
  unfold totalError
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · apply Finset.sum_congr rfl
    intro z hz
    exact row_identity L J N d j l F hF hsF T ((2:ℝ)^k*M) Q eps z alpha beta sigma _ _ _ phi
      (by have := (Finset.mem_Icc.mp hd).1; omega) hT (by positivity) hs
      (PRZZFreezeScales.scaled_support G1 Q hQ hsG1) hheight hz
  · rfl

theorem phi_mass (T P : ℝ) (hT : 0 ≤ T) (phi : ℝ → ℂ)
    (hp : ∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) :
    (∫ t in Icc T (2*T), ‖phi t‖) ≤ P*T := by
  have hi : IntegrableOn (fun _ : ℝ => P) (Icc T (2*T)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh : (∫ t in Icc T (2*T), ‖phi t‖) ≤ ∫ _t in Icc T (2*T), P := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hp t ht
  apply hh.trans_eq
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ 2*T-T by linarith),smul_eq_mul]
  ring

/-- Height-uniform bound for the actual residual integrals themselves,
not just their computed coefficient charge. The source scale conditions
are explicit, and every finite truncation L,K and central cutoff J is uniform. -/
theorem scaled_residual_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L J N K : ℕ) (T M Q V eH : ℝ) (A B : ℂ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      residualMass L J F phi js N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨E,hE,hmass⟩ := mass_bound F hF hcF hsF (S+1)
  obtain ⟨D,hD,hbudget⟩ := PRZZEmptyMomentMass.empty_absorbed G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    js S r eps eta delta hS hr heps heta.le heta1 hmargin
  refine ⟨E*D,by positivity,?_⟩
  intro L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := by linarith
  have hlc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero hab hlc
  have hbn : ‖B/(Real.log T:ℂ)‖ ≤ S := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl]
    exact (div_le_div_of_nonneg_right hB hl.le).trans (div_le_self hS hL)
  have hz : ‖(1/2:ℂ)+B/(Real.log T:ℂ)‖ ≤ S+1 := by
    have hh : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
    calc
      _ ≤ ‖(1/2:ℂ)‖+‖B/(Real.log T:ℂ)‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+S := add_le_add hh.le hbn
      _ ≤ S+1 := by linarith
  have hstrip := scaled_strip A B S (Real.log T) eta hl heta hleta hA hB
  have hm := hmass L J N K js T M Q V eps eH eta G1 G2 phi _ _ _
    hz hs hphi ht hM hQ heta.le hstrip hsG1 hheight
  have hshift : 1+1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ 1+(Real.log T)^2/r^2 := by
    have he : 1/‖(A+B)/(Real.log T:ℂ)‖^2 = (Real.log T)^2/‖A+B‖^2 := by
      rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      field_simp
    rw [he]
    gcongr
  have hw : 0 ≤ emptyMoment js N K T M Q V eps eH eta G1 G2
      (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    unfold emptyMoment rowMoment sourceCost PRZZFreezeScales.ratioCap
    positivity
  have hbound := hbudget N K T M Q V eH _ _ hN hT hL hscale hM hQ hV
    (PRZZFreezeErrorBudget.scaled_real_bound B S (Real.log T) hl hB)
    (PRZZFreezeErrorBudget.scaled_real_bound A S (Real.log T) hl hA)
  have hh := mul_le_mul hshift (phi_mass T P ht.le phi hp)
    (integral_nonneg (fun t => norm_nonneg _)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hE.le) hw
  have he := mul_le_mul_of_nonneg_left hbound (show 0 ≤ E*P by positivity)
  have hstep : residualMass L J F phi js N K T M Q V eps eH G1 G2
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
      (E*((1+(Real.log T)^2/r^2)*(P*T)))*
        emptyMoment js N K T M Q V eps eH eta G1 G2 (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    apply hm.trans
    convert hh' using 1 <;> ring
  apply hstep.trans
  convert he using 1 <;> ring

theorem scaled_total_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L J N K : ℕ) (T M Q V eH : ℝ) (A B : ℂ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖totalError L J F phi js N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_residual_bound F hF hcF hsF G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    js S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  exact (total_norm_le L J F phi js N K T M Q V eps eH G1 G2 _ _ _).trans
    (h L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp)

#print axioms cover_bounds
#print axioms active_data
#print axioms active_small_gap
#print axioms row_identity
#print axioms row_bound
#print axioms mass_bound
#print axioms total_norm_le
#print axioms total_identity
#print axioms phi_mass
#print axioms scaled_residual_bound
#print axioms scaled_total_bound
end XiPrime8845.PRZZActualPoissonError
