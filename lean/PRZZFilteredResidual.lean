import PRZZWRowReindex

/-! Exact original-pair coordinates for the entire filtered empty-H
residual family. Strict gap bounds, valued cutoff zero tests, the spatial
grid and the empty Fourier-range test are not dropped. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform
open Set Complex MeasureTheory Finset
namespace XiPrime8845.PRZZFilteredResidual
open PRZZPrefactorMass PRZZActiveFreezeBudget PRZZEmptyArithmeticMass
open PRZZWRowReindex PRZZActualPoissonError PRZZL1Finite
set_option maxHeartbeats 7000000

theorem grid_sum (N : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ u ∈ PRZZDyadic.cell N j, ∑ v ∈ PRZZDyadic.cell N l, f u v) =
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, f u v := by
  rw [PRZZDyadic.sum_partition N (fun u => ∑ v ∈ Finset.Icc 1 N, f u v)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (PRZZDyadic.sum_partition N (f u)).symm

theorem active_grid (N d : ℕ) (D : ℝ) (F1 F2 : ℝ → ℂ)
    (f : ℕ → ℕ → ℤ → ℂ) :
    (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ z ∈ active N d j l D 2 F1 F2, f z.1.1 z.1.2 z.2.1) =
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N ∧
          F1 ((d:ℝ)*u) ≠ 0 ∧ F2 ((d:ℝ)*v) ≠ 0 then
        ∑ delta ∈ gaps d D, f u v delta else 0 := by
  classical
  rw [← grid_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  unfold active localIndices
  rw [frequencies_two]
  simp only [Finset.sum_filter,Finset.sum_product,Finset.sum_singleton,pairs]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N
  · by_cases h1 : F1 ((d:ℝ)*u) = 0 <;> by_cases h2 : F2 ((d:ℝ)*v) = 0 <;>
      simp [hc,h1,h2]
  · simp only [if_neg hc]
    split_ifs with hh
    · exact (hc ⟨hh.1,hh.2.1,hh.2.2.1⟩).elim
    · rfl

/-- Both dyadic labels and gcd are eliminated without pair multiplicity.
The H=2 frequency label is solely the h=1 enumeration of signed gaps. -/
theorem active_sum_original (N : ℕ) (D : ℕ → ℝ) (F1 F2 : ℝ → ℂ)
    (f : ℕ → ℕ → ℕ → ℤ → ℂ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ j ∈ range (Nat.log 2 N+1),
      ∑ l ∈ range (Nat.log 2 N+1), ∑ z ∈ active N d j l (D d) 2 F1 F2,
        f d z.1.1 z.1.2 z.2.1) =
    ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      if F1 n ≠ 0 ∧ F2 r ≠ 0 then
        ∑ delta ∈ gaps (Nat.gcd n r) (D (Nat.gcd n r)),
          f (Nat.gcd n r) (n/Nat.gcd n r) (r/Nat.gcd n r) delta else 0 := by
  classical
  simp_rw [active_grid]
  have hg := gcd_sum N (fun d u v =>
    if F1 ((d:ℝ)*u) ≠ 0 ∧ F2 ((d:ℝ)*v) ≠ 0 then
      ∑ delta ∈ gaps d (D d), f d u v delta else 0)
  have he : (∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N ∧ F1 ((d:ℝ)*u) ≠ 0 ∧ F2 ((d:ℝ)*v) ≠ 0 then
        ∑ delta ∈ gaps d (D d), f d u v delta else 0) =
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N then
          (if F1 ((d:ℝ)*u) ≠ 0 ∧ F2 ((d:ℝ)*v) ≠ 0 then
            ∑ delta ∈ gaps d (D d), f d u v delta else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : Nat.Coprime u v ∧ d*u ≤ N ∧ d*v ≤ N <;>
      by_cases h1 : F1 ((d:ℝ)*u) = 0 <;> by_cases h2 : F2 ((d:ℝ)*v) = 0 <;> simp [h,h1,h2]
  rw [he,← hg]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  have hn' : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hr' : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
  rw [hn',hr']

def originalResidual (L J n r : ℕ) (F F1 F2 : ℝ → ℂ) (M T : ℝ)
    (delta : ℤ) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (phi : ℝ → ℂ) : ℂ :=
  ∫ t in Icc T (2*T), phi t*((∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
    if (m:ℤ)*(n/Nat.gcd n r:ℕ)-(k:ℤ)*(r/Nat.gcd n r:ℕ) = -delta then
      F (M⁻¹*(m:ℝ))*F1 n*F2 r*
        term a a alpha beta (fun (x : ℕ) (t : ℝ) =>
          PRZZDyadicEnvelope.sourceW sigma (2*Real.pi*(x:ℝ)/t)) t m k n r else 0) -
    poissonPart L J F M ((n/Nat.gcd n r,r/Nat.gcd n r),(delta,1))
      alpha beta sigma a (Nat.gcd n r) F1 F2 t)

theorem originalResidual_eq (L J n r : ℕ) (F F1 F2 : ℝ → ℂ) (M T : ℝ)
    (delta : ℤ) (alpha beta sigma : ℂ) (a : ℕ → ℂ) (phi : ℝ → ℂ) :
    originalResidual L J n r F F1 F2 M T delta alpha beta sigma a phi =
      rowIntegral L J F M T ((n/Nat.gcd n r,r/Nat.gcd n r),(delta,1))
        alpha beta sigma a (Nat.gcd n r) F1 F2 phi := by
  have hn : Nat.gcd n r*(n/Nat.gcd n r) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hr : Nat.gcd n r*(r/Nat.gcd n r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
  have hn' : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by exact_mod_cast hn
  have hr' : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by exact_mod_cast hr
  unfold originalResidual rowIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  congr 2
  unfold PRZZUnfrozenPoisson.afeRow
  rw [← positive_int_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← positive_int_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Int.toNat_natCast,Int.cast_natCast,hn,hr,hn',hr']

def originalTotal (L J : ℕ) (F phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℂ := by
  classical
  let F1 := PRZZMellinSeparation.scaledCutoff G1 Q
  let F2 := PRZZMellinSeparation.scaledCutoff G2 V
  exact ∑ k ∈ range K, ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    if F1 n ≠ 0 ∧ F2 r ≠ 0 then
      ∑ delta ∈ gaps (Nat.gcd n r) (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps),
        if PRZZSourceCutoffs.poissonCutoff (Nat.gcd n r) T ((2:ℝ)^k*M) V eH ≤ 1 then
          originalResidual L J n r F F1 F2 ((2:ℝ)^k*M) T delta alpha beta sigma
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) phi else 0
    else 0

/-- Equality with every original-pair filter retained, not a new assumed
residual budget. In particular no cutoff-zero or empty-H row is counted. -/
theorem totalError_eq_original (L J : ℕ) (F phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) :
    totalError L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma =
      originalTotal L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma := by
  classical
  unfold totalError originalTotal
  dsimp only
  simp_rw [Finset.sum_comm (s := range (Nat.log 2 N+1)) (t := range K)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have he (d : ℕ) :
      (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
          ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
            (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
            rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
              (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
              (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi
        else 0) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
          if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
            rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
              (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
              (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  -- The h=1 enumeration is exact; the original AFE row has no Fourier h.
  have ha := active_sum_original N (fun _ => PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
    (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V)
    (fun d u v delta => if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH ≤ 1 then
      rowIntegral L J F ((2:ℝ)^k*M) T ((u,v),(delta,1)) alpha beta sigma
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
        (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi else 0)
  -- Replace h=1 in each active index before applying the coordinate map.
  convert ha using 1
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro z hz
    have hh : z.2.2 = 1 := by
      have hz' := (Finset.mem_filter.mp hz).1
      have hw := (Finset.mem_product.mp hz').2
      rw [frequencies_two] at hw
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hw).2
    have hez : ((z.1.1,z.1.2),(z.2.1,1)) = z := by
      rcases z with ⟨⟨u,v⟩,⟨delta,h⟩⟩
      simp only at hh
      subst h
      rfl
    rw [hez]
  · simp_rw [originalResidual_eq]

/-- The already proved target estimate now bounds the literal original
sharp-pair residual sum, with all source filters retained. -/
theorem originalTotal_bound
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
      ‖originalTotal L J F phi js N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_total_bound F hF hcF hsF G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    js S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hp hP hphi
  rw [← totalError_eq_original]
  exact h L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hp hP hphi

/-- Extend only the residue phase to signed Fourier modes. Zero and
negative modes remain explicit; they are not positive-h A* terms. -/
def signedPrefactor (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (h : ℤ) : ℂ :=
  PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha z *
    PRZZKloostermanInputs.e (-((h:ℝ)*(z.2.1:ℝ))*
      PRZZKloostermanInputs.inverseResidue z.1.2 z.1.1/z.1.2)

theorem residue_phase (z : PRZZAStar.Index) (h : ℤ) :
    PRZZFrozenTail.phase 1 (PRZZCentralTail.residue z/z.1.2) h =
      PRZZKloostermanInputs.e (-((h:ℝ)*(z.2.1:ℝ))*
        PRZZKloostermanInputs.inverseResidue z.1.2 z.1.1/z.1.2) := by
  unfold PRZZFrozenTail.phase PRZZCentralTail.residue PRZZKloostermanInputs.e
  push_cast
  congr 1
  ring

/-- The positive Fourier residue coefficient is exactly the existing
A* prefactor, including the original shift-slot swap. -/
theorem signedPrefactor_nat (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (d : ℕ)
    (alpha beta : ℂ) (z : PRZZAStar.Index) (h : ℕ) :
    signedPrefactor a F1 F2 d alpha beta z h =
      PRZZAStar.prefactor a F1 F2 d beta alpha (z.1,(z.2.1,h)) := by
  rw [PRZZUnfrozenPoisson.prefactor_eq]
  rfl

theorem normalized_mode (a : ℕ → ℂ) (F1 F2 F : ℝ → ℂ) (d : ℕ)
    (alpha beta sigma : ℂ) (z : PRZZAStar.Index) (M t : ℝ) (h : ℤ) :
    PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
      PRZZCentralTail.mode F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t h =
      signedPrefactor a F1 F2 d alpha beta z h *
        𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) (h:ℝ)/((z.1.1:ℂ)*(z.1.2:ℂ)) := by
  simp only [PRZZCentralTail.mode,inv_one,Complex.ofReal_one,one_mul,div_one]
  rw [residue_phase]
  unfold signedPrefactor
  ring

/-- Split every central mode without suppressing h=0 or h<0. The
positive coefficients reduce to the literal A* prefactor above. -/
theorem central_modes (a : ℕ → ℂ) (F1 F2 F : ℝ → ℂ) (d H : ℕ)
    (alpha beta sigma : ℂ) (z : PRZZAStar.Index) (M t : ℝ) :
    PRZZUnfrozenPoisson.arithmetic a F1 F2 d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))*
      PRZZCentralTail.central F M 1 (PRZZCentralTail.residue z/z.1.2) z alpha beta sigma t H =
      signedPrefactor a F1 F2 d alpha beta z 0*
        𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) 0/((z.1.1:ℂ)*(z.1.2:ℂ)) +
      ∑ j ∈ range H,
        (signedPrefactor a F1 F2 d alpha beta z ((j:ℤ)+1)*
          𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) ((j:ℝ)+1)/((z.1.1:ℂ)*(z.1.2:ℂ)) +
         signedPrefactor a F1 F2 d alpha beta z (-((j:ℤ)+1))*
          𝓕 (PRZZFrozenTail.frozen F M z alpha beta sigma t) (-((j:ℝ)+1))/((z.1.1:ℂ)*(z.1.2:ℂ))) := by
  unfold PRZZCentralTail.central PRZZFrozenTail.pair
  rw [mul_add,Finset.mul_sum,normalized_mode]
  simp only [Int.cast_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hp := normalized_mode a F1 F2 F d alpha beta sigma z M t ((j:ℤ)+1)
  have hm := normalized_mode a F1 F2 F d alpha beta sigma z M t (-((j:ℤ)+1))
  simp only [PRZZCentralTail.mode,inv_one,Complex.ofReal_one,one_mul,div_one,
    Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_neg] at hp hm
  simp only [Nat.cast_zero,zero_add,inv_one,Complex.ofReal_one,one_mul,div_one]
  rw [mul_add,hp,hm]

/-- Supply source geometry and both actual cutoff VALUES to the discarded
exact-phase arithmetic sum. The constant precedes all spatial scales and
the truncation. No Geometry or coefficient-mass bound is a premise. -/
theorem source_valued_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H)
    (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (N K : ℕ) (A B alpha beta : ℂ) (T M Q R d : ℝ)
      (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+alpha.re → 0 ≤ 1/2+beta.re →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      0 < M → 0 < Q → 0 < d → 1 ≤ T^(1-eps) →
      ∀ s : ℕ → ℕ → Finset (ℕ × ℕ),
      ‖PRZZDiscardedOuter.tailError F js N T alpha beta ((A+B)/(Real.log T:ℂ)) s
        (fun u v p => (PRZZMellinSeparation.scaledCutoff G Q (d*u)*
          PRZZMellinSeparation.scaledCutoff H R (d*v))*
          PRZZDiscardedOuter.sourceMask P (PRZZMellinSeparation.scaledCutoff G Q)
            K T M Q d eps u v p)‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,h⟩ := PRZZValuedCutoffs.valued_negligible F G H hF hcF hsF
    hG hH hcG hcH js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro N K A B alpha beta T M Q R d P hN hNT hT hL hsep ha hb
    hP hlo hhi hleft hright hM hQ hd hheight s
  apply h N A B alpha beta T Q R d hN hNT hT hL hsep ha hb s
    (PRZZDiscardedOuter.sourceMask P (PRZZMellinSeparation.scaledCutoff G Q) K T M Q d eps)
  exact PRZZDiscardedOuter.source_geometry P (PRZZMellinSeparation.scaledCutoff G Q)
    hP hlo hhi hleft hright N K T M Q d eps (by linarith) hM hQ hd hheight
    (PRZZFreezeScales.scaled_support G Q hQ hsG) s

#print axioms grid_sum
#print axioms active_grid
#print axioms active_sum_original
#print axioms originalResidual_eq
#print axioms totalError_eq_original
#print axioms originalTotal_bound
#print axioms residue_phase
#print axioms signedPrefactor_nat
#print axioms normalized_mode
#print axioms central_modes
#print axioms source_valued_negligible
end XiPrime8845.PRZZFilteredResidual
