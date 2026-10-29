import FengMarkedCross
import FengMarkedLimit

/-! Completion of the marked scalar supplier, retaining the ordered-pair
convention and subtracting the coincident-prime model explicitly. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengMarkedCrossLimit
open TotientCoprime FengMarkedTail FengMertensModels FengMarkedDiagonal FengMarkedCross
set_option maxHeartbeats 1500000

def erasedModel (X : ℝ) : ℝ :=
  ∑ p ∈ primes X, ∑ q ∈ (primes X).erase p,
    (Real.log p)^2*(Real.log q)^2/((p:ℝ)*q)*cutoffLog X p q

def squareMoment (X : ℝ) : ℝ := ∑ p ∈ primes X, (Real.log p)^2/(p:ℝ)^2

theorem squareMoment_bound (X : ℝ) : squareMoment X ≤ Zeta23.XiPrime.Cdef :=
  Zeta23.XiPrime.sum_prime_log_sq_div_sq_le _

theorem cross_error_bound (X : ℝ) (hX : 0 ≤ X) :
    |FengMarkedDecomposition.cross ⌊Real.exp X⌋₊-erasedModel X| ≤
      4*TotientHarmonic.errorConstant*(moment 2 X)^2+
        2*(12*X+8*TotientHarmonic.errorConstant)*Zeta23.XiPrime.Cdef*moment 2 X := by
  let E := TotientHarmonic.errorConstant
  let K := 12*X+8*E
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi : Icc 1 ⌊Real.exp X⌋₊ = Ioc 0 ⌊Real.exp X⌋₊ := by
    ext n; simp only [mem_Icc,mem_Ioc]; omega
  unfold FengMarkedDecomposition.cross erasedModel
  rw [hi]
  change |(∑ p ∈ primes X, _) - ∑ p ∈ primes X, _| ≤ _
  rw [← sum_sub_distrib]
  change |∑ p ∈ primes X, _| ≤ _
  calc
    _ ≤ ∑ p ∈ primes X, ∑ q ∈ (primes X).erase p,
        (Real.log p)^2*(Real.log q)^2*(4*E/((p:ℝ)*q)+K*pairReciprocal p q) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro p hp
      change |(∑ q ∈ (primes X).erase p, _) - ∑ q ∈ (primes X).erase p, _| ≤ _
      rw [← sum_sub_distrib]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      have he : (Real.log p)^2*(Real.log q)^2*
          (restricted (⌊Real.exp X⌋₊/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ))) -
          (Real.log p)^2*(Real.log q)^2/((p:ℝ)*q)*cutoffLog X p q =
          ((Real.log p)^2*(Real.log q)^2)*
          (restricted (⌊Real.exp X⌋₊/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ))-
            cutoffLog X p q/((p:ℝ)*q)) := by ring
      rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(Real.log p)^2*(Real.log q)^2)]
      exact mul_le_mul_of_nonneg_left (cross_point_error X hX p q hp (mem_erase.mp hq).2) (by positivity)
    _ ≤ ∑ p ∈ primes X, ∑ q ∈ primes X,
        (Real.log p)^2*(Real.log q)^2*(4*E/((p:ℝ)*q)+K*pairReciprocal p q) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      intro q _ _
      unfold pairReciprocal
      positivity
    _ = 4*E*(moment 2 X)^2+2*K*squareMoment X*moment 2 X := by
      have he (p q : ℕ) :
          (Real.log p)^2*(Real.log q)^2*(4*E/((p:ℝ)*q)+K*pairReciprocal p q) =
          4*E*((Real.log p)^2/(p:ℝ))*((Real.log q)^2/(q:ℝ))+
          K*(((Real.log p)^2/(p:ℝ)^2)*((Real.log q)^2/(q:ℝ))+
            ((Real.log p)^2/(p:ℝ))*((Real.log q)^2/(q:ℝ)^2)) := by
        unfold pairReciprocal
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      simp_rw [he]
      simp only [sum_add_distrib,← mul_sum,← sum_mul]
      unfold moment squareMoment
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (squareMoment_bound X)
        (show 0≤2*K*moment 2 X from mul_nonneg (by positivity) (moment_nonneg _ _))
      dsimp only [E,K] at *
      nlinarith

theorem smooth_hinge (b : ℕ) (X Y : ℝ) (hYX : Y ≤ X) :
    smooth b Y = ∑ q ∈ primes X, (Real.log q)^b/(q:ℝ)*max (Y-Real.log q) 0 := by
  trans ∑ q ∈ primes Y, (Real.log q)^b/(q:ℝ)*max (Y-Real.log q) 0
  · unfold smooth
    apply sum_congr rfl
    intro q hq
    rw [max_eq_left (sub_nonneg.mpr (log_mem Y q hq).2)]
  apply sum_subset
  · apply filter_subset_filter
    exact Ioc_subset_Ioc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr hYX))
  · intro q hq hnot
    have hq0 : (0:ℝ)<q := by exact_mod_cast (mem_filter.mp hq).2.pos
    have hlog : Y < Real.log q := by
      by_contra hn
      have he : (q:ℝ) ≤ Real.exp Y := (Real.log_le_iff_le_exp hq0).mp (le_of_not_gt hn)
      apply hnot
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_filter.mp hq).2.pos,
        (Nat.le_floor_iff (Real.exp_pos Y).le).mpr he⟩,(mem_filter.mp hq).2⟩
    rw [max_eq_right (by linarith),mul_zero]

theorem nested_full (X : ℝ) :
    nested X = ∑ p ∈ primes X, ∑ q ∈ primes X,
      (Real.log p)^2*(Real.log q)^2/((p:ℝ)*q)*cutoffLog X p q := by
  unfold nested
  apply sum_congr rfl
  intro p hp
  rw [smooth_hinge 2 X (X-Real.log p) (by linarith [(log_mem X p hp).1]),mul_sum]
  apply sum_congr rfl
  intro q hq
  unfold cutoffLog
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def coincident (X : ℝ) : ℝ :=
  ∑ p ∈ primes X, (Real.log p)^4/(p:ℝ)^2*cutoffLog X p p

theorem nested_split (X : ℝ) : nested X = erasedModel X+coincident X := by
  rw [nested_full,erasedModel,coincident,← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have h := sum_erase_add (primes X)
    (fun q => (Real.log p)^2*(Real.log q)^2/((p:ℝ)*q)*cutoffLog X p q) hp
  convert h.symm using 1
  ring

theorem coincident_bound (X : ℝ) (hX : 0 ≤ X) :
    0 ≤ coincident X ∧ coincident X ≤ X^3*Zeta23.XiPrime.Cdef := by
  refine ⟨sum_nonneg (fun p _ => mul_nonneg (by positivity) (le_max_right _ _)),?_⟩
  calc
    _ ≤ X*∑ p ∈ primes X, (Real.log p)^4/(p:ℝ)^2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hv : cutoffLog X p p ≤ X := max_le
        (by linarith [(log_mem X p hp).1]) hX
      have hh := mul_le_mul_of_nonneg_left hv (show 0≤(Real.log p)^4/(p:ℝ)^2 by positivity)
      simpa only [mul_comm] using hh
    _ ≤ _ := by
      have he : Icc 1 ⌊Real.exp X⌋₊ = Ioc 0 ⌊Real.exp X⌋₊ := by
        ext n; simp only [mem_Icc,mem_Ioc]; omega
      have h := prime_fourth_square_bound X hX
      rw [he] at h
      have hh := mul_le_mul_of_nonneg_left h hX
      change X*(∑ p ∈ primes X, (Real.log p)^4/(p:ℝ)^2) ≤ _ at hh
      nlinarith

theorem cross_error_polynomial :
    ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
      |FengMarkedDecomposition.cross ⌊Real.exp X⌋₊-nested X| ≤ C*(1+X)^4 := by
  obtain ⟨D,hD,k⟩ := moment_upper 2 (by norm_num)
  let E := TotientHarmonic.errorConstant
  let F := Zeta23.XiPrime.Cdef
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  have hF : 0 ≤ F := by norm_num [F,Zeta23.XiPrime.Cdef]
  refine ⟨4*E*D^2+2*(12+8*E)*F*D+F,fun X hX => ?_⟩
  have h1 := cross_error_bound X hX
  have h2 := coincident_bound X hX
  have htri := abs_sub_le (FengMarkedDecomposition.cross ⌊Real.exp X⌋₊) (erasedModel X) (nested X)
  have he : |erasedModel X-nested X| = coincident X := by
    rw [nested_split,show erasedModel X-(erasedModel X+coincident X) = -coincident X by ring,
      abs_neg,abs_of_nonneg h2.1]
  rw [he] at htri
  have hp := k X hX
  have hn := moment_nonneg 2 X
  have hs := mul_self_le_mul_self hn hp
  have ha := mul_le_mul_of_nonneg_left hs (show 0≤4*E by positivity)
  have hb : (12*X+8*E)*moment 2 X ≤ (12+8*E)*D*(1+X)^4 := by
    calc
      _ ≤ ((12+8*E)*(1+X))*(D*(1+X)^2) := by
        gcongr
        nlinarith
      _ ≤ _ := by
        have h := pow_le_pow_right₀ (show (1:ℝ)≤1+X by linarith) (show 3≤4 by omega)
        have hh := mul_le_mul_of_nonneg_left h (show 0≤(12+8*E)*D by positivity)
        nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (show 0≤2*F by positivity)
  have hc : X^3 ≤ (1+X)^4 := (pow_le_pow_left₀ hX (by linarith) 3).trans
    (pow_le_pow_right₀ (by linarith) (by omega))
  have hc' := mul_le_mul_of_nonneg_right hc hF
  dsimp only [E,F] at ha hb' hc' ⊢
  nlinarith [htri,h1,h2.2,ha,hb',hc']

theorem cross_limit :
    Tendsto (fun X => FengMarkedDecomposition.cross ⌊Real.exp X⌋₊/X^5)
      atTop (nhds (1/120:ℝ)) := by
  obtain ⟨C,h⟩ := cross_error_polynomial
  have he := normalized_error_zero (fun X => FengMarkedDecomposition.cross ⌊Real.exp X⌋₊-nested X)
    5 (by norm_num) 0 C (by intro X hX; simpa using h X hX)
  simpa only [sub_zero,zero_add,sub_div,sub_add_cancel] using he.add nested_model_limit

theorem marked_scalar_asymptotic : FengMarkedLimit.MarkedScalarAsymptotic := by
  unfold FengMarkedLimit.MarkedScalarAsymptotic
  have h := diagonal_limit.add cross_limit
  norm_num at h
  simpa only [FengMarkedDecomposition.summatory_decomposition,add_div] using h

theorem marked_profile_twoBidiscs (P G : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => FengMarkedProfile.markedProfileSum L PRZZAsymptotic.theta
        (OuterProfile.profile PRZZAsymptotic.theta P G p.1 p.2))
      (fun p => 7*BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 5)
      atTop ElementaryGcd.twoBidiscs :=
  FengMarkedLimit.marked_profile_twoBidiscs P G marked_scalar_asymptotic

#print axioms cross_error_bound
#print axioms smooth_hinge
#print axioms nested_full
#print axioms nested_split
#print axioms coincident_bound
#print axioms cross_error_polynomial
#print axioms cross_limit
#print axioms marked_scalar_asymptotic
#print axioms marked_profile_twoBidiscs
end XiPrime8845.FengMarkedCrossLimit

