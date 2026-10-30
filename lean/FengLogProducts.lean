import FengOutsideMainTerm

/-! Actual K22 products containing a logarithmic block. Polynomial absorption
retains the original finite cutoffs and shifted outer weight. Ordered products
are not doubled. No shared/shared or full K22 asymptotic is assumed. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengLogProducts
open FengAtG FengMixedInterior LogProfileSum CoprimeEndpoint BetaKernel FengLogMainTerm
set_option maxHeartbeats 1000000

abbrev Block := ℕ → ℕ → ℝ → ℝ → ℝ → Polynomial ℂ → ℂ → ℂ

def productSum (X Y : Block) (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g *
    X ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ P A *
    Y ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/(L:ℂ)

theorem productSum_swap (X Y : Block) (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    productSum X Y L θ P G A B = productSum Y X L θ G P B A := by
  unfold productSum
  congr 1
  apply sum_congr rfl
  intro g hg
  have hw : FengMixedShift.rawWeight (A/L) (B/L) g =
      FengMixedShift.rawWeight (B/L) (A/L) g := by
    unfold FengMixedShift.rawWeight
    congr 2 <;> ring
  rw [hw]
  ring

theorem log_log_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    productSum logBlock logBlock L θ P G A B =
      ConreyOuter.actualSum L θ (logProfile θ θ P) (logProfile θ θ G) A B := by
  unfold productSum ConreyOuter.actualSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [logBlock_eq_conrey L θ θ g P A (mem_Ioc.mp hg).1.ne' hθ,
    logBlock_eq_conrey L θ θ g G B (mem_Ioc.mp hg).1.ne' hθ]
  unfold conrey FengMixedShift.rawWeight BareEuler.weight
  ring

theorem log_shared_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    productSum logBlock sharedBlock L θ P G A B =
      FengMixedShift.actualSum L θ θ (logProfile θ θ P) G A B := by
  unfold productSum FengMixedShift.actualSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [logBlock_eq_conrey L θ θ g P A (mem_Ioc.mp hg).1.ne' hθ]

theorem log_outside_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    productSum logBlock outsideBlock L θ P G A B =
      FengCrossAssembly.outsideSum L θ (logProfile θ θ P) G A B := by
  unfold productSum FengCrossAssembly.outsideSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [logBlock_eq_conrey L θ θ g P A (mem_Ioc.mp hg).1.ne' hθ]

def logLogKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  24*E 1 1 5-12*(E 1 0 4+E 0 1 4)+8*E 0 0 3

def logSharedKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  -12*E 1 1 5+6*E 0 1 4

def logOutsideKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  2*E 1 (-1) 3-2*E 0 (-1) 2

theorem log_log_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    H 0 0 A B θ (logProfile θ θ P) (logProfile θ θ G) =
      logLogKernel (monomialIntegral A B θ P G) := by
  simp only [H,assemble00,Nat.add_zero,pow_zero,div_one,logLogKernel]
  unfold monomialIntegral
  norm_num
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub,← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [D_logProfile θ θ (θ-v) P A hθ,D_logProfile θ θ (θ-v) G B hθ]
    push_cast
    ring
  all_goals apply Continuous.intervalIntegrable; unfold D; norm_num; fun_prop

theorem log_shared_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    -monomialIntegral A B θ (logProfile θ θ P) G 1 1 3 =
      logSharedKernel (monomialIntegral A B θ P G) := by
  unfold logSharedKernel monomialIntegral
  norm_num
  rw [← intervalIntegral.integral_neg,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [D_logProfile θ θ (θ-v) P A hθ]
    push_cast
    ring
  all_goals apply Continuous.intervalIntegrable; unfold D; norm_num; fun_prop

theorem log_outside_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    monomialIntegral A B θ (logProfile θ θ P) G 1 (-1) 1 =
      logOutsideKernel (monomialIntegral A B θ P G) := by
  unfold logOutsideKernel monomialIntegral
  norm_num
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [D_logProfile θ θ (θ-v) P A hθ]
    push_cast
    ring
  all_goals
    apply Continuous.intervalIntegrable
    have hi : Continuous (fun v : ℝ => D (-1) B θ (θ-v) G) :=
      (FengInverseProfile.inverse_continuous B θ G).comp (continuous_const.sub continuous_id)
    unfold D at hi ⊢
    norm_num at hi ⊢
    fun_prop

/-- Literal shifted log/log product, including its moving endpoint. -/
theorem log_log_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum logBlock logBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => logLogKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have ht : PRZZAsymptotic.theta ≠ 0 := by norm_num [PRZZAsymptotic.theta]
  simpa only [log_log_eq _ _ _ _ _ _ ht,log_log_kernel _ _ _ _ _ ht] using
    ConreyOuter.actualSum_twoBidiscs (logProfile PRZZAsymptotic.theta PRZZAsymptotic.theta P)
      (logProfile PRZZAsymptotic.theta PRZZAsymptotic.theta G)
      (logProfile_zero _ _ P hP) (logProfile_zero _ _ G hG)

theorem log_shared_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum logBlock sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => logSharedKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have ht : PRZZAsymptotic.theta ≠ 0 := by norm_num [PRZZAsymptotic.theta]
  simpa only [log_shared_eq _ _ _ _ _ _ ht,log_shared_kernel _ _ _ _ _ ht] using
    FengMixedShift.actualSum_twoBidiscs (logProfile PRZZAsymptotic.theta PRZZAsymptotic.theta P) G
      (logProfile_zero _ _ P hP) hG

theorem log_outside_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum logBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => logOutsideKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have ht : PRZZAsymptotic.theta ≠ 0 := by norm_num [PRZZAsymptotic.theta]
  simpa only [FengCrossAssembly.OutsideAsymptotic,log_outside_eq _ _ _ _ _ _ ht,
    log_outside_kernel _ _ _ _ _ ht] using
    FengOutsideMainTerm.outsideAsymptotic (logProfile PRZZAsymptotic.theta PRZZAsymptotic.theta P) G
      (logProfile_zero _ _ P hP) hG

#print axioms productSum_swap
#print axioms log_log_eq
#print axioms log_shared_eq
#print axioms log_outside_eq
#print axioms log_log_kernel
#print axioms log_shared_kernel
#print axioms log_outside_kernel
#print axioms log_log_twoBidiscs
#print axioms log_shared_twoBidiscs
#print axioms log_outside_twoBidiscs

/-- Transposition exchanges both profiles and shifts; no equality at fixed
unequal shifts is used. -/
theorem uniform_transpose (X Y : Block) (P G : Polynomial ℂ) (K : ℂ → ℂ → ℂ)
    (h : TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum X Y L PRZZAsymptotic.theta G P p.1 p.2)
      (fun p => K p.1 p.2) atTop ElementaryGcd.twoBidiscs) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum Y X L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => K p.2 p.1) atTop ElementaryGcd.twoBidiscs := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  have hs : (p.2,p.1) ∈ ElementaryGcd.twoBidiscs := by
    rcases hp with hp | hp
    · exact Or.inl ⟨hp.2,hp.1⟩
    · apply Or.inr
      rw [ElementaryGcd.reflectedBidisc_center] at hp ⊢
      exact ⟨hp.2,hp.1⟩
  simpa only [productSum_swap Y X L PRZZAsymptotic.theta P G p.1 p.2] using hL (p.2,p.1) hs

def sharedLogKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  -12*E 1 1 5+6*E 1 0 4

def outsideLogKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  2*E (-1) 1 3-2*E (-1) 0 2

theorem shared_log_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum sharedBlock logBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => sharedLogKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have h := uniform_transpose logBlock sharedBlock P G
    (fun A B => logSharedKernel (monomialIntegral A B PRZZAsymptotic.theta G P))
    (log_shared_twoBidiscs G P hG hP)
  simpa only [logSharedKernel,sharedLogKernel,monomialIntegral_swap _ _ _ G P] using h

theorem outside_log_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock logBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => outsideLogKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have h := uniform_transpose logBlock outsideBlock P G
    (fun A B => logOutsideKernel (monomialIntegral A B PRZZAsymptotic.theta G P))
    (log_outside_twoBidiscs G P hG hP)
  simpa only [logOutsideKernel,outsideLogKernel,monomialIntegral_swap _ _ _ G P] using h

/-- All five products with at least one logarithmic block, in one theorem. -/
def logarithmicSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  productSum logBlock logBlock L θ P G A B+
  productSum logBlock sharedBlock L θ P G A B+
  productSum sharedBlock logBlock L θ P G A B+
  productSum logBlock outsideBlock L θ P G A B+
  productSum outsideBlock logBlock L θ P G A B

def logarithmicKernel (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  -6*(E 1 0 4+E 0 1 4)+8*E 0 0 3+
    2*(E 1 (-1) 3+E (-1) 1 3)-2*(E 0 (-1) 2+E (-1) 0 2)

theorem logarithmic_kernel_assemble (E : ℤ → ℤ → ℕ → ℂ) :
    logLogKernel E+logSharedKernel E+sharedLogKernel E+logOutsideKernel E+outsideLogKernel E =
      logarithmicKernel E := by
  unfold logLogKernel logSharedKernel sharedLogKernel logOutsideKernel outsideLogKernel logarithmicKernel
  ring

theorem logarithmicSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => logarithmicSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => logarithmicKernel (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [Pi.add_def,logarithmicSum,logarithmic_kernel_assemble] using
    ((((log_log_twoBidiscs P G hP hG).add (log_shared_twoBidiscs P G hP hG)).add
      (shared_log_twoBidiscs P G hP hG)).add (log_outside_twoBidiscs P G hP hG)).add
      (outside_log_twoBidiscs P G hP hG)

theorem logarithmicSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => logarithmicSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => logarithmicKernel (monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (logarithmicSum_twoBidiscs P G hP hG)

#print axioms uniform_transpose
#print axioms shared_log_twoBidiscs
#print axioms outside_log_twoBidiscs
#print axioms logarithmic_kernel_assemble
#print axioms logarithmicSum_twoBidiscs
#print axioms logarithmicSum_reflected

end XiPrime8845.FengLogProducts

