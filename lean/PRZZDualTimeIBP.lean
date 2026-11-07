import PRZZDualSmooth
import PRZZTimeDiscarded

/-! Genuine dual Gamma multiplier inside the discarded time integral.
All boundary cancellations, derivative integrability and repeated IBP
are supplied. The actual all-order Gamma jet cost is displayed, not
declared height-uniform by smoothness or by the order-zero Gamma cap. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Finset
namespace XiPrime8845.PRZZDualTimeIBP
set_option maxHeartbeats 6000000

def weight (F : ℝ → ℂ) (T k : ℝ) (a b sigma : ℂ) (t : ℝ) : ℂ :=
  PRZZAFEDual.dualMultiplier a b t*PRZZTimeAmplitude.amplitude F T k sigma t

def jetMass (F : ℝ → ℂ) (T k : ℝ) (a b sigma : ℂ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), (n.choose i:ℝ)*
    ∫ t : ℝ, ‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖*
      ‖iteratedDeriv (n-i) (PRZZTimeAmplitude.amplitude F T k sigma) t‖

theorem smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (T k : ℝ) (a b sigma : ℂ)
    (hT : 0 < T) (hk : 0 < k) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : sigma ≠ 0) :
    ContDiff ℝ ∞ (weight F T k a b sigma) :=
  (PRZZDualSmooth.multiplier_contDiff a b ha hb).mul (PRZZTimeAmplitude.smooth F hF hsF T k sigma hT hk hs)

theorem compact (F : ℝ → ℂ) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (T k : ℝ) (a b sigma : ℂ) (hT : 0 < T) :
    HasCompactSupport (weight F T k a b sigma) :=
  (PRZZTimeAmplitude.compact F hsF T k sigma hT).mul_left

theorem product_jet_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (T k : ℝ) (a b sigma : ℂ)
    (hT : 0 < T) (hk : 0 < k) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : sigma ≠ 0)
    (i j : ℕ) :
    Integrable (fun t : ℝ => ‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖*
      ‖iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t‖) := by
  have hd := PRZZDualSmooth.multiplier_contDiff a b ha hb
  have hw := PRZZTimeAmplitude.smooth F hF hsF T k sigma hT hk hs
  have hj (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
  have hc := (hd.continuous_iteratedDeriv i (hj i)).mul (hw.continuous_iteratedDeriv j (hj j))
  have hcomp : HasCompactSupport (fun t : ℝ => iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t*
      iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t) :=
    (PRZZCutoffJets.jet_support _ (PRZZTimeAmplitude.compact F hsF T k sigma hT) j).mul_left
  have hi : Integrable (fun t : ℝ => iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t*
      iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t) :=
    hc.integrable_of_hasCompactSupport hcomp
  simpa only [norm_mul] using hi.norm

theorem leibniz_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (T k : ℝ) (a b sigma : ℂ)
    (hT : 0 < T) (hk : 0 < k) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : sigma ≠ 0)
    (n : ℕ) :
    (∫ t : ℝ, ‖iteratedDeriv n (weight F T k a b sigma) t‖) ≤ jetMass F T k a b sigma n := by
  have hd := PRZZDualSmooth.multiplier_contDiff a b ha hb
  have hw := PRZZTimeAmplitude.smooth F hF hsF T k sigma hT hk hs
  have low : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
  have hi (i : ℕ) : Integrable (fun t : ℝ => (n.choose i:ℝ)*
      (‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖*
        ‖iteratedDeriv (n-i) (PRZZTimeAmplitude.amplitude F T k sigma) t‖)) :=
    (product_jet_integrable F hF hsF T k a b sigma hT hk ha hb hs i (n-i)).const_mul _
  have hbnd (t : ℝ) : ‖iteratedDeriv n (weight F T k a b sigma) t‖ ≤
      ∑ i ∈ range (n+1), (n.choose i:ℝ)*
        (‖iteratedDeriv i (PRZZAFEDual.dualMultiplier a b) t‖*
          ‖iteratedDeriv (n-i) (PRZZTimeAmplitude.amplitude F T k sigma) t‖) := by
    change ‖iteratedDeriv n (fun t => PRZZAFEDual.dualMultiplier a b t*
      PRZZTimeAmplitude.amplitude F T k sigma t) t‖ ≤ _
    rw [iteratedDeriv_fun_mul (hd.contDiffAt.of_le low) (hw.contDiffAt.of_le low)]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hh
    simp only [norm_mul,Complex.norm_natCast]
    exact le_of_eq (by ring)
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (integrable_finsetSum _ (fun i _ => hi i)) (Filter.Eventually.of_forall hbnd)).trans_eq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  unfold jetMass
  apply sum_congr rfl; intro i hh
  rw [integral_const_mul]

/-- Arbitrary-order time IBP for the actual dual Gamma/sourceW product.
The displayed cost includes every derivative of the genuine multiplier. -/
theorem discarded_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1:ℝ) 2) (T R x y B D : ℝ) (a b sigma : ℂ)
    (hT : 0 < T) (hR : 0 < R) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : sigma ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hxb : x ≤ B) (hyb : y ≤ B)
    (hD : 0 < D) (hgap : D ≤ |y-x|) (n : ℕ) :
    ‖∫ t : ℝ, exp (I*((t*Real.log (y/x):ℝ):ℂ))*weight F T (2*Real.pi*R) a b sigma t‖ ≤
      jetMass F T (2*Real.pi*R) a b sigma n*(B/D)^n := by
  have hB : 0 < B := hx.trans_le hxb
  apply (PRZZDeltaDecay.discarded_bound _ (smooth F hF hsF T _ a b sigma hT (by positivity) ha hb hs)
    (compact F hsF T _ a b sigma hT) n x y B D hx hy hxb hyb hD hgap).trans
  exact mul_le_mul_of_nonneg_right
    (leibniz_mass F hF hsF T _ a b sigma hT (by positivity) ha hb hs n) (by positivity)

#print axioms smooth
#print axioms compact
#print axioms product_jet_integrable
#print axioms leibniz_mass
#print axioms discarded_bound
end XiPrime8845.PRZZDualTimeIBP
