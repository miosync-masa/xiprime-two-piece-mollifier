import WuStirling

/-! Higher gamma jets on nested dyadic discs. Cauchy bounds are taken in the
analytic variable, never by differentiating a pointwise big-O statement. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.WuGammaJets
open WuStirling WuAuxiliary
set_option maxHeartbeats 2000000

theorem H_iterated_analytic (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (iteratedDeriv n H) s := by
  rw [iteratedDeriv_eq_iterate]
  exact (show AnalyticOnNhd ℂ H {z | 0 < z.re} from fun z hz => H_analytic z hz).iterated_deriv n s hs

theorem jet_analytic (n : ℕ) (T : ℝ) (s : ℂ)
    (hs : 0 < s.re) (h1 : s ≠ 1) (hL : Real.log T ≠ 0) :
    AnalyticAt ℂ (jet n T) s := by
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL
  exact (H_iterated_analytic n s hs).div
    ((H_analytic s hs).mul analyticAt_const) (mul_ne_zero (H_ne_zero s hs h1) (pow_ne_zero _ hLc))

theorem jet_recurrence (n : ℕ) (T : ℝ) (s : ℂ)
    (hs : 0 < s.re) (h1 : s ≠ 1) (hL : Real.log T ≠ 0) :
    jet (n+1) T s = deriv (jet n T) s/(Real.log T:ℂ)+jet n T s*jet 1 T s := by
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL
  have hH := H_ne_zero s hs h1
  have hd := ((H_iterated_analytic n s hs).differentiableAt.hasDerivAt).div
    (((H_analytic s hs).differentiableAt.hasDerivAt).mul_const ((Real.log T:ℂ)^n))
    (mul_ne_zero hH (pow_ne_zero _ hLc))
  change HasDerivAt (jet n T) _ s at hd
  rw [hd.deriv]
  simp only [jet,iteratedDeriv_succ,iteratedDeriv_zero,pow_succ,pow_zero]
  field_simp
  ring

def center (t : ℝ) : ℂ := 2+(t:ℂ)*Complex.I
def radius (n : ℕ) : ℝ := (31-(n:ℝ))/16

theorem disc_strip (T t r : ℝ) (s : ℂ) (hT : 4 ≤ T)
    (ht : t ∈ Set.Icc T (2*T)) (hr : r < 2) (hs : ‖s-center t‖ ≤ r) :
    0 < s.re ∧ s.re ≤ 4 ∧ T/2 ≤ s.im ∧ s.im ≤ 3*T ∧ s ≠ 1 := by
  have hre := (Complex.abs_re_le_norm (s-center t)).trans hs
  have him := (Complex.abs_im_le_norm (s-center t)).trans hs
  norm_num [center] at hre him
  obtain ⟨hre1,hre2⟩ := abs_le.mp hre
  obtain ⟨him1,him2⟩ := abs_le.mp him
  refine ⟨by linarith,by linarith,by linarith [ht.1],by linarith [ht.2],?_⟩
  intro he
  have : s.im = 0 := by simp [he]
  linarith [ht.1]

def jetConstant : ℕ → ℝ
  | 0 => 0
  | n+1 => 16*(1+jetConstant n)+(1+jetConstant n)*firstConstant+jetConstant n/2

theorem jetConstant_nonneg (n : ℕ) : 0 ≤ jetConstant n := by
  induction n with
  | zero => rfl
  | succ n ih => dsimp [jetConstant]; have := firstConstant_pos; positivity

/-- One rate O(1/log T) for each order up to six, on a disc wide enough to
contain the left counting line and the right line Re(s)=3. -/
theorem jet_bound (n : ℕ) (hn : n ≤ 6) (T t : ℝ) (hT : 4 ≤ T)
    (hL : 1 ≤ Real.log T) (ht : t ∈ Set.Icc T (2*T)) (s : ℂ)
    (hs : ‖s-center t‖ ≤ radius n) :
    ‖jet n T s-(1/2:ℂ)^n‖ ≤ jetConstant n/Real.log T := by
  induction n generalizing s with
  | zero =>
    have hr : radius 0 < 2 := by norm_num [radius]
    have hz := disc_strip T t _ s hT ht hr hs
    simp [jet,jetConstant,H_ne_zero s hz.1 hz.2.2.2.2]
  | succ n ih =>
    have hn6 : n ≤ 6 := by omega
    have hr : radius n < 2 := by unfold radius; have := Nat.cast_nonneg (α:=ℝ) n; linarith
    have hrs : radius (n+1)+1/16 = radius n := by simp [radius,Nat.cast_add]; ring
    have hs' : ‖s-center t‖ ≤ radius n := hs.trans (by linarith)
    have hz := disc_strip T t _ s hT ht hr hs'
    have hreg (z : ℂ) (hd : dist z s ≤ 1/16) :
        ‖z-center t‖ ≤ radius n := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z s (center t)
      rw [dist_eq_norm] at hd
      linarith
    have hpow : ‖(1/2:ℂ)^n‖ ≤ 1 := by
      rw [norm_pow]; norm_num
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hb (z : ℂ) (hd : dist z s ≤ 1/16) : ‖jet n T z‖ ≤ 1+jetConstant n := by
      have hh := ih hn6 z (hreg z hd)
      have hc : jetConstant n/Real.log T ≤ jetConstant n :=
        div_le_self (jetConstant_nonneg n) hL
      have ht := norm_sub_le_norm_sub_add_norm_sub (jet n T z) ((1/2:ℂ)^n) 0
      simp only [sub_zero] at ht
      linarith
    have hd : ‖deriv (jet n T) s‖ ≤ 16*(1+jetConstant n) := by
      have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (f:=jet n T) (c:=s) (R:=1/16) (C:=1+jetConstant n) (by norm_num)
        (DifferentiableOn.diffContOnCl (by
          intro z hzc
          have hd := Metric.closure_ball_subset_closedBall hzc
          have hzz := disc_strip T t _ z hT ht hr (hreg z (Metric.mem_closedBall.mp hd))
          exact (jet_analytic n T z hzz.1 hzz.2.2.2.2 (by linarith)).differentiableAt.differentiableWithinAt))
        (fun z hz => hb z (Metric.mem_sphere.mp hz).le)
      convert hh using 1; ring
    have hfirst := jet_one_bound T s hT hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1
    have hnerr := ih hn6 s hs'
    have hnorm := hb s (by simp)
    have hLp : 0 < Real.log T := by linarith
    rw [jet_recurrence n T s hz.1 hz.2.2.2.2 hLp.ne',pow_succ]
    have he : deriv (jet n T) s/(Real.log T:ℂ)+jet n T s*jet 1 T s-
        (1/2:ℂ)^n*(1/2) =
        deriv (jet n T) s/(Real.log T:ℂ)+
          jet n T s*(jet 1 T s-1/2)+(jet n T s-(1/2:ℂ)^n)*(1/2) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    have hmul := mul_le_mul hnorm hfirst (norm_nonneg _)
      (by have := jetConstant_nonneg n; positivity : 0 ≤ 1+jetConstant n)
    have herr := mul_le_mul_of_nonneg_right hnerr (by norm_num : (0:ℝ) ≤ 1/2)
    have hder := div_le_div_of_nonneg_right hd hLp.le
    norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
    apply (add_le_add (add_le_add hder hmul) herr).trans_eq
    rw [jetConstant]
    ring

#print axioms H_iterated_analytic
#print axioms jet_analytic
#print axioms jet_recurrence
#print axioms disc_strip
#print axioms jetConstant_nonneg
#print axioms jet_bound
end XiPrime8845.WuGammaJets

