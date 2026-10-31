import WuRightLittlewood

/-! Wider Gamma jet discs for the moving-family horizontal argument.
The seven Cauchy steps have width 1/128, retaining radius at least 249/128.
No horizontal phase bound is assumed here. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.WuWideGamma
open WuStirling WuAuxiliary WuGammaJets
set_option maxHeartbeats 2000000

def radius (n : ℕ) : ℝ := (255-(n:ℝ))/128

def jetConstant : ℕ → ℝ
  | 0 => 0
  | n+1 => 128*(1+jetConstant n)+(1+jetConstant n)*firstConstant+jetConstant n/2

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
    have hrs : radius (n+1)+1/128 = radius n := by simp [radius,Nat.cast_add]; ring
    have hs' : ‖s-center t‖ ≤ radius n := hs.trans (by linarith)
    have hz := disc_strip T t _ s hT ht hr hs'
    have hreg (z : ℂ) (hd : dist z s ≤ 1/128) :
        ‖z-center t‖ ≤ radius n := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z s (center t)
      rw [dist_eq_norm] at hd
      linarith
    have hpow : ‖(1/2:ℂ)^n‖ ≤ 1 := by
      rw [norm_pow]; norm_num
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hb (z : ℂ) (hd : dist z s ≤ 1/128) : ‖jet n T z‖ ≤ 1+jetConstant n := by
      have hh := ih hn6 z (hreg z hd)
      have hc : jetConstant n/Real.log T ≤ jetConstant n :=
        div_le_self (jetConstant_nonneg n) hL
      have ht := norm_sub_le_norm_sub_add_norm_sub (jet n T z) ((1/2:ℂ)^n) 0
      simp only [sub_zero] at ht
      linarith
    have hd : ‖deriv (jet n T) s‖ ≤ 128*(1+jetConstant n) := by
      have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (f:=jet n T) (c:=s) (R:=1/128) (C:=1+jetConstant n) (by norm_num)
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

#print axioms jetConstant_nonneg
#print axioms jet_bound
end XiPrime8845.WuWideGamma
