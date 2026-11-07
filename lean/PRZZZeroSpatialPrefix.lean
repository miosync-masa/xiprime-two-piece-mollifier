import PRZZZeroNativeCompletion
import PRZZZeroBoundaryHeight

/-! The ACTUAL strict native M grid is an initial dyadic segment.
Its exact lower/upper spatial complement is identified after x=m/v,
with a proved radius at least T^4. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZZeroSpatialPrefix
open Finset
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem exists_scale (T : ℝ) : ∃ k : ℕ, T^(4:ℝ) ≤ (2:ℝ)^k := by
  obtain ⟨k,hk⟩ := exists_nat_gt (T^(4:ℝ))
  refine ⟨k,hk.le.trans ?_⟩
  exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := k)))

def firstIndex (T : ℝ) : ℕ := Nat.find (exists_scale T)

theorem radius (T : ℝ) : T^(4:ℝ) ≤ (2:ℝ)^(firstIndex T) := Nat.find_spec (exists_scale T)

theorem index_iff (T : ℝ) (s : ℕ) : (2:ℝ)^s < T^(4:ℝ) ↔ s < firstIndex T := by
  constructor
  · intro h
    by_contra hn
    have hh : (2:ℝ)^(firstIndex T) ≤ (2:ℝ)^s :=
      pow_le_pow_right₀ (by norm_num) (le_of_not_gt hn)
    linarith [radius T]
  · intro h
    exact lt_of_not_ge (Nat.find_min (exists_scale T) h)

theorem strict_grid (T : ℝ) (L : ℕ) (hL : PRZZLiteralExhaustion.spatialLength T ≤ L) :
    (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)) = range (firstIndex T) := by
  ext s
  simp only [Finset.mem_filter,Finset.mem_range]
  constructor
  · intro hs
    exact (index_iff T s).mp hs.2
  · intro hs
    have hp := (index_iff T s).mpr hs
    have hh := PRZZLiteralExhaustion.strict_index_lt T s hp
    exact ⟨by omega,hp⟩

theorem prefix_sum (P : ℝ → ℂ) (K : ℕ) (v x : ℝ) (hv : v ≠ 0) :
    (∑ s ∈ range K, PRZZWRowLimit.profile P (((2:ℝ)^s/v)⁻¹*x)) =
      P (v*x/(2:ℝ)^K)-P (v*x) := by
  have he (s : ℕ) : PRZZWRowLimit.profile P (((2:ℝ)^s/v)⁻¹*x) =
      PRZZAFEProgression.piece P ((2:ℝ)^s) (v*x) := by
    rw [PRZZWRowLimit.profile_piece]
    congr 1
    field_simp
  simp_rw [he]
  simpa only [mul_one,div_one] using PRZZAFEProgression.piece_telescope P 1 (v*x) K

/-- In particular the lower boundary is P(v*x), not P(x).  The upper
radius is the first excluded M scale, not the final included one. -/
theorem native_complement (P : ℝ → ℂ) (T : ℝ) (L : ℕ) (v x : ℝ)
    (hL : PRZZLiteralExhaustion.spatialLength T ≤ L) (hv : v ≠ 0) :
    1-(∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
      PRZZWRowLimit.profile P (((2:ℝ)^s/v)⁻¹*x)) =
        P (v*x)+(1-P (v*x/(2:ℝ)^(firstIndex T))) := by
  rw [strict_grid T L hL,prefix_sum P (firstIndex T) v x hv]
  ring

/-- Integrability comes from the actual source core, not an assumed
Fubini or boundary-integrability premise. -/
theorem boundary_integral (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hr : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (L : ℕ) (T u v delta : ℝ) (sigma : ℂ)
    (hL : PRZZLiteralExhaustion.spatialLength T ≤ L) (hT : 0 < T)
    (hu : 0 < u) (hv : 0 < v) (hd : delta ≠ 0) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∫ x in Set.Ioi (0:ℝ),
      (1-(∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
        PRZZWRowLimit.profile (fun y => (P y:ℂ)) (((2:ℝ)^s/v)⁻¹*x)))*
          PRZZZeroGap.core Phi T (u*v) sigma delta x) =
      (∫ x in Set.Ioi (0:ℝ), (P (v*x):ℂ)*PRZZZeroGap.core Phi T (u*v) sigma delta x)+
      (∫ x in Set.Ioi (0:ℝ), ((1-P (v*x/(2:ℝ)^(firstIndex T)):ℝ):ℂ)*
        PRZZZeroGap.core Phi T (u*v) sigma delta x) := by
  have hcore := (PRZZZeroSpatialLimit.spatial_limit P hP hm hlo hhi hl hr Phi hPhi hcPhi hsPhi
    T (u*v) sigma delta hT (mul_pos hu hv) hs hn hd).1
  have hw (w : ℝ → ℂ) (hc : Continuous w) (hb : ∀ x : ℝ, ‖w x‖ ≤ 1) :
      IntegrableOn (fun x => w x*PRZZZeroGap.core Phi T (u*v) sigma delta x) (Set.Ioi (0:ℝ)) := by
    apply hcore.norm.mono' (hc.aestronglyMeasurable.mul hcore.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro x
    change ‖w x*PRZZZeroGap.core Phi T (u*v) sigma delta x‖ ≤
      ‖PRZZZeroGap.core Phi T (u*v) sigma delta x‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)).trans_eq (one_mul _)
  have hlow := hw (fun x => (P (v*x):ℂ)) (by fun_prop) (by
    intro x
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hlo _)]
    exact hhi _)
  have hhigh := hw (fun x => ((1-P (v*x/(2:ℝ)^(firstIndex T)):ℝ):ℂ)) (by fun_prop) (by
    intro x
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hhi _))]
    linarith [hlo (v*x/(2:ℝ)^(firstIndex T))])
  rw [← integral_add hlow hhigh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [native_complement (fun y => (P y:ℂ)) T L v x hL hv.ne']
  push_cast
  ring

/-- The native strict-M spatial boundary integral itself, at every
nonzero signed gap, with constants before L,T,u,v and the shift family. -/
theorem native_boundary_power (P : ℝ → ℝ) (hP : Continuous P) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (r theta rate : ℝ) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (T u v delta : ℝ) (A B : ℂ),
      PRZZLiteralExhaustion.spatialLength T ≤ L → 4 ≤ T → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → 0 < u → u ≤ T^theta → 0 < v → v ≤ T →
      1 ≤ u*v → u*v ≤ T^2 → 1 ≤ |delta| →
      ‖∫ x in Set.Ioi (0:ℝ),
        (1-(∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
          PRZZWRowLimit.profile (fun y => (P y:ℂ)) (((2:ℝ)^s/v)⁻¹*x)))*
            PRZZZeroGap.core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x‖ ≤
              C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hloB⟩ := PRZZZeroBoundaryHeight.lower_integral Phi hPhi hcPhi hsPhi r theta rate hr htheta
  obtain ⟨D,hD,hhiB⟩ := PRZZZeroBoundaryHeight.upper_integral Phi hPhi hcPhi hsPhi r rate hr hrate
  refine ⟨C+D,by positivity,?_⟩
  intro L T u v delta A B hL hT hsep hn hu huT hv hvT hp hpT hd
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hlog.ne')
  have hd0 : delta ≠ 0 := abs_pos.mp (by linarith)
  rw [boundary_integral P hP hm hlo hhi hl hright Phi hPhi hcPhi hsPhi L T u v delta _
    hL hT0 hu hv hd0 hs hn]
  have h1 := hloB P T u v delta A B hlo hhi hright (by linarith) hsep hn hu.le huT hp hpT hd
  have hR : T^4/2 ≤ (2:ℝ)^(firstIndex T) := by
    have hh := radius T
    rw [Real.rpow_ofNat] at hh
    nlinarith [sq_nonneg (T^2)]
  have h2 := hhiB P T ((2:ℝ)^(firstIndex T)) u v delta A B hlo hhi hl hT hsep hn hR hv hvT hp hpT hd0
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

#print axioms boundary_integral
#print axioms native_boundary_power
#print axioms exists_scale
#print axioms radius
#print axioms index_iff
#print axioms strict_grid
#print axioms prefix_sum
#print axioms native_complement
end XiPrime8845.PRZZZeroSpatialPrefix
