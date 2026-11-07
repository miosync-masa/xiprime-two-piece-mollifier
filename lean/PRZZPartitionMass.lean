import PRZZSourceBoundaryDecay
import PRZZGroupedTime

/-! Pointwise partition mass must be aggregated before taking row suprema.
The seed is real, antitone, and valued in [0,1]. These shape hypotheses
are explicit; no uniform bound on the number of spatial pieces is used. -/
noncomputable section
open scoped BigOperators
open Finset Set Complex MeasureTheory Filter Topology
namespace XiPrime8845.PRZZPartitionMass
open PRZZAFEProgression PRZZAFEIndices PRZZSourceBoundaryDecay
set_option maxHeartbeats 3000000

theorem piece_nonneg (F : ℝ → ℝ) (hF : Antitone F) (M x : ℝ)
    (hM : 0 < M) (hx : 0 ≤ x) : 0 ≤ F (x/(2*M))-F (x/M) := by
  apply sub_nonneg.mpr
  apply hF
  apply (div_le_div_iff₀ (by positivity) hM).mpr
  nlinarith

theorem piece_norm (F : ℝ → ℝ) (hF : Antitone F) (M x : ℝ)
    (hM : 0 < M) (hx : 0 ≤ x) :
    ‖piece (fun x => (F x:ℂ)) M x‖ = F (x/(2*M))-F (x/M) := by
  rw [piece,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (piece_nonneg F hF M x hM hx)]

/-- The absolute mass of any initial segment of actual dyadic pieces is
at most one. Neither K nor the covered arithmetic cutoff enters the bound. -/
theorem piece_mass (F : ℝ → ℝ) (hF : Antitone F)
    (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (M x : ℝ) (K : ℕ) (hM : 0 < M) (hx : 0 ≤ x) :
    (∑ j ∈ range K, ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) x‖) ≤ 1 := by
  have he := piece_telescope (fun x => (F x:ℂ)) M x K
  have hr := congrArg Complex.re he
  simp only [Complex.re_sum,Complex.sub_re,Complex.ofReal_re] at hr
  have hn : (∑ j ∈ range K, ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) x‖) =
      ∑ j ∈ range K, (piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) x).re := by
    apply sum_congr rfl
    intro j hj
    rw [piece_norm F hF _ x (by positivity) hx]
    simp [piece]
  rw [hn,hr]
  linarith [hhi (x/((2:ℝ)^K*M)),hlo (x/M)]

/-- The actual gcd/gap/dyadic labels are disjoint. Even though labels and
spatial pieces grow with L, they contribute no multiplicity to this mass. -/
theorem grouped_piece_mass (L N K : ℕ) (F : ℝ → ℝ) (hF : Antitone F)
    (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1) (M : ℝ) (hM : 0 < M)
    (f : PRZZAFEIndices.Index → ℂ) :
    (∑ j ∈ range K, ∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) i.1.1 * f i‖) ≤
      ∑ i ∈ indices L N, ‖f i‖ := by
  simp_rw [← grouped]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  simp only [norm_mul,← sum_mul]
  exact (mul_le_mul_of_nonneg_right
    (piece_mass F hF hlo hhi M i.1.1 K hM (by positivity)) (norm_nonneg _)).trans_eq
      (one_mul _)

/-- Time integration of an L-uniform boundary envelope. No measurability
of the error is needed for this norm inequality (Bochner integral convention).
Actual convergence assertions still use a supplied common envelope. -/
theorem integrated_boundary (T C : ℝ) (L : ℕ) (phi E : ℝ → ℂ)
    (hphi : Continuous phi)
    (hE : ∀ t ∈ Icc T (2*T), ‖E t‖ ≤ C*tail L) :
    ‖∫ t in Icc T (2*T), phi t*E t‖ ≤
      C*tail L*(∫ t in Icc T (2*T), ‖phi t‖) := by
  apply (norm_integral_le_integral_norm _).trans
  have hi : IntegrableOn (fun t => C*tail L*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  have hh : (∫ t in Icc T (2*T), ‖phi t*E t‖) ≤
      ∫ t in Icc T (2*T), C*tail L*‖phi t‖ := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul,mul_comm (C*tail L)]
    exact mul_le_mul_of_nonneg_left (hE t ht) (norm_nonneg _)
  simpa only [integral_const_mul] using hh

theorem integrated_boundary_zero (T C : ℝ) (phi : ℝ → ℂ)
    (hphi : Continuous phi) (E : ℕ → ℝ → ℂ)
    (hE : ∀ L t, t ∈ Icc T (2*T) → ‖E L t‖ ≤ C*tail L) :
    Tendsto (fun L => ∫ t in Icc T (2*T), phi t*E L t) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun L => integrated_boundary T C L phi (E L) hphi (hE L))
  simpa using ((tendsto_const_nhds (x := C)).mul tail_zero).mul_const
    (∫ t in Icc T (2*T), ‖phi t‖)

def profile (F : ℝ → ℝ) : ℝ → ℂ := piece (fun x => (F x:ℂ)) 1

theorem profile_scaled (F : ℝ → ℝ) (M x : ℝ) :
    profile F (M⁻¹*x) = piece (fun x => (F x:ℂ)) M x := by
  unfold profile piece
  congr 2 <;> ring

def configuration (F : ℝ → ℝ) (M t : ℝ) (u v : ℕ)
    (a b sigma : ℂ) (delta : ℤ) (p : ℕ × ℕ) : ℂ :=
  if delta = ((p.2+1:ℕ):ℤ)*v-((p.1+1:ℕ):ℤ)*u ∧ |(delta:ℝ)| ≤ M*u/4 then
    PRZZSourceLattice.source (profile F) M ((u,v),(delta,0)) a b sigma t (p.1+1)
  else 0

/-- Unique signed gap and the pointwise partition mass remove both
growing Delta and M counts. The bound is uniform in K and in D. -/
theorem configuration_mass (F : ℝ → ℝ) (hF : Antitone F)
    (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (M T t : ℝ) (u v : ℕ) (a b sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hu : 0 < u) (hv : 0 < v) (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (K : ℕ) (D : Finset ℤ) (p : ℕ × ℕ) :
    (∑ j ∈ range K, ∑ delta ∈ D,
      ‖configuration F ((2:ℝ)^j*M) t u v a b sigma delta p‖) ≤
      cap 1 T ((u,v),(0,0)) a b sigma * majorant p := by
  have hsp : Function.support (profile F) ⊆ Icc (1/2:ℝ) 3 := by
    have hh := piece_support (fun x => (F x:ℂ)) 1 (by norm_num)
      (by intro x hx; simp [hleft x hx]) (by intro x hx; simp [hright x hx])
    intro x hx
    have hp := hh hx
    simp only [mul_one,one_div] at hp
    exact ⟨by simpa only [one_div] using hp.1,hp.2.trans (by norm_num)⟩
  have hc : 0 ≤ cap 1 T ((u,v),(0,0)) a b sigma*majorant p := by
    unfold cap majorant PRZZWArithmeticCutoff.decayConstant; positivity
  let delta0 : ℤ := ((p.2+1:ℕ):ℤ)*v-((p.1+1:ℕ):ℤ)*u
  have hrow (j : ℕ) (delta : ℤ) :
      ‖configuration F ((2:ℝ)^j*M) t u v a b sigma delta p‖ ≤
        if delta = delta0 then
          ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) (p.1+1)‖ *
            (cap 1 T ((u,v),(0,0)) a b sigma*majorant p) else 0 := by
    unfold configuration
    split_ifs with h h' h'
    · have hh := source_pointwise (profile F)
        ‖profile F (((2:ℝ)^j*M)⁻¹*((p.1+1:ℕ):ℝ))‖ ((2:ℝ)^j*M) T t
        ((u,v),(delta,0)) a b sigma (p.1+1) (p.2+1) (norm_nonneg _) le_rfl
        hsp (by positivity) hT ht hu hv hs hab h.2 (by omega) (by omega)
        (by dsimp only; dsimp [delta0] at h'; omega)
      rw [profile_scaled] at hh
      convert hh using 1 <;> simp only [cap,majorant,Nat.cast_add,Nat.cast_one] <;> ring
    · exact (h' h.1).elim
    · simp only [norm_zero]; exact mul_nonneg (norm_nonneg _) hc
    · simp
  calc
    _ ≤ ∑ j ∈ range K, ∑ delta ∈ D,
        if delta = delta0 then
          ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) (p.1+1)‖ *
            (cap 1 T ((u,v),(0,0)) a b sigma*majorant p) else 0 := by
      exact sum_le_sum (fun j _ => sum_le_sum (fun delta _ => hrow j delta))
    _ ≤ ∑ j ∈ range K, ‖piece (fun x => (F x:ℂ)) ((2:ℝ)^j*M) (p.1+1)‖ *
        (cap 1 T ((u,v),(0,0)) a b sigma*majorant p) := by
      apply sum_le_sum
      intro j hj
      simp only [sum_ite_eq']
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (norm_nonneg _) hc
    _ ≤ _ := by
      rw [← sum_mul]
      exact (mul_le_mul_of_nonneg_right
        (piece_mass F hF hlo hhi M (p.1+1) K hM (by positivity)) hc).trans_eq (one_mul _)

def assembled {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ)
    (F : ℝ → ℝ) (M t : ℝ) (a b sigma : ℂ) (K : ℕ) (D : Finset ℤ)
    (p : ℕ × ℕ) : ℂ :=
  ∑ i ∈ s, c i * ∑ j ∈ range K, ∑ delta ∈ D,
    configuration F ((2:ℝ)^j*M) t (u i) (v i) a b sigma delta p

def outerMass {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ)
    (T : ℝ) (a b sigma : ℂ) : ℝ :=
  ∑ i ∈ s, ‖c i‖*cap 1 T ((u i,v i),(0,0)) a b sigma

/-- The coefficient mass is computed, not assumed. Only the fixed finite
arithmetic pair set remains; K and the signed gap set D are unrestricted. -/
theorem assembled_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ)
    (F : ℝ → ℝ) (hF : Antitone F) (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (M T t : ℝ) (a b sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (ht : t ∈ Icc T (2*T)) (hu : ∀ i ∈ s, 0 < u i) (hv : ∀ i ∈ s, 0 < v i)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re) (K : ℕ) (D : Finset ℤ) (p : ℕ × ℕ) :
    ‖assembled s c u v F M t a b sigma K D p‖ ≤ outerMass s c u v T a b sigma*majorant p := by
  unfold assembled outerMass
  apply (norm_sum_le _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  rw [norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun j _ => norm_sum_le _ _)).trans
  exact configuration_mass F hF hlo hhi hleft hright M T t (u i) (v i) a b sigma
    hM hT ht (hu i hi) (hv i hi) hs hab K D p

/-- Full boundary aggregation and its time integral, uniform in the
growing spatial partition, signed gap set and containing arithmetic box. -/
theorem assembled_integral_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ)
    (F : ℝ → ℝ) (hF : Antitone F) (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (M T : ℝ) (a b sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (hu : ∀ i ∈ s, 0 < u i) (hv : ∀ i ∈ s, 0 < v i)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (K B : ℕ → ℕ) (D : ℕ → Finset ℤ) (hLB : ∀ L, L ≤ B L)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L => ∫ t in Icc T (2*T), phi t *
      ∑ p ∈ (range (B L) ×ˢ range (B L)) \ (range L ×ˢ range L),
        assembled s c u v F M t a b sigma (K L) (D L) p) atTop (𝓝 0) := by
  apply integrated_boundary_zero T (outerMass s c u v T a b sigma) phi hphi
  intro L t ht
  apply boundary_bound L (B L) (hLB L) _ _
    (by unfold outerMass cap PRZZWArithmeticCutoff.decayConstant; positivity)
  exact assembled_bound s c u v F hF hlo hhi hleft hright M T t a b sigma
    hM hT ht hu hv hs hab (K L) (D L)

def timeCoefficient (c e : ℕ → ℂ) (t : ℝ) (p : ℕ × ℕ) : ℂ :=
  (c p.1/(p.1:ℂ)^(1/2+t*I))*star (e p.2/(p.2:ℂ)^(1/2+t*I))

theorem timeCoefficient_norm (c e : ℕ → ℂ) (t : ℝ) (p : ℕ × ℕ)
    (hn : 0 < p.1) (hr : 0 < p.2) :
    ‖timeCoefficient c e t p‖ = ‖timeCoefficient c e 0 p‖ := by
  have hn0 : (0:ℝ) < p.1 := by exact_mod_cast hn
  have hr0 : (0:ℝ) < p.2 := by exact_mod_cast hr
  simp only [timeCoefficient,norm_mul,norm_star,norm_div,← Complex.ofReal_natCast p.1,
    ← Complex.ofReal_natCast p.2,norm_cpow_eq_rpow_re_of_pos hn0,
    norm_cpow_eq_rpow_re_of_pos hr0]
  simp

/-- The original mollifier pair set supplies positive gcd quotients.
Their coefficients retain both square-root denominators and time twists;
their absolute mass is independent of time and of L. -/
theorem gcd_time_cutoff (N : ℕ) (c e : ℕ → ℂ)
    (F : ℝ → ℝ) (hF : Antitone F) (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (M T : ℝ) (a b sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (K B : ℕ → ℕ) (D : ℕ → Finset ℤ) (hLB : ∀ L, L ≤ B L)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L => ∫ t in Icc T (2*T), phi t *
      ∑ p ∈ (range (B L) ×ˢ range (B L)) \ (range L ×ˢ range L),
        assembled (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) (timeCoefficient c e t)
          (fun q => q.1/Nat.gcd q.1 q.2) (fun q => q.2/Nat.gcd q.1 q.2)
          F M t a b sigma (K L) (D L) p) atTop (𝓝 0) := by
  let s := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
  let u := fun q : ℕ × ℕ => q.1/Nat.gcd q.1 q.2
  let v := fun q : ℕ × ℕ => q.2/Nat.gcd q.1 q.2
  have hu (q : ℕ × ℕ) (hq : q ∈ s) : 0 < u q := by
    have hn := (mem_Icc.mp (mem_product.mp hq).1).1
    exact Nat.div_pos (Nat.gcd_le_left q.2 hn) (Nat.gcd_pos_of_pos_left q.2 hn)
  have hv (q : ℕ × ℕ) (hq : q ∈ s) : 0 < v q := by
    have hr := (mem_Icc.mp (mem_product.mp hq).2).1
    exact Nat.div_pos (Nat.gcd_le_right q.1 hr) (Nat.gcd_pos_of_pos_right q.1 hr)
  let C := outerMass s (timeCoefficient c e 0) u v T a b sigma
  have hc : 0 ≤ C := by unfold C outerMass cap PRZZWArithmeticCutoff.decayConstant; positivity
  have he (t : ℝ) : outerMass s (timeCoefficient c e t) u v T a b sigma = C := by
    apply sum_congr rfl
    intro q hq
    rw [timeCoefficient_norm c e t q
      (mem_Icc.mp (mem_product.mp hq).1).1 (mem_Icc.mp (mem_product.mp hq).2).1]
  apply integrated_boundary_zero T C phi hphi
  intro L t ht
  apply boundary_bound L (B L) (hLB L) _ C hc
  intro p
  have hh := assembled_bound s (timeCoefficient c e t) u v F hF hlo hhi hleft hright
    M T t a b sigma hM hT ht hu hv hs hab (K L) (D L) p
  rw [he] at hh
  exact hh

#print axioms timeCoefficient_norm
#print axioms gcd_time_cutoff
#print axioms assembled_bound
#print axioms assembled_integral_zero
#print axioms configuration_mass
#print axioms profile_scaled
#print axioms piece_nonneg
#print axioms piece_norm
#print axioms piece_mass
#print axioms grouped_piece_mass
#print axioms integrated_boundary
#print axioms integrated_boundary_zero
/-- The original cutoff at d*u supplies the scale condition for every
retained signed gap. This does not assert that discarded gaps are small. -/
theorem cutoff_small_gap (G : ℝ → ℂ) (Q T M eps : ℝ) (d u : ℕ) (delta : ℤ)
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q))
    (hGu : G ((d:ℝ)*u) ≠ 0) (hd : 0 < d) (hu : 0 < u)
    (hT : 0 < T) (hM : 0 < M) (hheight : 8 ≤ T^(1-eps))
    (hdelta : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d) :
    |(delta:ℝ)| ≤ M*u/4 := by
  have hQ := (hG hGu).1
  exact PRZZSourceLattice.source_delta T M Q d u eps delta hT hM
    (by exact_mod_cast hd) (by exact_mod_cast hu)
    (by
      have hp : (0:ℝ) ≤ (d:ℝ)*u := by positivity
      nlinarith) hheight hdelta

/-- The source-cutoff mask, rather than an independently assumed small-ratio
mask, gives exactly the retained configuration. -/
theorem retained_configuration (F : ℝ → ℝ) (G : ℝ → ℂ)
    (Q T M eps t : ℝ) (d u v : ℕ) (a b sigma : ℂ) (delta : ℤ) (p : ℕ × ℕ)
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q)) (hGu : G ((d:ℝ)*u) ≠ 0)
    (hd : 0 < d) (hu : 0 < u) (hT : 0 < T) (hM : 0 < M)
    (hheight : 8 ≤ T^(1-eps)) :
    (if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d then
      if delta = ((p.2+1:ℕ):ℤ)*v-((p.1+1:ℕ):ℤ)*u then
        PRZZSourceLattice.source (profile F) M ((u,v),(delta,0)) a b sigma t (p.1+1)
      else 0 else 0) =
    (if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d then
      configuration F M t u v a b sigma delta p else 0) := by
  by_cases hh : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d
  · have hs := cutoff_small_gap G Q T M eps d u delta hG hGu hd hu hT hM hheight hh
    simp [hh,configuration,hs]
  · simp [hh]

/-- All spatial pieces and signed gaps may be retained at their own source
cutoff without paying their cardinality. The cutoff varies with the piece. -/
theorem retained_mass (F : ℝ → ℝ) (hF : Antitone F)
    (hlo : ∀ x, 0 ≤ F x) (hhi : ∀ x, F x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (G : ℝ → ℂ) (Q eps M T t : ℝ) (d u v : ℕ) (a b sigma : ℂ)
    (hG : Function.support G ⊆ Icc (Q/2) (3*Q)) (hGu : G ((d:ℝ)*u) ≠ 0)
    (hd : 0 < d) (hM : 0 < M) (hT : 0 < T) (hheight : 8 ≤ T^(1-eps))
    (ht : t ∈ Icc T (2*T)) (hu : 0 < u) (hv : 0 < v)
    (hs : sigma ≠ 0) (hab : 0 ≤ (a+b+1).re)
    (K : ℕ) (D : Finset ℤ) (p : ℕ × ℕ) :
    (∑ j ∈ range K, ∑ delta ∈ D,
      ‖if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^j*M) Q eps/d then
        if delta = ((p.2+1:ℕ):ℤ)*v-((p.1+1:ℕ):ℤ)*u then
          PRZZSourceLattice.source (profile F) ((2:ℝ)^j*M) ((u,v),(delta,0))
            a b sigma t (p.1+1) else 0 else 0‖) ≤
      cap 1 T ((u,v),(0,0)) a b sigma * majorant p := by
  apply le_trans _ (configuration_mass F hF hlo hhi hleft hright M T t u v a b sigma
    hM hT ht hu hv hs hab K D p)
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro delta hdelta
  rw [retained_configuration F G Q T ((2:ℝ)^j*M) eps t d u v a b sigma delta p
    hG hGu hd hu hT (by positivity) hheight]
  split_ifs <;> simp

/-- The supplier applies directly to the gcd-reduced AFE indices. -/
theorem gcd_cutoff_small_gap (G : ℝ → ℂ) (Q T M eps : ℝ) (n r : ℕ) (delta : ℤ)
    (hn : 0 < n) (hG : Function.support G ⊆ Icc (Q/2) (3*Q)) (hGn : G n ≠ 0)
    (hT : 0 < T) (hM : 0 < M) (hheight : 8 ≤ T^(1-eps))
    (hdelta : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/(n.gcd r:ℝ)) :
    |(delta:ℝ)| ≤ M*(n/n.gcd r:ℕ)/4 := by
  have hd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  have he : n.gcd r*(n/n.gcd r) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
  have hu : 0 < n/n.gcd r := by nlinarith
  apply cutoff_small_gap G Q T M eps (n.gcd r) (n/n.gcd r) delta hG _ hd hu hT hM hheight hdelta
  simpa only [← Nat.cast_mul,he] using hGn

/-- Exact finite decomposition with the discarded source gaps retained.
Their bound is a separate analytic obligation, not a small-gap hypothesis. -/
theorem gap_split (D : Finset ℤ) (T M Q eps d : ℝ) (f : ℤ → ℂ) :
    (∑ delta ∈ D, f delta) =
      (∑ delta ∈ D, if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d
        then f delta else 0) +
      (∑ delta ∈ D, if PRZZSourceCutoffs.deltaCutoff T M Q eps/d < |(delta:ℝ)|
        then f delta else 0) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro delta hd
  by_cases hh : |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d
  · simp [hh,not_lt.mpr hh]
  · simp [hh,lt_of_not_ge hh]

#print axioms gcd_cutoff_small_gap
#print axioms gap_split
#print axioms cutoff_small_gap
#print axioms retained_configuration
#print axioms retained_mass
end XiPrime8845.PRZZPartitionMass
