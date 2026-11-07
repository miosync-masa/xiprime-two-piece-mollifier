import PRZZCentralTail
import PRZZTruncatedProgression
import PRZZCutoffPhase

/-! Remove a sharp double cutoff only after it contains the smooth support
and its reconstructed positive partner. The original AFE-to-frozen-weight
replacement is a separate error, not an equality asserted here. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform
open Set Complex
namespace XiPrime8845.PRZZSharpPoisson
open PRZZTruncatedProgression
set_option maxHeartbeats 3000000

theorem support_retained (L u v : ℕ) (delta m : ℤ) (a b : ℝ)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : b ≤ L)
    (hlo : 0 < a*u-delta) (hhi : b*u-delta ≤ (L:ℝ)*v)
    (hm : (m:ℝ) ∈ Icc a b) (hd : (v:ℤ) ∣ m*u-delta) :
    m ∈ retained L u v delta := by
  have hu0 : (0:ℝ) < u := by exact_mod_cast hu
  have hv0 : (0:ℝ) < v := by exact_mod_cast hv
  have hmul := Int.ediv_mul_cancel hd
  have he : (((m*u-delta)/v:ℤ):ℝ)*v = (m:ℝ)*u-delta := by exact_mod_cast hmul
  have hm0 : 0 < m := by exact_mod_cast (ha.trans_le hm.1)
  have hmL : m ≤ L := by exact_mod_cast (hm.2.trans hb)
  have hk0 : 0 < (m*u-delta)/v := by
    have hh : (0:ℝ) < ((m*u-delta)/v:ℤ) := by nlinarith [hm.1]
    exact_mod_cast hh
  have hkL : (m*u-delta)/v ≤ L := by
    have hh : (((m*u-delta)/v:ℤ):ℝ) ≤ L := by nlinarith [hm.2]
    exact_mod_cast hh
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hmL⟩,hd,by omega,hkL⟩

/-- Both sharp cutoffs disappear by support containment, not by assigning
smoothness to their indicators. No summability premise is required. -/
theorem sharp_eq_progression (L u v : ℕ) (delta : ℤ) (f : ℝ → ℂ) (a b : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hc : u.Coprime v)
    (hs : Function.support f ⊆ Icc a b) (ha : 0 < a) (hb : b ≤ L)
    (hlo : 0 < a*u-delta) (hhi : b*u-delta ≤ (L:ℝ)*v) :
    (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
      if m*u-k*v=delta then f m else 0) =
      ∑' j : ℤ, f ((residue u v delta:ℝ)+(v:ℝ)*j) := by
  rw [weighted_sum L u v delta hv hc (fun m _ => f m)]
  symm
  push_cast
  apply tsum_eq_sum
  intro j hj
  by_contra hf
  let m : ℤ := residue u v delta+(v:ℤ)*j
  have hfm : f (m:ℝ) ≠ 0 := by simpa [m] using hf
  have hd : (v:ℤ) ∣ m*u-delta :=
    (PRZZCongruencePoisson.progression_iff u v hv hc m delta).mpr ⟨j,rfl⟩
  have hm := support_retained L u v delta m a b hu hv ha hb hlo hhi (hs hfm) hd
  apply hj
  apply Finset.mem_image.mpr
  refine ⟨m,hm,?_⟩
  have hvz : (v:ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  simpa only [m,add_sub_cancel_left] using Int.mul_ediv_cancel_left j hvz

/-- The small-ratio condition now holds for every nonzero supported term,
including terms selected by either sharp cutoff or any arithmetic mask. -/
theorem active_small (T M Q d eps delta m u : ℝ) (FM F1 : ℝ → ℂ) (c : ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) (hnon : c*FM m*F1 (d*u) ≠ 0) :
    |delta/(m*u)| ≤ 1/2 := by
  have hm : FM m ≠ 0 := by intro h; apply hnon; simp [h]
  have hu : F1 (d*u) ≠ 0 := by intro h; apply hnon; simp [h]
  exact PRZZCutoffPhase.support_small T M Q d eps delta m u FM F1
    hT hM hQ hd hsM hs1 hm hu hdelta hheight

/-- The sharp double sum of the actual frozen W weight equals its central
Fourier block plus tail once both support endpoints fit inside the cutoff.
These explicit bounds are uniform in time and in the frequency cutoff J. -/
theorem sharp_frozen (L J : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (ht : 0 < t) (hn : 0 < z.1.1) (hm : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ (M/z.1.2)*z.1.1/4)
    (hL : 3*(M/z.1.2) ≤ L)
    (hkL : 3*(M/z.1.2)*z.1.1+|(z.2.1:ℝ)| ≤ (L:ℝ)*z.1.2) :
    (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
      if m*z.1.1-k*z.1.2= -z.2.1 then
        PRZZFrozenTail.frozen F M z alpha beta sigma t m else 0) =
      PRZZCentralTail.central F M z.1.2 (PRZZCentralTail.residue z) z alpha beta sigma t J +
        ∑' j : ℕ, PRZZFrozenTail.pair F M z.1.2 (PRZZCentralTail.residue z)
          z alpha beta sigma J j t := by
  have hN : 0 < M/(z.1.2:ℝ) := by positivity
  have hsupport := PRZZWeightFourier.support_subset (1/2) 3 (by norm_num) F
    (M/z.1.2) (2*Real.pi*z.1.1*z.1.2/t)
    ((z.2.1:ℝ)*t/((z.1.1:ℝ)*z.1.2)) (alpha+beta+1) sigma hN hsF
  have hlo : 0 < (1/2:ℝ)*(M/z.1.2)*z.1.1-((-z.2.1:ℤ):ℝ) := by
    push_cast
    have hprod : 0 < (M/(z.1.2:ℝ))*(z.1.1:ℝ) := by positivity
    nlinarith [neg_abs_le (z.2.1:ℝ)]
  have hhi : 3*(M/(z.1.2:ℝ))*z.1.1-((-z.2.1:ℤ):ℝ) ≤ (L:ℝ)*z.1.2 := by
    push_cast
    linarith [le_abs_self (z.2.1:ℝ)]
  rw [sharp_eq_progression L z.1.1 z.1.2 (-z.2.1)
    (PRZZFrozenTail.frozen F M z alpha beta sigma t)
    ((1/2)*(M/z.1.2)) (3*(M/z.1.2)) hn hm hc hsupport (by positivity) hL hlo hhi]
  simpa [PRZZTruncatedProgression.residue,PRZZCentralTail.residue] using
    PRZZCentralTail.poisson_split F hF hsF M z.1.2 (PRZZCentralTail.residue z) t z
      alpha beta sigma J hM (by exact_mod_cast hm) ht hn hm hs

/-- A single finite cutoff works for every positive time and every central
frequency cutoff. Thus the frozen sharp sums stabilize, not merely converge. -/
theorem sharp_frozen_stable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hM : 0 < M) (hn : 0 < z.1.1) (hm : 0 < z.1.2)
    (hc : z.1.1.Coprime z.1.2) (hs : sigma ≠ 0)
    (hdelta : |(z.2.1:ℝ)| ≤ (M/z.1.2)*z.1.1/4) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ t : ℝ, 0 < t → ∀ J : ℕ,
      (∑ m ∈ Finset.Icc (1:ℤ) L, ∑ k ∈ Finset.Icc (1:ℤ) L,
        if m*z.1.1-k*z.1.2= -z.2.1 then
          PRZZFrozenTail.frozen F M z alpha beta sigma t m else 0) =
        PRZZCentralTail.central F M z.1.2 (PRZZCentralTail.residue z) z alpha beta sigma t J +
          ∑' j : ℕ, PRZZFrozenTail.pair F M z.1.2 (PRZZCentralTail.residue z)
            z alpha beta sigma J j t := by
  obtain ⟨L0,hL0⟩ := exists_nat_ge (max (3*(M/(z.1.2:ℝ)))
    ((3*(M/(z.1.2:ℝ))*z.1.1+|(z.2.1:ℝ)|)/z.1.2))
  refine ⟨L0,?_⟩
  intro L hL t ht J
  have hLL : (L0:ℝ) ≤ L := by exact_mod_cast hL
  apply sharp_frozen L J F hF hsF M t z alpha beta sigma hM ht hn hm hc hs hdelta
  · exact (le_max_left _ _).trans (hL0.trans hLL)
  · exact (div_le_iff₀ (by exact_mod_cast hm : (0:ℝ) < z.1.2)).mp
      ((le_max_right _ _).trans (hL0.trans hLL))

/-- Zero cutoff terms need no ratio condition. The surviving terms gain
the source factor 64*T/(T^(1-eps))^2 before any coefficient counting. -/
theorem active_phase (T M Q d eps delta m k u v t : ℝ)
    (FM F1 : ℝ → ℂ) (c : ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) (hgap : m*u-k*v=delta) (ht : |t| ≤ 2*T) :
    ‖(c*FM m*F1 (d*u)) *
      (Complex.exp (I*((t*Real.log (k*v/(m*u)):ℝ):ℂ))-
        Complex.exp (I*((t*(-delta)/(m*u):ℝ):ℂ)))‖ ≤
      (64*T/(T^(1-eps))^2)*‖c*FM m*F1 (d*u)‖ := by
  by_cases hz : c*FM m*F1 (d*u) = 0
  · simp [hz]
  have hfm : FM m ≠ 0 := by intro h; apply hz; simp [h]
  have hf1 : F1 (d*u) ≠ 0 := by intro h; apply hz; simp [h]
  have hm0 : 0 < m := (by positivity : 0 < M/2).trans_le (hsM hfm).1
  have hu0 : 0 < u := by nlinarith [(hs1 hf1).1]
  have hsmall := active_small T M Q d eps delta m u FM F1 c hT hM hQ hd
    hsM hs1 hdelta hheight hz
  have hratio := PRZZCutoffPhase.support_ratio T M Q d eps delta m u FM F1
    hT hM hQ hd hsM hs1 hfm hf1 hdelta
  have hsquare : (delta/(m*u))^2 ≤ (4/T^(1-eps))^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (delta/(m*u)))
      (by positivity : 0 ≤ 4/T^(1-eps))).mpr hratio
    simpa only [sq_abs] using hh
  have hb : 2*|t| *delta^2/(m*u)^2 ≤ 64*T/(T^(1-eps))^2 := by
    calc
      _ = 2*|t| *(delta/(m*u))^2 := by ring
      _ ≤ 2*(2*T)*(4/T^(1-eps))^2 := by gcongr
      _ = _ := by ring
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    ((PRZZCongruencePoisson.signed_phase_error m k u v delta t
      (mul_pos hm0 hu0).ne' hgap hsmall).trans hb) (norm_nonneg _)).trans_eq (by ring)

/-- Finite families keep their exact coefficient mass and all zero masks.
There is no assumption that every summand has nonzero smooth cutoffs. -/
theorem active_phase_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (delta m k u v : ι → ℝ) (T M Q d eps t : ℝ) (FM F1 : ℝ → ℂ)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hd : 0 < d)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hdelta : ∀ i ∈ s, |delta i| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) (hgap : ∀ i ∈ s, m i*u i-k i*v i=delta i)
    (ht : |t| ≤ 2*T) :
    ‖∑ i ∈ s, (c i*FM (m i)*F1 (d*u i)) *
      (Complex.exp (I*((t*Real.log (k i*v i/(m i*u i)):ℝ):ℂ))-
        Complex.exp (I*((t*(-delta i)/(m i*u i):ℝ):ℂ)))‖ ≤
      (64*T/(T^(1-eps))^2)*∑ i ∈ s, ‖c i*FM (m i)*F1 (d*u i)‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact active_phase T M Q d eps (delta i) (m i) (k i) (u i) (v i) t FM F1 (c i)
    hT hM hQ hd hsM hs1 (hdelta i hi) hheight (hgap i hi) ht

#print axioms active_phase_sum
#print axioms active_phase
#print axioms sharp_frozen_stable
#print axioms sharp_frozen
#print axioms support_retained
#print axioms sharp_eq_progression
#print axioms active_small
end XiPrime8845.PRZZSharpPoisson
