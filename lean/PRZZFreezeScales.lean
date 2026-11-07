import PRZZFreezeMass
import PRZZSourceRows

/-! Supply the retained ratio and product floor from the actual spatial
support and half-open dyadic cells. The resulting local cost is explicit;
its sum over outer spatial scales is not replaced by an optimized exponent. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory Complex
namespace XiPrime8845.PRZZFreezeScales
set_option maxHeartbeats 4000000

def productFloor (M : ℝ) (j l : ℕ) : ℝ :=
  Real.pi*M^2*(2:ℝ)^j/(4*(2:ℝ)^l)

def ratioCap (T eps : ℝ) : ℝ := 4/T^(1-eps)

theorem floor_pos (M : ℝ) (j l : ℕ) (hM : 0 < M) : 0 < productFloor M j l := by
  unfold productFloor; positivity

theorem product_floor (N j l : ℕ) (p : ℕ × ℕ) (M m : ℝ)
    (hM : 0 < M) (hm : M/2 ≤ m)
    (hp : p ∈ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l) :
    productFloor M j l ≤ 2*Real.pi*m^2*p.1/p.2 := by
  have hc := Finset.mem_product.mp hp
  have hu := (PRZZDyadic.mem_cell N j p.1).mp hc.1
  have hv := (PRZZDyadic.mem_cell N l p.2).mp hc.2
  have hv0 : (0:ℝ) < p.2 := by exact_mod_cast (Finset.mem_Icc.mp hv.1).1
  have hlo : (2:ℝ)^j ≤ p.1 := by exact_mod_cast hu.2.1
  have hhi : (p.2:ℝ) ≤ 2*(2:ℝ)^l := by
    have hh : (p.2:ℝ) < (2:ℝ)^(l+1) := by exact_mod_cast hv.2.2
    rw [pow_succ] at hh
    linarith
  have hm0 : 0 ≤ M/2 := by positivity
  calc
    _ = 2*Real.pi*(M/2)^2*(2:ℝ)^j/(2*(2:ℝ)^l) := by unfold productFloor; ring
    _ ≤ 2*Real.pi*m^2*p.1/p.2 := by gcongr

theorem scaled_support (F : ℝ → ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    Function.support (PRZZMellinSeparation.scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) := by
  intro x hx
  have hh := hF hx
  change Q/2 ≤ x ∧ x ≤ 3*Q
  change (1/2:ℝ) ≤ Q⁻¹*x ∧ Q⁻¹*x ≤ 3 at hh
  have h1 := mul_le_mul_of_nonneg_left hh.1 hQ.le
  have h2 := mul_le_mul_of_nonneg_left hh.2 hQ.le
  have hQn := hQ.ne'
  field_simp at h1 h2
  constructor <;> nlinarith

/-- Geometry for an actual nonzero row. No local R0 or kappa condition
is requested: both are consequences of source support and Delta cutoff. -/
theorem row_scales (N d j l : ℕ) (F1 F2 FM : ℝ → ℂ)
    (T M Q eps : ℝ) (m k : (ℕ × ℕ) → ℝ) (p : ℕ × ℕ)
    (hd : 1 ≤ d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hp : p ∈ PRZZSourceRows.rows N d j l F1 F2) (hfm : FM (m p) ≠ 0)
    (hdelta : |k p*p.2-m p*p.1| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d)
    (hheight : 8 ≤ T^(1-eps)) :
    productFloor M j l ≤ 2*Real.pi*(m p)^2*p.1/p.2 ∧
      |k p*p.2/(m p*p.1)-1| ≤ ratioCap T eps ∧
      |k p*p.2/(m p*p.1)-1| ≤ 1/2 := by
  have hp' := Finset.mem_filter.mp hp
  have hh := PRZZAmplitudeFreeze.actual_ratio T M Q d eps
    (k p*p.2-m p*p.1) (m p) (k p) p.1 p.2 FM F1 hT hM hQ
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) hsM hs1 hfm
    hp'.2.2.2.2.1 hdelta hheight (by ring)
  exact ⟨product_floor N j l p M (m p) hM (hsM hfm).1 hp'.1,hh⟩

/-- Original source-row substitution into the arithmetic/time bound.
Length, coprimality and both valued cutoff masks remain in the row set.
Zero spatial-cutoff rows are omitted by the supplied retained subset. -/
theorem source_time_bound (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (S r : ℝ) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B : ℂ) (js : List ℕ) (N d j l : ℕ)
      (T M Q V eps : ℝ) (FM : ℝ → ℂ) (s : Finset (ℕ × ℕ))
      (phase : ℕ × ℕ → ℂ) (m k : ℕ × ℕ → ℝ) (phi : ℝ → ℂ),
      ‖B‖ ≤ S → r ≤ ‖A+B‖ → 1 ≤ Real.log T → 1 ≤ N → 1 ≤ d →
      0 < T → 0 < M → 0 < Q → 8 ≤ T^(1-eps) → Continuous phi →
      Function.support FM ⊆ Icc (M/2) (3*M) →
      s ⊆ PRZZSourceRows.rows N d j l (PRZZMellinSeparation.scaledCutoff F Q)
        (PRZZMellinSeparation.scaledCutoff G V) →
      (∀ p ∈ s, FM (m p) ≠ 0) → (∀ p ∈ s, ‖phase p‖ ≤ 1) →
      (∀ p ∈ s, |k p*p.2-m p*p.1| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d) →
      ‖∫ t in Icc T (2*T), phi t*∑ p ∈ s,
        ((((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
          (F (Q⁻¹*((d:ℝ)*p.1))*G (V⁻¹*((d:ℝ)*p.2))*phase p))/((p.1:ℂ)*(p.2:ℂ)))*
          PRZZAmplitudeFreeze.error ((1/2:ℂ)+B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))
            ((2*Real.pi*(m p)^2*p.1/p.2)/t) t (k p*p.2/(m p*p.1)-1)‖ ≤
        E*(1+(Real.log T)^2/r^2)*(ratioCap T eps+2*T*(ratioCap T eps)^2)*(2*T)^2*
          ((Real.log N)^(2*PRZZGCoefficient.degree js)/(productFloor M j l)^2)*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨E,hE,hh⟩ := PRZZFreezeMass.scaled_cutoff_time_bound F G hF hG hcF hcG S r hr
  refine ⟨E,hE,?_⟩
  intro A B js N d j l T M Q V eps FM s phase m k phi hB hsep hL hN hd
    hT hM hQ hheight hphi hsM hs hfm hp hdelta
  have hgeo (p : ℕ × ℕ) (hps : p ∈ s) := row_scales N d j l _ _ FM T M Q eps m k p
    hd hT hM hQ hsM (scaled_support F Q hQ hsF) (hs hps) (hfm p hps) (hdelta p hps) hheight
  apply hh A B js N d j l T Q V (productFloor M j l) (ratioCap T eps) s phase
    (fun p => 2*Real.pi*(m p)^2*p.1/p.2) (fun p => k p*p.2/(m p*p.1)-1) phi
    hB hsep hL hN hd
  · intro p hps; exact (Finset.mem_filter.mp (hs hps)).1
  · intro p hps
    have h := (Finset.mem_filter.mp (hs hps)).2
    exact ⟨h.1,h.2.1⟩
  · exact hp
  · exact hT
  · exact floor_pos M j l hM
  · unfold ratioCap; positivity
  · exact hphi
  · intro p hps; exact (hgeo p hps).1
  · intro p hps; exact (hgeo p hps).2.2
  · intro p hps; exact (hgeo p hps).2.1

/-- The same suppliers on every original four-index AFE term, using its
actual gcd reduction and its unique pair of dyadic labels. -/
theorem original_index_scales (L N : ℕ) (i : PRZZAFEIndices.Index)
    (hi : i ∈ PRZZAFEIndices.indices L N) (F1 F2 FM : ℝ → ℂ)
    (T M Q eps : ℝ) (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q))
    (hf1 : F1 i.2.1 ≠ 0) (hf2 : F2 i.2.2 ≠ 0) (hfm : FM i.1.1 ≠ 0)
    (hheight : 8 ≤ T^(1-eps)) :
    let d := Nat.gcd i.2.1 i.2.2
    let u := i.2.1/d
    let v := i.2.2/d
    |(i.1.2:ℝ)*v-(i.1.1:ℝ)*u| ≤ PRZZSourceCutoffs.deltaCutoff T M Q eps/d →
    productFloor M (Nat.log 2 u) (Nat.log 2 v) ≤ 2*Real.pi*(i.1.1:ℝ)^2*u/v ∧
      |(i.1.2:ℝ)*v/((i.1.1:ℝ)*u)-1| ≤ ratioCap T eps ∧
      |(i.1.2:ℝ)*v/((i.1.1:ℝ)*u)-1| ≤ 1/2 := by
  dsimp only
  intro hdelta
  have hn := Finset.mem_product.mp (Finset.mem_product.mp hi).2
  have hd : 1 ≤ Nat.gcd i.2.1 i.2.2 :=
    Nat.gcd_pos_of_pos_left _ (Finset.mem_Icc.mp hn.1).1
  have hp := PRZZAFEIndices.reduced_rows N i.2.1 i.2.2 hn.1 hn.2 F1 F2 hf1 hf2
  exact row_scales N (Nat.gcd i.2.1 i.2.2)
    (Nat.log 2 (i.2.1/Nat.gcd i.2.1 i.2.2)) (Nat.log 2 (i.2.2/Nat.gcd i.2.1 i.2.2))
    F1 F2 FM T M Q eps (fun _ => (i.1.1:ℝ)) (fun _ => (i.1.2:ℝ))
    (i.2.1/Nat.gcd i.2.1 i.2.2,i.2.2/Nat.gcd i.2.1 i.2.2)
    hd hT hM hQ hsM hs1 hp hfm hdelta hheight

#print axioms original_index_scales
#print axioms floor_pos
#print axioms product_floor
#print axioms scaled_support
#print axioms row_scales
#print axioms source_time_bound
end XiPrime8845.PRZZFreezeScales
