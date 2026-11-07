import PRZZFreezeScales
import PRZZPoissonActualWeight

/-! The literal A* prefactor, including dilated coefficients, valued
cutoffs, complex shifts and the inverse-residue phase, in a dyadic mass.
The Delta/h multiplicity is retained as the exact finite frequency set. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZPrefactorMass
set_option maxHeartbeats 4000000

def pairs (N d j l : ℕ) : Finset (ℕ × ℕ) :=
  ((PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l)).filter
    (fun p => p.1.Coprime p.2 ∧ d*p.1 ≤ N ∧ d*p.2 ≤ N)

def frequencies (d : ℕ) (D H : ℝ) : Finset (ℤ × ℕ) :=
  ((Finset.Icc (-⌈D/d⌉) ⌈D/d⌉).filter
    (fun delta : ℤ => 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < D/d)) ×ˢ
  ((Finset.Icc 1 ⌊H⌋₊).filter (fun h : ℕ => (h:ℝ) < H))

def localIndices (N d j l : ℕ) (D H : ℝ) : Finset PRZZAStar.Index :=
  pairs N d j l ×ˢ frequencies d D H

theorem local_indices_eq (N d j l : ℕ) (D H : ℝ) :
    localIndices N d j l D H = (PRZZAStar.indices N d D H).filter
      (fun z => z.1.1 ∈ PRZZDyadic.cell N j ∧ z.1.2 ∈ PRZZDyadic.cell N l) := by
  classical
  ext z
  constructor
  · intro hz
    have h := Finset.mem_product.mp hz
    have hp := Finset.mem_filter.mp h.1
    have hc := Finset.mem_product.mp hp.1
    have hu := ((PRZZDyadic.mem_cell N j z.1.1).mp hc.1).1
    have hv := ((PRZZDyadic.mem_cell N l z.1.2).mp hc.2).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,hc⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hu,hv⟩,hp.2⟩,h.2⟩
  · intro hz
    have h := Finset.mem_filter.mp hz
    have hp := Finset.mem_product.mp h.1
    have hc := (Finset.mem_filter.mp hp.1).2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr h.2,hc⟩,hp.2⟩

theorem inverse_pair (N d j l : ℕ) (p : ℕ × ℕ) (T S : ℝ) (alpha beta : ℂ)
    (hd : 1 ≤ d) (hNT : (N:ℝ) ≤ T) (hL : 0 < Real.log T) (hS : 0 ≤ S)
    (hp : p ∈ pairs N d j l)
    (ha : |alpha.re| ≤ S/Real.log T) (hb : |beta.re| ≤ S/Real.log T) :
    ‖((p.1:ℂ)^alpha)⁻¹‖ ≤ Real.exp S ∧ ‖((p.2:ℂ)^beta)⁻¹‖ ≤ Real.exp S := by
  have h := Finset.mem_filter.mp hp
  have hc := Finset.mem_product.mp h.1
  have hu := ((PRZZDyadic.mem_cell N j p.1).mp hc.1).1
  have hv := ((PRZZDyadic.mem_cell N l p.2).mp hc.2).1
  have bound (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (z : ℂ) (hz : |z.re| ≤ S/Real.log T) :
      ‖((n:ℂ)^z)⁻¹‖ ≤ Real.exp S := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnT : (n:ℝ) ≤ T := hnN.trans hNT
    have hlog : |Real.log n| ≤ 1*Real.log T := by
      rw [abs_of_nonneg (Real.log_nonneg hn1),one_mul]
      exact Real.log_le_log (by linarith) hnT
    simpa only [one_mul,Complex.ofReal_natCast] using PRZZDyadicEnvelope.inverse_power T 1 S n z
      hL (by linarith) hS hlog hz
  exact ⟨bound p.1 hu alpha ha,bound p.2 hv beta hb⟩

/-- One frequency row of the actual normalized prefactor. The dyadic
denominators pay for the pair cardinality, with no further pair count. -/
theorem pair_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l : ℕ) (T Q V S : ℝ)
      (alpha beta : ℂ) (w : ℤ × ℕ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ p ∈ pairs N d j l,
        ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta (p,w)/((p.1:ℂ)*(p.2:ℂ))‖) ≤
        C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d := by
  obtain ⟨B,hB,hcut⟩ := PRZZValuedCutoffs.cutoff_pair_uniform F G hF hG hcF hcG
  refine ⟨B+1,by positivity,?_⟩
  intro js N d j l T Q V S alpha beta w hN hd hNT hL hS ha hb
  let f1 := PRZZMellinSeparation.scaledCutoff F Q
  let f2 := PRZZMellinSeparation.scaledCutoff G V
  let g := fun p : ℕ × ℕ =>
    f1 ((d:ℝ)*p.1)*f2 ((d:ℝ)*p.2)*((d:ℂ)*(p.1:ℂ)^alpha*(p.2:ℂ)^beta)⁻¹*
      PRZZKloostermanInputs.e (-((w.2:ℝ)*(w.1:ℝ))*
        PRZZKloostermanInputs.inverseResidue p.2 p.1/p.2)
  have hg (p : ℕ × ℕ) (hp : p ∈ pairs N d j l) : ‖g p‖ ≤ B*Real.exp (2*S)/d := by
    have hs := inverse_pair N d j l p T S alpha beta hd hNT hL hS hp ha hb
    have hn : ‖PRZZKloostermanInputs.e (-((w.2:ℝ)*(w.1:ℝ))*
        PRZZKloostermanInputs.inverseResidue p.2 p.1/p.2)‖ = 1 := by
      simp [PRZZKloostermanInputs.e,Complex.norm_exp]
    have hc := hcut Q V ((d:ℝ)*p.1) ((d:ℝ)*p.2)
    change ‖f1 ((d:ℝ)*p.1)*f2 ((d:ℝ)*p.2)‖ ≤ B at hc
    dsimp only [g]
    rw [norm_mul,hn,mul_one]
    simp only [norm_mul,norm_inv,Complex.norm_natCast,mul_inv_rev]
    have hd0 : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have h1 := hs.1; have h2 := hs.2
    rw [norm_inv] at h1 h2
    rw [norm_mul] at hc
    have hpow : ‖(p.2:ℂ)^beta‖⁻¹*‖(p.1:ℂ)^alpha‖⁻¹ ≤ Real.exp S*Real.exp S :=
      mul_le_mul h2 h1 (by positivity) (Real.exp_pos S).le
    calc
      _ = (‖f1 ((d:ℝ)*p.1)‖*‖f2 ((d:ℝ)*p.2)‖)*
          (‖(p.2:ℂ)^beta‖⁻¹*‖(p.1:ℂ)^alpha‖⁻¹)*(d:ℝ)⁻¹ := by ring
      _ ≤ (B*(Real.exp S*Real.exp S))*(d:ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc hpow (by positivity) hB) (by positivity)
      _ = _ := by
        have he : Real.exp S*Real.exp S = Real.exp (2*S) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he]
        ring
  have hm := PRZZDyadicArithmeticMass.dilated_weighted_pair_mass js N d j l hN hd
    (pairs N d j l) (by intro p hp; exact (Finset.mem_filter.mp hp).1)
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.2)
    g (B*Real.exp (2*S)/d) (by positivity) hg
  have he : (∑ p ∈ pairs N d j l,
      ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) f1 f2 d
        alpha beta (p,w)/((p.1:ℂ)*(p.2:ℂ))‖) =
      ∑ p ∈ pairs N d j l,
        ‖(((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*
          star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*g p)/((p.1:ℂ)*(p.2:ℂ))‖ := by
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    unfold PRZZAStar.prefactor g
    push_cast
    ring
  rw [he]
  apply hm.trans
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ = B*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d := by ring
    _ ≤ _ := by gcongr; linarith

/-- All signed Delta and positive h values in the original strict
cutoffs are included. Their exact multiplicity remains visible. -/
theorem local_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d j l : ℕ) (T Q V S D H : ℝ)
      (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ z ∈ localIndices N d j l D H,
        ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
        (frequencies d D H).card*(C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d) := by
  obtain ⟨C,hC,hh⟩ := pair_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N d j l T Q V S D H alpha beta hN hd hNT hL hS ha hb
  simp only [localIndices,Finset.sum_product]
  rw [Finset.sum_comm]
  exact (Finset.sum_le_sum (fun w hw => hh js N d j l T Q V S alpha beta w
    hN hd hNT hL hS ha hb)).trans_eq (by simp)

/-- Exact reconstruction of all original A* indices, once each, from
the two half-open dyadic labels. Both signed gaps and every h survive. -/
theorem dyadic_partition (N d : ℕ) (D H : ℝ) (f : PRZZAStar.Index → ℝ) :
    (∑ z ∈ PRZZAStar.indices N d D H, f z) =
      ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
        ∑ z ∈ localIndices N d j l D H, f z := by
  classical
  have hm (z : PRZZAStar.Index) (hz : z ∈ PRZZAStar.indices N d D H) :
      z.1.1 ∈ Finset.Icc 1 N ∧ z.1.2 ∈ Finset.Icc 1 N := by
    exact Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hlog (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Nat.log 2 n ∈ Finset.range (Nat.log 2 N+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Icc.mp hn).2))
  have hfirst := Finset.sum_fiberwise_of_maps_to
    (s := PRZZAStar.indices N d D H) (t := Finset.range (Nat.log 2 N+1))
    (g := fun z : PRZZAStar.Index => Nat.log 2 z.1.1)
    (fun z hz => hlog z.1.1 (hm z hz).1) f
  rw [← hfirst]
  apply Finset.sum_congr rfl
  intro j hj
  have hsecond := Finset.sum_fiberwise_of_maps_to
    (s := (PRZZAStar.indices N d D H).filter (fun z => Nat.log 2 z.1.1 = j))
    (t := Finset.range (Nat.log 2 N+1)) (g := fun z : PRZZAStar.Index => Nat.log 2 z.1.2)
    (fun z hz => hlog z.1.2 (hm z (Finset.mem_filter.mp hz).1).2) f
  rw [← hsecond]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [local_indices_eq]
  ext z
  by_cases hz : z ∈ PRZZAStar.indices N d D H
  · have hu := (hm z hz).1
    have hv := (hm z hz).2
    have hu' := Finset.mem_Icc.mp hu
    have hv' := Finset.mem_Icc.mp hv
    simp [Finset.mem_filter,PRZZDyadic.cell,hz,hu'.1,hu'.2,hv'.1,hv'.2,and_assoc]
  · simp [Finset.mem_filter,hz]

/-- The full literal frequency, dyadic and arithmetic prefactor mass.
No decomposition identity or cell estimate is an input. -/
theorem full_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N d : ℕ) (T Q V S D H : ℝ)
      (alpha beta : ℂ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ z ∈ PRZZAStar.indices N d D H,
        ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
        ((Nat.log 2 N+1:ℕ):ℝ)^2*(frequencies d D H).card*
          (C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d) := by
  obtain ⟨C,hC,hh⟩ := local_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N d T Q V S D H alpha beta hN hd hNT hL hS ha hb
  rw [dyadic_partition]
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
        (frequencies d D H).card*(C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun l hl => hh js N d j l T Q V S D H alpha beta hN hd hNT hL hS ha hb)
    _ = _ := by simp; ring

/-- Sum all admissible gcd divisors without replacing the reciprocal
d cost by an extra factor N. The exact frequency mass remains weighted. -/
theorem divisor_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N : ℕ) (T Q V S : ℝ)
      (D H : ℕ → ℝ) (alpha beta : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ d ∈ Finset.Icc 1 N, ∑ z ∈ PRZZAStar.indices N d (D d) (H d),
        ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
        ((Nat.log 2 N+1:ℕ):ℝ)^2*C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
          (∑ d ∈ Finset.Icc 1 N, ((frequencies d (D d) (H d)).card:ℝ)/d) := by
  obtain ⟨C,hC,hh⟩ := full_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N T Q V S D H alpha beta hN hNT hL hS ha hb
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((Nat.log 2 N+1:ℕ):ℝ)^2*(frequencies d (D d) (H d)).card*
        (C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)/d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hh js N d T Q V S (D d) (H d) alpha beta hN (Finset.mem_Icc.mp hd).1 hNT hL hS ha hb
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d hd; ring

def sourceCost (T M eps : ℝ) (j l : ℕ) : ℝ :=
  (PRZZFreezeScales.ratioCap T eps+2*T*(PRZZFreezeScales.ratioCap T eps)^2)*(2*T)^2/
    (PRZZFreezeScales.productFloor M j l)^2

/-- Simultaneous substitution of the concrete Delta/h cutoffs and local
analytic cost. All spatial scales, gcd divisors, dyadic labels and signed
frequencies are summed, with their weighted budget still explicit. -/
theorem source_weighted_mass (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N : ℕ) (T Q V S eps eH : ℝ)
      (alpha beta : ℂ) (ms : Finset ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (∑ M ∈ ms, ∑ d ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
        sourceCost T M eps j l*
          ∑ z ∈ localIndices N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps)
            (PRZZSourceCutoffs.poissonCutoff d T M V eH),
          ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
            d alpha beta z/((z.1.1:ℂ)*(z.1.2:ℂ))‖) ≤
      C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
        (∑ M ∈ ms, ∑ d ∈ Finset.Icc 1 N,
          ∑ j ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
          sourceCost T M eps j l*
            ((frequencies d (PRZZSourceCutoffs.deltaCutoff T M Q eps)
              (PRZZSourceCutoffs.poissonCutoff d T M V eH)).card:ℝ)/d) := by
  obtain ⟨C,hC,hh⟩ := local_mass F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N T Q V S eps eH alpha beta ms hN hNT hT hL hS ha hb
  have cost_nonneg (M : ℝ) (j l : ℕ) : 0 ≤ sourceCost T M eps j l := by
    unfold sourceCost PRZZFreezeScales.ratioCap
    positivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hi := hh js N d j l T Q V S (PRZZSourceCutoffs.deltaCutoff T M Q eps)
    (PRZZSourceCutoffs.poissonCutoff d T M V eH) alpha beta
    hN (Finset.mem_Icc.mp hd).1 hNT hL hS ha hb
  exact (mul_le_mul_of_nonneg_left hi (cost_nonneg M j l)).trans_eq (by ring)

#print axioms source_weighted_mass
#print axioms dyadic_partition
#print axioms full_mass
#print axioms divisor_mass
#print axioms local_indices_eq
#print axioms inverse_pair
#print axioms pair_mass
#print axioms local_mass
end XiPrime8845.PRZZPrefactorMass
