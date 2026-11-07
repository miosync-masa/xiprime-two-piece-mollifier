import PRZZFourierTime

/-! Explicit retained reduced arithmetic pairs, with original cutoff masks.
The local domain is derived from support, not assumed per row. Identifying
this pair family with every term of the original AFE remains separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory
namespace XiPrime8845.PRZZSourceRows
open PRZZTailTimeSum PRZZGCoefficient
set_option maxHeartbeats 3000000

local instance (s : Finset ℕ) (F : ℝ → ℂ) : Decidable (PRZZPrunedTailRows.Active s F) :=
  Classical.propDecidable _

def rows (N d j l : ℕ) (F1 F2 : ℝ → ℂ) : Finset (ℕ × ℕ) := by
  classical
  exact ((PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l)).filter (fun p =>
    d*p.1 ≤ N ∧ d*p.2 ≤ N ∧ Nat.Coprime p.1 p.2 ∧
    F1 ((d:ℝ)*p.1) ≠ 0 ∧ F2 ((d:ℝ)*p.2) ≠ 0)

def data (d : ℕ) (T M Q1 Q2 eH delta : ℝ) (p : ℕ × ℕ) : Row :=
  ⟨M,Q1,Q2,p.2,p.1,delta,⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊⟩

/-- Exact removal of zero cutoff pairs from the full restricted dyadic sum.
The arbitrary residual factor can retain all remaining arithmetic weights. -/
theorem pair_prune (N d j l : ℕ) (F1 F2 : ℝ → ℂ) (c : ℕ × ℕ → ℂ) :
    (∑ p ∈ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l),
      if d*p.1 ≤ N ∧ d*p.2 ≤ N ∧ Nat.Coprime p.1 p.2 then
        F1 ((d:ℝ)*p.1)*F2 ((d:ℝ)*p.2)*c p else 0) =
    ∑ p ∈ rows N d j l F1 F2, F1 ((d:ℝ)*p.1)*F2 ((d:ℝ)*p.2)*c p := by
  classical
  rw [rows,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h1 : d*p.1 ≤ N
  · by_cases h2 : d*p.2 ≤ N
    · by_cases hc : Nat.Coprime p.1 p.2
      · by_cases hf : F1 ((d:ℝ)*p.1) = 0
        · simp [h1,h2,hc,hf]
        · by_cases hg : F2 ((d:ℝ)*p.2) = 0 <;> simp [h1,h2,hc,hf,hg]
      · simp [h1,h2,hc]
    · simp [h1,h2]
  · simp [h1]

theorem domain (N d j l : ℕ) (F1 F2 FM : ℝ → ℂ) (s : Finset ℕ)
    (T M Q1 Q2 b eD eH delta : ℝ) (p : ℕ × ℕ)
    (hd : 1 ≤ d) (hNT : (N:ℝ) ≤ T) (hM : M ≤ T^b)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hs1 : Function.support F1 ⊆ Icc (Q1/2) (3*Q1))
    (hs2 : Function.support F2 ⊆ Icc (Q2/2) (3*Q2))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs : ∀ m ∈ s, 1 ≤ m) (ha : PRZZPrunedTailRows.Active s FM)
    (hp : p ∈ rows N d j l F1 F2)
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d) :
    Domain d T b eD eH (data d T M Q1 Q2 eH delta p) := by
  classical
  dsimp only [Domain,data]
  have hp' := Finset.mem_filter.mp hp
  have hcell := Finset.mem_product.mp hp'.1
  have hu := (Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N j p.1).mp hcell.1).1).1
  have hv := (Finset.mem_Icc.mp ((PRZZDyadic.mem_cell N l p.2).mp hcell.2).1).1
  have hdu : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hvN : p.2 ≤ N := (Nat.le_mul_of_pos_left p.2 hd).trans hp'.2.2.1
  have hleft := (hs1 hp'.2.2.2.2.1).1
  have hright := (hs2 hp'.2.2.2.2.2).2
  refine ⟨PRZZPrunedTailRows.active_scale s FM M hs hsM ha,hM,hQ1,hQ2,
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hv),
    (by exact_mod_cast hvN : (p.2:ℝ) ≤ N).trans hNT,?_,by exact_mod_cast hu,hleft,hdelta,?_⟩
  · change (p.2:ℝ) ≤ 3*Q2/d
    exact (le_div_iff₀ hdu).mpr (by nlinarith)
  · change PRZZSourceCutoffs.poissonCutoff d T M Q2 eH ≤
      (⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊:ℝ)+1
    exact (Nat.le_ceil _).trans (by linarith)

/-- Simultaneous substitution for the explicit cutoff-restricted pair set.
The empty lattice mask is retained and the reciprocal coefficient mass is
paid by its own dyadic denominators, with no pair-count loss. -/
theorem integrated (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (js : List ℕ) (N d j l : ℕ) (s : Finset ℕ)
      (F1 F2 FM : ℝ → ℂ) (T M Q1 Q2 delta : ℝ) (alpha beta : ℂ)
      (Phi : ℝ → ℂ) (freq : Finset ℕ) (residue : (ℕ × ℕ) → ℝ),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → 36 ≤ T → 1 ≤ Real.log T →
      ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ → Continuous Phi →
      M ≤ T^b → 0 < Q1 → 0 < Q2 →
      Function.support F1 ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) →
      Function.support FM ⊆ Icc (M/2) (3*M) → (∀ m ∈ s, 1 ≤ m) →
      |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d →
      let H := ⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊
      ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ p ∈ rows N d j l F1 F2,
        (((coefficient js p.1:ℂ)*star (coefficient js p.2:ℂ))/((p.1:ℂ)*(p.2:ℂ)))*
        (if PRZZPrunedTailRows.Active s FM then
          finiteTail F T t alpha beta (data d T M Q1 Q2 eH delta p) freq
            (PRZZFourierTime.residuePhase H p.2 (residue p))
            (PRZZFourierTime.residuePhase H p.2 (-residue p)) else 0))‖ ≤
        K*T^(-A)*(Real.log N)^(2*degree js)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  classical
  obtain ⟨K,hK,h⟩ := PRZZArithmeticFourierTail.pair_integrated F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro js N d j l s F1 F2 FM T M Q1 Q2 delta alpha beta Phi freq residue
    hN hd hNT hT hlog halpha hsep hPhi hM hQ1 hQ2 hs1 hs2 hsM hs hdelta
  apply h js N j l (rows N d j l F1 F2) (data d T M Q1 Q2 eH delta)
    (fun _ => PRZZPrunedTailRows.Active s FM) freq
    (fun p _ => PRZZFourierTime.residuePhase
      ⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊ p.2 (residue p))
    (fun p _ => PRZZFourierTime.residuePhase
      ⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊ p.2 (-residue p))
    d T alpha beta Phi hN
    (by intro p hp; exact (Finset.mem_filter.mp hp).1)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) hT hlog halpha hsep hPhi
  · intro p hp hactive
    exact domain N d j l F1 F2 FM s T M Q1 Q2 b eD eH delta p hd hNT hM
      hQ1 hQ2 hs1 hs2 hsM hs hactive hp hdelta
  · intro p hp t ht v
    exact ⟨(PRZZFourierTime.residue_norm _ _ _ _).le,
      (PRZZFourierTime.residue_norm _ _ _ _).le⟩

/-- Every retained active pair also inherits the actual infinite-series
time exchange; no per-pair Domain or Fourier measurability premise remains. -/
theorem time_swap (N d j l : ℕ) (F1 F2 FM F : ℝ → ℂ) (s : Finset ℕ)
    (T M Q1 Q2 b eD eH delta residue r : ℝ) (p : ℕ × ℕ)
    (hd : 1 ≤ d) (hNT : (N:ℝ) ≤ T) (hM : M ≤ T^b)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hs1 : Function.support F1 ⊆ Icc (Q1/2) (3*Q1))
    (hs2 : Function.support F2 ⊆ Icc (Q2/2) (3*Q2))
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hs : ∀ m ∈ s, 1 ≤ m) (ha : PRZZPrunedTailRows.Active s FM)
    (hp : p ∈ rows N d j l F1 F2)
    (hdelta : |delta| ≤ PRZZSourceCutoffs.deltaCutoff T M Q1 eD/d)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hT : 36 ≤ T) (hlog : 1 ≤ Real.log T) (alpha beta : ℂ)
    (hr : 0 < r) (hsep : r ≤ ‖alpha+beta‖) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    let H := ⌈PRZZSourceCutoffs.poissonCutoff d T M Q2 eH⌉₊
    let f := fun v t => Phi (t/T)*PRZZFourierTime.term F M p.1 p.2 delta
      (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) H v
      (PRZZFourierTime.residuePhase H p.2 residue)
      (PRZZFourierTime.residuePhase H p.2 (-residue)) t
    (∑' v, ∫ t in Icc T (2*T), f v t) = ∫ t in Icc T (2*T), ∑' v, f v t :=
  PRZZFourierTime.source_swap F hF hsF d T b eD eH residue r
    (data d T M Q1 Q2 eH delta p)
    (domain N d j l F1 F2 FM s T M Q1 Q2 b eD eH delta p hd hNT hM hQ1 hQ2
      hs1 hs2 hsM hs ha hp hdelta) hT hlog alpha beta hr hsep Phi hPhi

#print axioms time_swap
#print axioms pair_prune
#print axioms domain
#print axioms integrated
end XiPrime8845.PRZZSourceRows
