import PRZZActualCaseSum
import PRZZOptimalPowers

/-! Normalize the literal three-case row budget using its dyadic modulus.
The local frequency condition is explicit; supplying it for all nonempty
source boxes and localizing the outer integral remain separate steps. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZActualCasePowers
open PRZZActualCaseSum PRZZOptimalPowers
set_option maxHeartbeats 3000000

theorem row_normalized (Cs Ci Cg Cd Cr Cp Cv eps eta T A d lam : ℝ)
    (N K j l : ℕ) (ks : List ℕ)
    (hCs : 0 ≤ Cs) (hCi : 0 ≤ Ci) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hCr : 0 ≤ Cr) (hCp : 0 ≤ Cp) (hCv : 0 ≤ Cv)
    (hN : 1 ≤ (N:ℝ)) (hNT : (N:ℝ) ≤ T) (hd : 0 < d) (hA : 0 ≤ A)
    (hl : 1 ≤ lam) (hj : (2:ℝ)^j ≤ N) (hlN : (2:ℝ)^l ≤ N)
    (hfreq : A ≤ lam*(((2:ℝ)^j/2^((ks.length+1)*(2*K)))*(2:ℝ)^l/T)) :
    let c : ℝ := 2^((ks.length+1)*(2*K))
    let X : ℝ := (2:ℝ)^j/c
    let V : ℝ := (2:ℝ)^l
    let I := Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps
    let J := PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 *
      ((2*c)*(2*c^2)^2)
    T/(d*X*V)*(smallBudget Cs T A eta l+
      largeBudget Ci Cg Cd Cr Cp Cv eps eta T A 0 N K j l ks) ≤
        (2*Cs*T^eta*A^eta+11*I+22*J)*lam*target N T/d := by
  dsimp only
  let c : ℝ := 2^((ks.length+1)*(2*K))
  let X : ℝ := (2:ℝ)^j/c
  let V : ℝ := (2:ℝ)^l
  let W : ℝ := PRZZDyadicModulus.bound N l
  let I := Ci*(c*T)^eta*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps
  let J := PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A 0 *((2*c)*(2*c^2)^2)
  have hc : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hX : 0 < X := by dsimp [X,c]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hXN : X ≤ N := (div_le_self (by positivity) hc).trans hj
  have hVW : V ≤ W := by
    dsimp [W,PRZZDyadicModulus.bound,V]
    push_cast
    exact le_min hlN (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) l])
  have hWV : W ≤ 2*V := by
    dsimp [W,PRZZDyadicModulus.bound,V]
    push_cast
    exact (min_le_right _ _).trans_eq (by ring)
  have hWN : W ≤ N := by dsimp [W,PRZZDyadicModulus.bound]; exact_mod_cast Nat.min_le_left N (2^(l+1))
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  have hs := small_frequency_bound N T X V d A lam hN hT hX hV hlN hd (by linarith) hfreq
  have hi := source_frequency_bound N T X V d A lam hN hNT hX hXN hV hlN hd hA hl hfreq
  have hi' : T/(d*X*V)*PRZZCombinedBudget.typeI X A V ≤ lam*(11*target N T/d) := by
    apply le_trans _ hi
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by unfold PRZZDISeven.envelope; positivity)
  have hj' := clipped_frequency_bound N T X V W d A lam hN hNT hX hXN hV hVW hWV hWN hd hA hl hfreq
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith)
  have hJ : 0 ≤ J := by dsimp [J,PRZZCommonCellBound.budget]; positivity
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*Cs*T^eta*A^eta by positivity))
    (mul_le_mul_of_nonneg_left hi' hI)) (mul_le_mul_of_nonneg_left hj' hJ)
  convert hh using 1 <;>
    (try simp only [smallBudget,largeBudget,abs_zero,add_zero,mul_one,I,J,X,V,c,W,pow_succ]) <;>
    first | rfl | ring

#print axioms row_normalized

/-- A nonzero original cutoff fixes the scale of its actual dyadic row. -/
theorem cutoff_row_scale (N d j n : ℕ) (Q : ℝ) (F : ℝ → ℂ)
    (hd : 0 < d) (hs : Function.support F ⊆ Set.Icc Q (2*Q))
    (hn : n ∈ PRZZDyadic.cell N j) (hf : F ((d:ℝ)*n) ≠ 0) :
    Q ≤ 2*(d:ℝ)*(2:ℝ)^j ∧ (d:ℝ)*(2:ℝ)^j ≤ 2*Q := by
  have hc := hs hf
  have hrow := (PRZZDyadic.mem_cell N j n).mp hn
  have hlo : (2:ℝ)^j ≤ n := by exact_mod_cast hrow.2.1
  have hhi : (n:ℝ) ≤ 2*(2:ℝ)^j := by
    have hh : (n:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast hrow.2.2
    rw [pow_succ] at hh
    linarith
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  constructor <;> nlinarith [hc.1,hc.2]

/-- Source frequency localization supplied by both original cutoff supports.
The factor 4*c is fixed by dyadic widths and the HB branch length, not T. -/
theorem cutoff_frequency (N d j l n m : ℕ) (Q1 Q2 T A lam c : ℝ)
    (F1 F2 : ℝ → ℂ) (hd : 0 < d) (hT : 0 < T) (hc : 0 < c)
    (_hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hlam : 0 ≤ lam)
    (hs1 : Function.support F1 ⊆ Set.Icc Q1 (2*Q1))
    (hs2 : Function.support F2 ⊆ Set.Icc Q2 (2*Q2))
    (hn : n ∈ PRZZDyadic.cell N j) (hm : m ∈ PRZZDyadic.cell N l)
    (hf1 : F1 ((d:ℝ)*n) ≠ 0) (hf2 : F2 ((d:ℝ)*m) ≠ 0)
    (hfreq : A ≤ lam*(Q1*Q2/((d:ℝ)^2*T))) :
    A ≤ (4*c*lam)*(((2:ℝ)^j/c)*(2:ℝ)^l/T) := by
  have h1 := (cutoff_row_scale N d j n Q1 F1 hd hs1 hn hf1).1
  have h2 := (cutoff_row_scale N d l m Q2 F2 hd hs2 hm hf2).1
  have hp := mul_le_mul h1 h2 hQ2 (by positivity)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  apply hfreq.trans
  calc
    _ ≤ lam*((2*(d:ℝ)*(2:ℝ)^j)*(2*(d:ℝ)*(2:ℝ)^l)/((d:ℝ)^2*T)) := by gcongr
    _ = _ := by field_simp; ring

#print axioms cutoff_row_scale
#print axioms cutoff_frequency

/-- A nonzero literal row supplies both cutoff witnesses. Arithmetic
coefficients, twists and coprimality masks are not assumed nonzero. -/
theorem row_nonzero_cutoffs (N d j l n : ℕ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x t : ℝ) (v : ℤ)
    (hr : PRZZSupportedBranches.row N d j l a b F1 F2 FM alpha beta x t v n ≠ 0) :
    n ∈ PRZZDyadic.cell N j ∧ F1 ((d:ℝ)*n) ≠ 0 ∧
      ∃ m ∈ PRZZDyadic.cell N l, F2 ((d:ℝ)*m) ≠ 0 := by
  classical
  have hn : n ∈ PRZZDyadic.cell N j := by
    by_contra hn
    exact hr (by simp [PRZZSupportedBranches.row,hn])
  refine ⟨hn,?_,?_⟩
  · intro hf
    exact hr (by simp [PRZZSupportedBranches.row,hf])
  · by_contra hh
    push Not at hh
    apply hr
    simp only [PRZZSupportedBranches.row,if_pos hn]
    apply Finset.sum_eq_zero
    intro m hm
    simp [hh m hm]

/-- The local frequency premise now follows from nonvanishing of the
actual row and the original two cutoff supports. -/
theorem nonzero_row_frequency (N d j l n : ℕ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x t : ℝ) (v : ℤ)
    (Q1 Q2 T A lam c : ℝ) (hd : 0 < d) (hT : 0 < T) (hc : 0 < c)
    (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hlam : 0 ≤ lam)
    (hs1 : Function.support F1 ⊆ Set.Icc Q1 (2*Q1))
    (hs2 : Function.support F2 ⊆ Set.Icc Q2 (2*Q2))
    (hr : PRZZSupportedBranches.row N d j l a b F1 F2 FM alpha beta x t v n ≠ 0)
    (hfreq : A ≤ lam*(Q1*Q2/((d:ℝ)^2*T))) :
    A ≤ (4*c*lam)*(((2:ℝ)^j/c)*(2:ℝ)^l/T) := by
  obtain ⟨hn,hf1,m,hm,hf2⟩ := row_nonzero_cutoffs N d j l n a b F1 F2 FM alpha beta x t v hr
  exact cutoff_frequency N d j l n m Q1 Q2 T A lam c F1 F2 hd hT hc hQ1 hQ2 hlam
    hs1 hs2 hn hm hf1 hf2 hfreq

#print axioms row_nonzero_cutoffs
#print axioms nonzero_row_frequency
end XiPrime8845.PRZZActualCasePowers
