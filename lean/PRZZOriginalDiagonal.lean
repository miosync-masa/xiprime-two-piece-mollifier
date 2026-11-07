import PRZZDiagonalAssembly

/-! Reindex the existing complete-family diagonal into the actual gcd
arithmetic rows. No diagonal decomposition equality is supplied. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Finset Set Filter Topology
namespace XiPrime8845.PRZZOriginalDiagonal
open PRZZDiagonalAssembly PRZZAFEIndices PRZZL1Finite
set_option maxHeartbeats 7000000

def finiteAssembled (L N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta : ℂ) (t : ℝ) : ℂ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
    if admissible N d u v then pair L a F1 F2 alpha beta d u v t else 0

theorem label_diagonal (L N : ℕ) (i : PRZZAFEIndices.Index) (hi : i ∈ indices L N) :
    (label i).2.1 = 0 ↔ i.1.1*i.2.1 = i.1.2*i.2.2 := by
  have hn := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hi).2).1).1
  have hd : (Nat.gcd i.2.1 i.2.2:ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left i.2.2 hn).ne'
  have he := gap_eq i
  constructor
  · intro h
    rw [h,mul_zero] at he
    have hh := sub_eq_zero.mp he
    exact_mod_cast hh
  · intro h
    have hh : (i.1.1:ℤ)*i.2.1 = (i.1.2:ℤ)*i.2.2 := by exact_mod_cast h
    rw [hh,sub_self] at he
    have hprod := mul_eq_zero.mp he.symm
    exact hprod.resolve_left hd

/-- The actual labelled spatial diagonal, with the original cutoff
values, is exactly the sharp original four-index diagonal. -/
theorem labelled_eq_original (L N : ℕ) (P F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ)
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0) :
    PRZZWRowLimit.diagonal L N P (PRZZWRowReindex.leftCoefficient a F1)
      (PRZZWRowReindex.rightCoefficient a F2) alpha beta t =
    ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        if m*n = k*r then F1 n*F2 r*term a a alpha beta
          (PRZZActualDirectSum.mainWeight alpha beta) t m k n r else 0 := by
  classical
  let f : PRZZAFEIndices.Index → ℂ := fun i => if (label i).2.1 = 0 then
    term (PRZZWRowReindex.leftCoefficient a F1) (PRZZWRowReindex.rightCoefficient a F2)
      alpha beta (PRZZActualDirectSum.mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2 else 0
  have he (j : ℕ) (z : Label) :
      (if z.2.1 = 0 then PRZZWRowLimit.row L N P j z
        (PRZZWRowReindex.leftCoefficient a F1) (PRZZWRowReindex.rightCoefficient a F2) alpha beta t else 0) =
      ∑ i ∈ fibre L N z, PRZZAFEProgression.piece P ((2:ℝ)^j) i.1.1*f i := by
    let g : PRZZAFEIndices.Index → ℂ := fun i => PRZZAFEProgression.piece P ((2:ℝ)^j) i.1.1 *
      term (PRZZWRowReindex.leftCoefficient a F1) (PRZZWRowReindex.rightCoefficient a F2)
        alpha beta (PRZZActualDirectSum.mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2
    have hb : PRZZWRowLimit.row L N P j z
        (PRZZWRowReindex.leftCoefficient a F1) (PRZZWRowReindex.rightCoefficient a F2) alpha beta t =
        ∑ i ∈ fibre L N z, g i := (PRZZExplicitDomain.fibre_explicit L N z g).symm
    rw [hb]
    by_cases hz : z.2.1 = 0
    · simp only [if_pos hz]
      apply Finset.sum_congr rfl
      intro i hi
      have hl := (Finset.mem_filter.mp hi).2
      simp only [f,g,hl,if_pos hz]
    · simp only [if_neg hz]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hl := (Finset.mem_filter.mp hi).2
      simp only [f,hl,if_neg hz,mul_zero]
  unfold PRZZWRowLimit.diagonal
  simp_rw [he]
  have hp := PRZZGroupedTime.partition_grouped L N (L+2) P 1 (by norm_num) le_rfl
    (by simpa using PRZZWRowLimit.cover L) hlo hhi f
  simp only [mul_one] at hp
  rw [← hp,← PRZZAFEIndices.grouped]
  have hf : (∑ i ∈ indices L N, f i) =
      ∑ i ∈ indices L N, if i.1.1*i.2.1 = i.1.2*i.2.2 then
        F1 i.2.1*F2 i.2.2*term a a alpha beta
          (PRZZActualDirectSum.mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f,label_diagonal L N i hi,PRZZWRowReindex.term_cutoffs]
  rw [hf]
  simp only [indices,Finset.sum_product]
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 L) (t := Finset.Icc 1 N)]

/-- The gcd reduction preserves both original AFE cutoffs and all
coefficient/cutoff evaluations, with no multiplicity factor. -/
theorem original_eq_finiteAssembled (L N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta : ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        if m*n = k*r then F1 n*F2 r*term a a alpha beta
          (PRZZActualDirectSum.mainWeight alpha beta) t m k n r else 0) =
      finiteAssembled L N a F1 F2 alpha beta t := by
  classical
  have he : (∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        if m*n = k*r then F1 n*F2 r*term a a alpha beta
          (PRZZActualDirectSum.mainWeight alpha beta) t m k n r else 0) =
      ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
        pair L a F1 F2 alpha beta (Nat.gcd n r) (n/Nat.gcd n r) (r/Nat.gcd n r) t := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro r hr
    have hd : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r (Finset.mem_Icc.mp hn).1
    have hdu := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
    have hdv := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
    have hduR : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by exact_mod_cast hdu
    have hdvR : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by exact_mod_cast hdv
    unfold pair
    simp only [hdu,hdv,hduR,hdvR]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro k hk
    have hm' : Nat.gcd n r*(m*(n/Nat.gcd n r)) = m*n := by
      calc
        _ = m*(Nat.gcd n r*(n/Nat.gcd n r)) := by ring
        _ = _ := by rw [hdu]
    have hk' : Nat.gcd n r*(k*(r/Nat.gcd n r)) = k*r := by
      calc
        _ = k*(Nat.gcd n r*(r/Nat.gcd n r)) := by ring
        _ = _ := by rw [hdv]
    have hiff : m*n = k*r ↔ m*(n/Nat.gcd n r) = k*(r/Nat.gcd n r) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hd.ne'
        exact hm'.trans (h.trans hk'.symm)
      · intro h
        calc
          _ = Nat.gcd n r*(m*(n/Nat.gcd n r)) := hm'.symm
          _ = Nat.gcd n r*(k*(r/Nat.gcd n r)) := by rw [h]
          _ = _ := hk'
    simp only [hiff]
  rw [he]
  apply (PRZZWRowReindex.gcd_sum N (fun d u v => pair L a F1 F2 alpha beta d u v t)).trans
  unfold finiteAssembled
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases ha : admissible N d u v
  · have hb : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := ha
    simp only [if_pos ha,if_pos hb]
  · have hb : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := ha
    simp only [if_neg ha,if_neg hb]

theorem labelled_eq_finiteAssembled (L N : ℕ) (P F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ)
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0) :
    PRZZWRowLimit.diagonal L N P (PRZZWRowReindex.leftCoefficient a F1)
      (PRZZWRowReindex.rightCoefficient a F2) alpha beta t =
      finiteAssembled L N a F1 F2 alpha beta t := by
  rw [labelled_eq_original L N P F1 F2 a alpha beta t hlo hhi,
    original_eq_finiteAssembled]

#print axioms label_diagonal
#print axioms labelled_eq_original
#print axioms original_eq_finiteAssembled
#print axioms labelled_eq_finiteAssembled

theorem grid_integral (N : ℕ) (T : ℝ) (phi : ℝ → ℂ) (hphi : Continuous phi)
    (f : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hf : ∀ d ∈ Finset.Icc 1 N, ∀ u ∈ Finset.Icc 1 N, ∀ v ∈ Finset.Icc 1 N,
      ContinuousOn (f d u v) (Set.Icc T (2*T))) :
    (∫ t in Set.Icc T (2*T), phi t*
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, f d u v t) =
      ∑ d ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        ∫ t in Set.Icc T (2*T), phi t*f d u v t := by
  simp only [Finset.mul_sum]
  have hi : ∀ d ∈ Finset.Icc 1 N, ∀ u ∈ Finset.Icc 1 N, ∀ v ∈ Finset.Icc 1 N,
      IntegrableOn (fun t => phi t*f d u v t) (Set.Icc T (2*T)) := by
    intro d hd u hu v hv
    exact (hphi.continuousOn.mul (hf d hd u hu v hv)).integrableOn_compact isCompact_Icc
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro u hu
      exact integral_finsetSum _ (hi d hd u hu)
    · intro u hu
      exact integrable_finsetSum _ (hi d hd u hu)
  · intro d hd
    apply integrable_finsetSum
    intro u hu
    exact integrable_finsetSum _ (hi d hd u hu)

/-- Remove the original sharp AFE cutoff under the time integral, after
the exact gcd reindexing. Every scalar majorant is supplied internally. -/
theorem finite_time_limit (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (hr : -1 ≤ (alpha+beta).re) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L : ℕ => ∫ t in Set.Icc T (2*T),
      phi t*finiteAssembled L N a F1 F2 alpha beta t) atTop
      (𝓝 (∫ t in Set.Icc T (2*T), phi t*assembled N a F1 F2 alpha beta t)) := by
  classical
  have hf (L : ℕ) := grid_integral N T phi hphi
    (fun d u v t => if admissible N d u v then pair L a F1 F2 alpha beta d u v t else 0)
    (by
      intro d hd u hu v hv
      by_cases ha : admissible N d u v
      · simp only [if_pos ha]
        exact pair_continuous L a F1 F2 alpha beta d u v
          (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1 ha.1 hs T hT
      · simp only [if_neg ha]; exact continuousOn_const)
  have hg := grid_integral N T phi hphi
    (fun d u v t => if admissible N d u v then coefficient a F1 F2 alpha beta d u v *
      PRZZDiagonalMellin.diagonal (alpha+beta) (t/(2*Real.pi*(u:ℝ)*v)) else 0)
    (by
      intro d hd u hu v hv
      by_cases ha : admissible N d u v
      · simp only [if_pos ha]
        exact (diagonal_time_continuous (alpha+beta) hs hr T hT u v
          (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1).const_mul _
      · simp only [if_neg ha]; exact continuousOn_const)
  unfold finiteAssembled assembled
  simp_rw [hf,hg]
  apply tendsto_finsetSum
  intro d hd
  apply tendsto_finsetSum
  intro u hu
  apply tendsto_finsetSum
  intro v hv
  by_cases ha : admissible N d u v
  · simp only [if_pos ha]
    exact pair_time_cutoff_removed a F1 F2 alpha beta d u v
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1 ha.1
      hs hr T hT phi hphi
  · simp only [if_neg ha,mul_zero,integral_zero]
    exact tendsto_const_nhds

theorem labelled_time_limit (N : ℕ) (P F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (hs : alpha+beta ≠ 0) (hr : -1 ≤ (alpha+beta).re)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hphi : Continuous phi)
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0) :
    Tendsto (fun L : ℕ => ∫ t in Set.Icc T (2*T), phi t*
      PRZZWRowLimit.diagonal L N P (PRZZWRowReindex.leftCoefficient a F1)
        (PRZZWRowReindex.rightCoefficient a F2) alpha beta t) atTop
      (𝓝 (∫ t in Set.Icc T (2*T), phi t*assembled N a F1 F2 alpha beta t)) := by
  simp_rw [labelled_eq_finiteAssembled _ _ _ _ _ _ _ _ _ hlo hhi]
  exact finite_time_limit N a F1 F2 alpha beta hs hr T hT phi hphi

/-- An original complete-family diagonal has this time-integrated main
term and a controlled defect. The actual exterior arithmetic mass remains
visible; no optimized bound for that mass is assumed or asserted. -/
theorem labelled_time_main_error : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (P F1 F2 : ℝ → ℂ)
    (a : ℕ → ℂ) (alpha beta : ℂ) (T : ℝ),
    alpha+beta ≠ 0 → ‖alpha+beta‖ ≤ 1/8 → 0 < T →
    (∀ y ≤ (1/2:ℝ), P y = 1) → (∀ y, 1 ≤ y → P y = 0) →
    ∀ phi : ℝ → ℂ, Continuous phi → ∃ E : ℂ,
      Tendsto (fun L : ℕ => (∫ t in Set.Icc T (2*T), phi t*
        PRZZWRowLimit.diagonal L N P (PRZZWRowReindex.leftCoefficient a F1)
          (PRZZWRowReindex.rightCoefficient a F2) alpha beta t)-
        (∫ t in Set.Icc T (2*T), phi t)*main N a F1 F2 alpha beta) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*(1+16/‖alpha+beta‖^2)*errorMass N a F1 F2 alpha beta T*
        (∫ t in Set.Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := assembled_time_error
  refine ⟨C,hC,?_⟩
  intro N P F1 F2 a alpha beta T hs hn hT hlo hhi phi hphi
  have hr : -1 ≤ (alpha+beta).re := by
    have hh := (abs_le.mp ((abs_re_le_norm (alpha+beta)).trans hn)).1
    linarith
  exact ⟨_,(labelled_time_limit N P F1 F2 a alpha beta hs hr T hT phi hphi hlo hhi).sub
    tendsto_const_nhds,h N a F1 F2 alpha beta T hs hn hT phi hphi⟩

#print axioms grid_integral
#print axioms finite_time_limit
#print axioms labelled_time_limit
#print axioms labelled_time_main_error
end XiPrime8845.PRZZOriginalDiagonal
