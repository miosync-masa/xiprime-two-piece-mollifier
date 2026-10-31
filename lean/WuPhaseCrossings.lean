import WuDeflatedDetection
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Int.Interval

/-! A single continuous phase counts distinct crossings; full analytic
orders dominate that count. The common eta divisor is then restored exactly.
This is a finite critical-line statement, not yet the rectangle counting gate. -/
noncomputable section
open scoped BigOperators
open Complex Set
namespace XiPrime8845.WuPhaseCrossings
open WuAuxiliary WuCriticalDeflation WuAuxiliaryMultiplicity Zeta23.XiPrime
set_option maxHeartbeats 2000000

theorem phase_count (a : ℝ → ℝ) (u v : ℝ) (ha : ContinuousOn a (uIcc u v))
    (S : Finset ℝ) (hS : ∀ t ∈ uIcc u v, Real.sin (a t) = 0 → t ∈ S) :
    |a v-a u| ≤ Real.pi*((S.card:ℝ)+1) := by
  classical
  let lo := min (a u) (a v)
  let hi := max (a u) (a v)
  let K := Finset.Icc (⌈lo/Real.pi⌉ : ℤ) ⌊hi/Real.pi⌋
  have hex (k : K) : ∃ t ∈ uIcc u v, a t = (k.val:ℝ)*Real.pi := by
    apply intermediate_value_uIcc ha
    have hk := Finset.mem_Icc.mp k.property
    have h1 : lo/Real.pi ≤ (k.val:ℝ) := (Int.le_ceil _).trans (by exact_mod_cast hk.1)
    have h2 : (k.val:ℝ) ≤ hi/Real.pi := (show (k.val:ℝ) ≤ (⌊hi/Real.pi⌋:ℝ) by
      exact_mod_cast hk.2).trans (Int.floor_le _)
    exact ⟨(div_le_iff₀ Real.pi_pos).mp h1,(le_div_iff₀ Real.pi_pos).mp h2⟩
  choose t ht he using hex
  have htS (k : K) : t k ∈ S := hS _ (ht k) (by rw [he k]; exact Real.sin_int_mul_pi _)
  let f : K → S := fun k => ⟨t k,htS k⟩
  have hinj : Function.Injective f := by
    intro k l hkl
    have heq : t k = t l := congrArg Subtype.val hkl
    have hh : (k.val:ℝ)*Real.pi = (l.val:ℝ)*Real.pi := (he k).symm.trans (heq ▸ he l)
    apply Subtype.ext
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero hh
  have hcard : K.card ≤ S.card := Finset.card_le_card_of_injective hinj
  have hkcard : (⌊hi/Real.pi⌋:ℝ)+1-(⌈lo/Real.pi⌉:ℝ) ≤ (K.card:ℝ) := by
    dsimp [K]
    rw [Int.card_Icc]
    exact_mod_cast (Int.self_le_toNat (⌊hi/Real.pi⌋+1-⌈lo/Real.pi⌉))
  have hgap : (hi-lo)/Real.pi ≤ (S.card:ℝ)+1 := by
    have hfloor := Int.sub_one_lt_floor (hi/Real.pi)
    have hceil := Int.ceil_lt_add_one (lo/Real.pi)
    have hcard' : (K.card:ℝ) ≤ S.card := by exact_mod_cast hcard
    rw [sub_div]
    linarith
  have heq : hi-lo = |a v-a u| := by dsimp [hi,lo]; exact max_sub_min_eq_abs _ _
  rw [heq] at hgap
  exact ((div_le_iff₀ Real.pi_pos).mp hgap).trans_eq (by ring)

theorem positive_order_at_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) (s : ℂ) (hs : f s = 0) : 1 ≤ analyticOrderNatAt f s := by
  have hne := (hf.analyticAt s).analyticOrderAt_ne_zero.mpr hs
  have htop := entire_order_ne_top f hf hn s
  have hnat : analyticOrderNatAt f s ≠ 0 := by
    intro h
    apply hne
    rw [← Nat.cast_analyticOrderNatAt htop,h,Nat.cast_zero]
  omega

/-- The phase of the globally deflated curve plus the removed eta orders
is bounded by the FULL xi' multiplicity, with only one endpoint allowance. -/
theorem phase_count_restored {L u v : ℝ} (d : Data L u v) (hL : L ≠ 0) (huv : u ≤ v)
    (q : WuLittlewood.EdgeLog d.curve (1/2) I u v)
    (S : Finset ℂ) (hdiv : d.zeros ⊆ S)
    (hS : ∀ t ∈ Icc u v, xiDeriv (critical t) = 0 → critical t ∈ S) :
    |(q.value v).im-(q.value u).im|/Real.pi+(d.totalOrder:ℝ) ≤
      (∑ s ∈ S, (analyticOrderNatAt xiDeriv s:ℝ))+1 := by
  classical
  let Z := S.filter (fun s => d.xiPart s = 0)
  have hq : ContinuousOn (fun t => (q.value t).im) (uIcc u v) :=
    Complex.continuous_im.comp_continuousOn q.continuous
  have hc := phase_count (fun t => (q.value t).im) u v hq (Z.image Complex.im) (by
    intro t ht hz
    have hrem := (d.phase_zero_iff hL q t ht).mp hz
    have hxi : xiDeriv (critical t) = 0 := by rw [d.xi_factor,hrem,mul_zero]
    have hmem : critical t ∈ Z := Finset.mem_filter.mpr
      ⟨hS t (by simpa [uIcc_of_le huv] using ht) hxi,hrem⟩
    exact Finset.mem_image.mpr ⟨critical t,hmem,by simp [critical]⟩)
  have hnon : ∃ s, d.xiPart s ≠ 0 := by
    obtain ⟨s,hs⟩ := exists_xiDeriv_ne_zero
    exact ⟨s,fun h => hs (by rw [d.xi_factor,h,mul_zero])⟩
  have hcard : (Z.image Complex.im).card ≤ ∑ s ∈ S, analyticOrderNatAt d.xiPart s := by
    apply (Finset.card_image_le).trans
    calc
      Z.card = ∑ s ∈ Z, 1 := by simp
      _ ≤ ∑ s ∈ Z, analyticOrderNatAt d.xiPart s := Finset.sum_le_sum (fun s hs =>
        positive_order_at_zero d.xiPart d.xi_entire hnon s (Finset.mem_filter.mp hs).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
  have hc' : |(q.value v).im-(q.value u).im|/Real.pi ≤
      ((Z.image Complex.im).card:ℝ)+1 := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith [hc])
  have he := d.count_restore S hdiv
  have he' : (∑ s ∈ S, (analyticOrderNatAt xiDeriv s:ℝ)) =
      (d.totalOrder:ℝ)+∑ s ∈ S, (analyticOrderNatAt d.xiPart s:ℝ) := by exact_mod_cast he
  have hc'' : ((Z.image Complex.im).card:ℝ) ≤ ∑ s ∈ S, (analyticOrderNatAt d.xiPart s:ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The actual fixed-L eta and xi' supply every object. The finite set is
exactly the CLOSED critical interval's xi' zeros; there is no nonvanishing
assumption on eta and no simplicity assumption. Rectangle/indentation
comparison with the original eta phase remains a separate step. -/
theorem critical_phase_count (L u v : ℝ) (hL : L ≠ 0) (huv : u ≤ v) :
    ∃ d : Data L u v, ∃ q : WuLittlewood.EdgeLog d.curve (1/2) I u v,
      ∃ S : Finset ℂ,
        (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ xiDeriv s = 0) ∧
        |(q.value v).im-(q.value u).im|/Real.pi+(d.totalOrder:ℝ) ≤
          (∑ s ∈ S, (analyticOrderNatAt xiDeriv s:ℝ))+1 := by
  classical
  obtain ⟨d⟩ := exists_data L u v hL
  obtain ⟨q⟩ := d.edgeLog huv
  obtain ⟨s,hs⟩ := exists_xiDeriv_ne_zero
  have hdisc : IsClosed {z | xiDeriv z = 0} ∧ IsDiscrete {z | xiDeriv z = 0} :=
    compl_mem_codiscrete_iff.mp ((show AnalyticOnNhd ℂ xiDeriv univ from
      fun z _ => xiDeriv_differentiable.analyticAt z).preimage_zero_mem_codiscrete hs)
  have hcompact : IsCompact (critical '' Icc u v) := isCompact_Icc.image (by
    unfold critical; fun_prop)
  have hfin : ((critical '' Icc u v) ∩ {z | xiDeriv z = 0}).Finite :=
    IsCompact.finite (hcompact.inter_right hdisc.1) (hdisc.2.mono inter_subset_right)
  let S := hfin.toFinset
  have hS (s : ℂ) : s ∈ S ↔ s ∈ critical '' Icc u v ∧ xiDeriv s = 0 := by simp [S]
  refine ⟨d,q,S,hS,phase_count_restored d hL huv q S ?_ ?_⟩
  · intro z hz
    have he := (d.mem_zeros z).mp hz
    obtain ⟨t,ht,rfl⟩ := he.1
    exact (hS _).mpr ⟨⟨t,ht,rfl⟩,(eta_im_zero_iff L t hL).mp (by rw [he.2]; rfl)⟩
  · intro t ht hz
    exact (hS _).mpr ⟨⟨t,ht,rfl⟩,hz⟩

#print axioms phase_count
#print axioms positive_order_at_zero
#print axioms phase_count_restored
#print axioms critical_phase_count
end XiPrime8845.WuPhaseCrossings
