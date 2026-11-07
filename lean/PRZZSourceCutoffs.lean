import PRZZSourceFrequency

/-! Concrete cutoffs from Pratt--Robles arXiv:1706.04593v3, pp. 8,10,15.
We use H_d = N_2 T^epsilon/(d M) as defined on p.10; the p.14
recall prints N^2 instead. The p.15 product agrees with p.10.
The two epsilon losses are kept distinct. These algebraic suppliers do
not prove the integration-by-parts bound for the actual AFE kernel. -/
noncomputable section
namespace XiPrime8845.PRZZSourceCutoffs

def deltaCutoff (T M Q1 eD : ℝ) : ℝ := M*Q1/T^(1-eD)
def poissonCutoff (d T M Q2 eH : ℝ) : ℝ := Q2*T^eH/(d*M)

theorem cutoff_product (d T M Q1 Q2 eD eH : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) :
    deltaCutoff T M Q1 eD * poissonCutoff d T M Q2 eH / d =
      T^(eD+eH)*(Q1*Q2/(d^2*T)) := by
  have ht : T^(1-eD)*T^eD = T := by
    rw [← Real.rpow_add hT]
    norm_num
  rw [deltaCutoff,poissonCutoff,Real.rpow_add hT]
  field_simp
  linear_combination -(Q1*Q2)*ht

/-- The original strict index set is empty, or its rounded frequency
envelope satisfies the concrete source bound with a height-independent 2. -/
theorem empty_or_frequency (N d : ℕ) (T M Q1 Q2 eD eH : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) :
    PRZZAStar.indices N d (deltaCutoff T M Q1 eD)
      (poissonCutoff d T M Q2 eH) = ∅ ∨
    (1 ≤ PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q1 eD)
        (poissonCutoff d T M Q2 eH) ∧
      (PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q1 eD)
        (poissonCutoff d T M Q2 eH):ℝ) ≤
        (2*T^(eD+eH))*(Q1*Q2/((d:ℝ)^2*T))) := by
  apply PRZZSourceFrequency.empty_or_source_frequency
  exact (cutoff_product d T M Q1 Q2 eD eH (by exact_mod_cast hd) hT hM).le

/-- The scalar gain used after integration by parts. The analytic IBP
estimate itself is not an input disguised as a proved tail estimate. -/
theorem tail_ratio (d T M Q2 eH e1 h : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q2)
    (hh : poissonCutoff d T M Q2 eH ≤ h) :
    Q2*T^e1/(d*M*h) ≤ T^(e1-eH) := by
  have hcut : 0 < poissonCutoff d T M Q2 eH := by
    unfold poissonCutoff; positivity
  have hh0 := hcut.trans_le hh
  have he : Q2*T^e1/(d*M*poissonCutoff d T M Q2 eH) = T^(e1-eH) := by
    rw [Real.rpow_sub hT]
    unfold poissonCutoff
    field_simp
  calc
    _ ≤ Q2*T^e1/(d*M*poissonCutoff d T M Q2 eH) := by gcongr
    _ = _ := he

/-- Explicit IBP order: any fixed polynomial prefactor is beaten once
e1 < eH. This is the exponent calculation, not the analytic tail sum. -/
theorem exists_tail_order (e1 eH B A : ℝ) (he : e1 < eH) :
    ∃ ell : ℕ, ∀ T : ℝ, 1 ≤ T →
      T^B*(T^(e1-eH))^ell ≤ T^(-A) := by
  obtain ⟨ell,hell⟩ := exists_nat_gt ((B+A)/(eH-e1))
  have hexp : B+(e1-eH)*(ell:ℝ) ≤ -A := by
    have hh := (div_lt_iff₀ (sub_pos.mpr he)).mp hell
    nlinarith
  refine ⟨ell,?_⟩
  intro T hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  rw [← Real.rpow_natCast (T^(e1-eH)) ell, ← Real.rpow_mul hT0.le,
    ← Real.rpow_add hT0]
  exact Real.rpow_le_rpow_of_exponent_le hT hexp

#print axioms exists_tail_order
#print axioms cutoff_product
#print axioms empty_or_frequency
#print axioms tail_ratio
end XiPrime8845.PRZZSourceCutoffs
