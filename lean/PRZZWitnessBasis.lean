import PRZZCoefficientPolarization

/-! The actual public witness in a height-dependent finite coefficient basis.
The logarithmic profile, Feng normalization and original support are part
of each basis vector. This is not an analytic uniform-square estimate. -/
noncomputable section
open scoped BigOperators
open Complex Filter Topology
namespace XiPrime8845.PRZZWitnessBasis
open PRZZCoefficientPolarization
set_option maxHeartbeats 3000000

def conreyMonomial (k : ℕ) : PRZZ.Profiles := ⟨Polynomial.X^k,0⟩
def fengMonomial (k : ℕ) : PRZZ.Profiles := ⟨0,Polynomial.X^k⟩

def profiles : Fin 7 → PRZZ.Profiles :=
  ![conreyMonomial 1,conreyMonomial 2,conreyMonomial 3,conreyMonomial 4,
    fengMonomial 1,fengMonomial 2,fengMonomial 3]

/-- Scaling by three places the fixed witness coordinates in the unit box.
The basis itself depends on height, including the cutoff and log powers. -/
def basis (theta T : ℝ) : Fin 7 → ℕ → ℂ :=
  fun i n => 3*PRZZ.coefficient (profiles i) theta T n

def coordinates : Fin 7 → ℂ :=
  ![((-0.30528514:ℝ)/3:ℂ),((2.50038954:ℝ)/3:ℂ),
    ((-1.12177152:ℝ)/3:ℂ),((-0.07333288:ℝ)/3:ℂ),
    ((1.89779072:ℝ)/3:ℂ),((0.56594804:ℝ)/3:ℂ),((0.07023055:ℝ)/3:ℂ)]

theorem coordinates_unit (i : Fin 7) : ‖coordinates i‖ ≤ 1 := by
  fin_cases i <;> norm_num [coordinates,Complex.norm_real,Real.norm_eq_abs]

/-- Exact equality for every height, without positivity or limiting
premises. In particular the basis may not be frozen at one height. -/
theorem witness_expansion (theta T : ℝ) :
    PRZZ.coefficient PRZZ.witness theta T = family (basis theta T) coordinates := by
  funext n
  simp only [family,Fin.sum_univ_succ,basis,profiles,coordinates,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  unfold PRZZ.coefficient
  split_ifs <;>
    simp [PRZZ.witness,conreyMonomial,fengMonomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_pow,Complex.ofReal_add,
      Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow] <;> ring

theorem profile_unit (i : Fin 7) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |(profiles i).conrey.eval u| ≤ 1 ∧ |(profiles i).feng.eval u| ≤ 1 := by
  have hp (k : ℕ) : |u^k| ≤ 1 := by
    rw [abs_pow,abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 hu1
  fin_cases i
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 1
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 2
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 3
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 4
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 1
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 2
  · simpa [profiles,conreyMonomial,fengMonomial] using hp 3

/-- A height-uniform coefficient bound for every basis profile, including
the normalized Feng arithmetic factor. No moment estimate is used. -/
theorem profile_coefficient_bound (i : Fin 7) (theta T : ℝ)
    (htheta : 0 < theta) (hT : 2 ≤ T) (n : ℕ) :
    ‖PRZZ.coefficient (profiles i) theta T n‖ ≤ 2 := by
  by_cases hs : 1 ≤ n ∧ (n:ℝ) ≤ PRZZ.length theta T
  · have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hs.1
    have hy : 1 < PRZZ.length theta T := Real.one_lt_rpow (by linarith) htheta
    have hlog : 0 < Real.log (PRZZ.length theta T) := Real.log_pos hy
    have hu0 : 0 ≤ Real.log (PRZZ.length theta T/n)/Real.log (PRZZ.length theta T) :=
      div_nonneg (Real.log_nonneg ((one_le_div hn).mpr hs.2)) hlog.le
    have hu1 : Real.log (PRZZ.length theta T/n)/Real.log (PRZZ.length theta T) ≤ 1 := by
      apply (div_le_one hlog).mpr
      apply Real.log_le_log (div_pos (by linarith) hn)
      exact div_le_self (by linarith) hn1
    obtain ⟨hP,hF⟩ := profile_unit i _ hu0 hu1
    have hln0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
    have hln : Real.log (n:ℝ) ≤ Real.log (PRZZ.length theta T) := Real.log_le_log hn hs.2
    have har : |PRZZ.fengArithmetic n|/(Real.log (PRZZ.length theta T))^2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos hlog)).mpr
      exact (PRZZ.abs_fengArithmetic_le_log_sq n hs.1).trans (by nlinarith)
    simp only [PRZZ.coefficient,if_pos hs,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |PRZZ.muReal n| * |(profiles i).conrey.eval _|+
          (|PRZZ.fengArithmetic n| / (Real.log (PRZZ.length theta T))^2)*
            |(profiles i).feng.eval _| := by
        have hh := abs_add_le
          (PRZZ.muReal n*(profiles i).conrey.eval
            (Real.log (PRZZ.length theta T/n)/Real.log (PRZZ.length theta T)))
          (PRZZ.fengArithmetic n*(profiles i).feng.eval
            (Real.log (PRZZ.length theta T/n)/Real.log (PRZZ.length theta T))/
              (Real.log (PRZZ.length theta T))^2)
        simpa only [abs_mul,abs_div,abs_of_nonneg (sq_nonneg (Real.log (PRZZ.length theta T))),
          div_mul_eq_mul_div] using hh
      _ ≤ 1*1+1*1 := add_le_add
        (mul_le_mul (PRZZ.abs_muReal_le_one n) hP (abs_nonneg _) (by norm_num))
        (mul_le_mul har hF (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  · simp [PRZZ.coefficient,hs]

theorem basis_coefficient_bound (i : Fin 7) (theta T : ℝ)
    (htheta : 0 < theta) (hT : 2 ≤ T) (n : ℕ) : ‖basis theta T i n‖ ≤ 6 := by
  simpa only [basis,norm_mul,Complex.norm_ofNat,show (3:ℝ)*2=6 by norm_num] using
    mul_le_mul_of_nonneg_left (profile_coefficient_bound i theta T htheta hT n)
      (show (0:ℝ) ≤ 3 by norm_num)

/-- One fixed bound covers the whole radius-two coefficient box at every
height. This supplies coefficient growth, not the missing moment supplier. -/
theorem family_coefficient_bound (theta T : ℝ) (htheta : 0 < theta) (hT : 2 ≤ T)
    (z : Fin 7 → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) (n : ℕ) :
    ‖family (basis theta T) z n‖ ≤ 84 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin 7, (12:ℝ) := by
      apply Finset.sum_le_sum; intro i hi
      rw [norm_mul]
      simpa only [show (2:ℝ)*6=12 by norm_num] using
        mul_le_mul (hz i) (basis_coefficient_bound i theta T htheta hT n)
        (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem witness_normalized_envelope :
    Tendsto (fun T : ℝ => T^(1/4000000:ℝ)*
      ((PRZZ.length (4/7-1/1000000) T)^(7/4:ℝ)+
        (PRZZ.length (4/7-1/1000000) T)^(7/8:ℝ)*T^(1/2:ℝ))/T) atTop (𝓝 0) := by
  exact PRZZ.normalized_error_tendsto_zero (4/7-1/1000000) (1/4000000)
    (by norm_num) (by norm_num)

/-- Instantiate a uniform square supplier at the actual witness. No
polarization or integrability premise is needed for this self-pairing.
The analytic square supplier remains explicit, not assumed proved. -/
theorem witness_of_uniform_squares (theta : ℝ)
    (E : ℝ → (ℕ → ℂ) → (ℕ → ℂ) → ℂ) (B : ℝ → ℝ)
    (hsquare : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : Fin 7 → ℂ,
      (∀ i, ‖z i‖ ≤ 2) →
      ‖E T (family (basis theta T) z) (family (basis theta T) z)‖ ≤ C*B T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ‖E T (PRZZ.coefficient PRZZ.witness theta T)
        (PRZZ.coefficient PRZZ.witness theta T)‖ ≤ C*B T := by
  obtain ⟨C,hC,h⟩ := hsquare
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT
  rw [witness_expansion]
  exact hT coordinates (fun i => (coordinates_unit i).trans (by norm_num))

#print axioms coordinates_unit
#print axioms witness_expansion
#print axioms witness_of_uniform_squares
#print axioms profile_unit
#print axioms profile_coefficient_bound
#print axioms basis_coefficient_bound
#print axioms family_coefficient_bound
#print axioms witness_normalized_envelope
end XiPrime8845.PRZZWitnessBasis
