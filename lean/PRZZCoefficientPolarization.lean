import PRZZInterface

/-! Polarization for the literal finite Dirichlet polynomial and a general
arithmetic main-term kernel. Both coefficient slots are independent.
The uniform square estimate below is an explicit hypothesis: the existing
fixed-js moment theorem does not yet supply it on complex linear combinations.
Integrability is retained, since totalized Bochner integrals are not linear
without it. No Hermitian symmetry of the shifted zeta kernel is required. -/
noncomputable section
open Complex MeasureTheory Filter
open scoped BigOperators
namespace XiPrime8845.PRZZCoefficientPolarization
set_option maxHeartbeats 2000000

def combine (a b : ℕ → ℂ) (z : ℂ) : ℕ → ℂ := fun n => a n + z*b n

theorem polynomial_combine (a b : ℕ → ℂ) (z s : ℂ) (N : ℕ) :
    PRZZ.dirichletPolynomial (combine a b z) N s =
      PRZZ.dirichletPolynomial a N s + z*PRZZ.dirichletPolynomial b N s := by
  simp only [PRZZ.dirichletPolynomial, combine, add_div, mul_div_assoc,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- Four rotations; conjugate-linearity is in the second slot. -/
theorem scalar_polarization (a b : ℂ) :
    4*(a*star b) =
      (a+b)*star (a+b) - (a-b)*star (a-b) +
      I*((a+I*b)*star (a+I*b)) - I*((a-I*b)*star (a-I*b)) := by
  simp only [star_add, star_sub, star_mul, Complex.star_def, conj_I]
  ring_nf
  simp only [I_sq]
  ring

def density (N : ℕ) (g : ℝ → ℂ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  g t * PRZZ.dirichletPolynomial a N (1/2+t*I) *
    star (PRZZ.dirichletPolynomial b N (1/2+t*I))

theorem density_polarization (N : ℕ) (g : ℝ → ℂ) (a b : ℕ → ℂ) (t : ℝ) :
    4*density N g a b t =
      density N g (combine a b 1) (combine a b 1) t -
      density N g (combine a b (-1)) (combine a b (-1)) t +
      I*density N g (combine a b I) (combine a b I) t -
      I*density N g (combine a b (-I)) (combine a b (-I)) t := by
  simp only [density, polynomial_combine, one_mul, neg_mul,
    ← sub_eq_add_neg]
  linear_combination g t * scalar_polarization
    (PRZZ.dirichletPolynomial a N (1/2+t*I))
    (PRZZ.dirichletPolynomial b N (1/2+t*I))

def pairing (μ : Measure ℝ) (N : ℕ) (g : ℝ → ℂ) (a b : ℕ → ℂ) : ℂ :=
  ∫ t, density N g a b t ∂μ

theorem pairing_polarization (μ : Measure ℝ) (N : ℕ) (g : ℝ → ℂ)
    (a b : ℕ → ℂ)
    (h : ∀ z ∈ ([1,-1,I,-I] : List ℂ),
      Integrable (density N g (combine a b z) (combine a b z)) μ) :
    4*pairing μ N g a b =
      pairing μ N g (combine a b 1) (combine a b 1) -
      pairing μ N g (combine a b (-1)) (combine a b (-1)) +
      I*pairing μ N g (combine a b I) (combine a b I) -
      I*pairing μ N g (combine a b (-I)) (combine a b (-I)) := by
  have h1 := h 1 (by simp)
  have h2 := h (-1) (by simp)
  have h3 := h I (by simp)
  have h4 := h (-I) (by simp)
  have he : (∫ t, 4*density N g a b t ∂μ) =
      ∫ t, (density N g (combine a b 1) (combine a b 1) t -
        density N g (combine a b (-1)) (combine a b (-1)) t +
        I*density N g (combine a b I) (combine a b I) t -
        I*density N g (combine a b (-I)) (combine a b (-I)) t) ∂μ :=
    integral_congr_ae (Eventually.of_forall (density_polarization N g a b))
  have hsub := integral_sub ((h1.sub h2).add (h3.const_mul I)) (h4.const_mul I)
  have hadd := integral_add (h1.sub h2) (h3.const_mul I)
  have hdiff := integral_sub h1 h2
  simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd hdiff
  rw [integral_const_mul, hsub, hadd, hdiff, integral_const_mul, integral_const_mul] at he
  exact he

/-- Arbitrary double-sum kernels include the gcd/lcm and Gamma main terms. -/
def arithmeticPairing (N : ℕ) (K : ℕ → ℕ → ℂ) (a b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, a n*star (b m)*K n m

theorem arithmetic_polarization (N : ℕ) (K : ℕ → ℕ → ℂ) (a b : ℕ → ℂ) :
    4*arithmeticPairing N K a b =
      arithmeticPairing N K (combine a b 1) (combine a b 1) -
      arithmeticPairing N K (combine a b (-1)) (combine a b (-1)) +
      I*arithmeticPairing N K (combine a b I) (combine a b I) -
      I*arithmeticPairing N K (combine a b (-I)) (combine a b (-I)) := by
  simp only [arithmeticPairing, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simp only [combine, star_add, star_mul, star_neg, star_one, Complex.star_def, conj_I]
  ring_nf
  simp only [I_sq]
  ring

/-- Historical printed kernel, without either coefficient. Independent
coefficient bridges must use densityGcdKernel, not this orientation. -/
def gcdKernel (T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) (d e : ℕ) : ℂ :=
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  1/(Nat.lcm d e:ℂ) * (Nat.gcd d e:ℂ)^(alpha+beta) /
    ((d:ℂ)^alpha*(e:ℂ)^beta) *
    ∫ t : ℝ, (riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
      ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2):ℝ):ℂ)^(alpha+beta)) * (Phi (t/T):ℂ)

theorem gcdMainTerm_eq (P Q : PRZZ.Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) :
    PRZZ.gcdMainTerm P Q theta T Phi A B =
      arithmeticPairing (PRZZ.cutoff theta T) (gcdKernel T Phi A B)
        (PRZZ.coefficient P theta T) (PRZZ.coefficient Q theta T) := by
  unfold PRZZ.gcdMainTerm arithmeticPairing gcdKernel
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  dsimp only
  ring

/-- Correct kernel for the stated density, also for complex combinations. -/
def densityGcdKernel (T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℕ → ℕ → ℂ :=
  gcdKernel T Phi B A

theorem densityGcdMainTerm_eq (P Q : PRZZ.Profiles) (theta T : ℝ)
    (Phi : ℝ → ℝ) (A B : ℂ) :
    PRZZ.densityGcdMainTerm P Q theta T Phi A B =
      arithmeticPairing (PRZZ.cutoff theta T) (densityGcdKernel T Phi A B)
        (PRZZ.coefficient P theta T) (PRZZ.coefficient Q theta T) :=
  gcdMainTerm_eq P Q theta T Phi B A

def zetaKernel (T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (1/2+A/(Real.log T:ℂ)+t*I) *
    riemannZeta (1/2+B/(Real.log T:ℂ)-t*I) * (Phi (t/T):ℂ)

/-- Exact equality with the public all-real-time moment, not a new model. -/
theorem twistedMoment_eq (P Q : PRZZ.Profiles) (theta T : ℝ)
    (Phi : ℝ → ℝ) (A B : ℂ) :
    PRZZ.twistedMoment P Q theta T Phi A B =
      pairing volume (PRZZ.cutoff theta T) (zetaKernel T Phi A B)
        (PRZZ.coefficient P theta T) (PRZZ.coefficient Q theta T) := by
  unfold PRZZ.twistedMoment pairing density zetaKernel
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by ring)

/-- A quantitative transfer for a possibly non-Hermitian error form.
Four square bounds B give the mixed bound B, not 4B. -/
theorem mixed_bound (E : (ℕ → ℂ) → (ℕ → ℂ) → ℂ) (a b : ℕ → ℂ) (B : ℝ)
    (hp : 4*E a b = E (combine a b 1) (combine a b 1) -
      E (combine a b (-1)) (combine a b (-1)) +
      I*E (combine a b I) (combine a b I) -
      I*E (combine a b (-I)) (combine a b (-I)))
    (h : ∀ z ∈ ([1,-1,I,-I] : List ℂ), ‖E (combine a b z) (combine a b z)‖ ≤ B) :
    ‖E a b‖ ≤ B := by
  have hh := congrArg norm hp
  simp only [norm_mul, norm_ofNat] at hh
  have hsum := norm_sub_le
    (E (combine a b 1) (combine a b 1) - E (combine a b (-1)) (combine a b (-1)) +
      I*E (combine a b I) (combine a b I))
    (I*E (combine a b (-I)) (combine a b (-I)))
  have hadd := norm_add_le
    (E (combine a b 1) (combine a b 1) - E (combine a b (-1)) (combine a b (-1)))
    (I*E (combine a b I) (combine a b I))
  have hsub := norm_sub_le (E (combine a b 1) (combine a b 1))
    (E (combine a b (-1)) (combine a b (-1)))
  simp only [norm_mul, norm_I, one_mul] at hsum hadd
  have h1 := h 1 (by simp)
  have h2 := h (-1) (by simp)
  have h3 := h I (by simp)
  have h4 := h (-I) (by simp)
  linarith

/-- The actual integral minus the arithmetic double sum has the same
polarization, with no reality or symmetry assumption on either kernel. -/
theorem error_polarization (μ : Measure ℝ) (N : ℕ) (g : ℝ → ℂ)
    (K : ℕ → ℕ → ℂ) (a b : ℕ → ℂ)
    (h : ∀ z ∈ ([1,-1,I,-I] : List ℂ),
      Integrable (density N g (combine a b z) (combine a b z)) μ) :
    let E := fun a b => pairing μ N g a b - arithmeticPairing N K a b
    4*E a b = E (combine a b 1) (combine a b 1) -
      E (combine a b (-1)) (combine a b (-1)) +
      I*E (combine a b I) (combine a b I) -
      I*E (combine a b (-I)) (combine a b (-I)) := by
  dsimp only
  linear_combination pairing_polarization μ N g a b h -
    arithmetic_polarization N K a b

def family {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ) (z : ι → ℂ) : ℕ → ℂ :=
  fun n => ∑ i, z i*basis i n

theorem family_combine {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (z w : ι → ℂ) (u : ℂ) :
    combine (family basis z) (family basis w) u = family basis (fun i => z i+u*w i) := by
  funext n
  simp only [combine, family, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Uniformity includes the common eventual height threshold, not just C.
The square hypothesis is on the radius-two box, so it contains all four
rotations of two radius-one profiles. It is NOT deduced from bounds on
the individual basis vectors. Both the basis and z,w may depend on height.
This algebraic theorem does not supply analytic uniformity of that basis. -/
theorem finite_family_uniform {ι : Type*} [Fintype ι] (basis : ℝ → ι → ℕ → ℂ)
    (E : ℝ → (ℕ → ℂ) → (ℕ → ℂ) → ℂ) (B : ℝ → ℝ)
    (hp : ∀ᶠ T : ℝ in atTop, ∀ a b, 4*E T a b = E T (combine a b 1) (combine a b 1) -
      E T (combine a b (-1)) (combine a b (-1)) +
      I*E T (combine a b I) (combine a b I) -
      I*E T (combine a b (-I)) (combine a b (-I)))
    (hsquare : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : ι → ℂ,
      (∀ i, ‖z i‖ ≤ 2) → ‖E T (family (basis T) z) (family (basis T) z)‖ ≤ C*B T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ z w : ι → ℂ,
      (∀ i, ‖z i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) →
      ‖E T (family (basis T) z) (family (basis T) w)‖ ≤ C*B T := by
  obtain ⟨C,hC,h⟩ := hsquare
  refine ⟨C,hC,?_⟩
  filter_upwards [h,hp] with T hT hpT
  intro z w hz hw
  apply mixed_bound (E T) _ _ (C*B T) (hpT _ _)
  intro u hu
  have hu1 : ‖u‖ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp
  rw [family_combine]
  apply hT
  intro i
  calc
    ‖z i+u*w i‖ ≤ ‖z i‖+‖u*w i‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_mul,hu1,one_mul]; linarith [hz i,hw i]

/-- Backward-compatible fixed-basis specialization. -/
theorem finite_family_uniform_fixed {ι : Type*} [Fintype ι] (basis : ι → ℕ → ℂ)
    (E : ℝ → (ℕ → ℂ) → (ℕ → ℂ) → ℂ) (B : ℝ → ℝ)
    (hp : ∀ᶠ T : ℝ in atTop, ∀ a b, 4*E T a b = E T (combine a b 1) (combine a b 1) -
      E T (combine a b (-1)) (combine a b (-1)) +
      I*E T (combine a b I) (combine a b I) -
      I*E T (combine a b (-I)) (combine a b (-I)))
    (hsquare : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : ι → ℂ,
      (∀ i, ‖z i‖ ≤ 2) → ‖E T (family basis z) (family basis z)‖ ≤ C*B T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ z w : ι → ℂ,
      (∀ i, ‖z i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) →
      ‖E T (family basis z) (family basis w)‖ ≤ C*B T :=
  finite_family_uniform (fun _ => basis) E B hp hsquare

/-- The second target term leaves only half the first term's margin. -/
theorem target_exponent_margins (gap tau : ℝ) (hg : 0 < gap)
    (ht : tau < 7*gap/8) :
    tau+(7/4:ℝ)*(4/7-gap) < 1 ∧
      tau+1/2+(7/8:ℝ)*(4/7-gap) < 1 := by
  constructor <;> linarith

/-- At gap=10^-6, tau=1/4000000 works for BOTH target terms. -/
theorem witness_exponent_margins :
    (1/4000000:ℝ)+(7/4:ℝ)*(4/7-1/1000000) < 1 ∧
    (1/4000000:ℝ)+1/2+(7/8:ℝ)*(4/7-1/1000000) < 1 := by
  norm_num

#print axioms polynomial_combine
#print axioms scalar_polarization
#print axioms density_polarization
#print axioms pairing_polarization
#print axioms arithmetic_polarization
#print axioms gcdMainTerm_eq
#print axioms densityGcdMainTerm_eq
#print axioms twistedMoment_eq
#print axioms mixed_bound
#print axioms error_polarization
#print axioms family_combine
#print axioms finite_family_uniform
#print axioms finite_family_uniform_fixed
#print axioms target_exponent_margins
#print axioms witness_exponent_margins
end XiPrime8845.PRZZCoefficientPolarization
