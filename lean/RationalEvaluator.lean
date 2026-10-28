import NumericalGate

/-! Executable rational polynomial arithmetic and its complex semantics.
No native computation axiom is used: executable calculations are intended to
be checked by kernel reduction, and are linked to the coefficient functional. -/
open scoped BigOperators
open Polynomial

namespace XiPrime8845.RationalEvaluator
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Poly := List ℚ

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def smul (c : ℚ) (p : Poly) : Poly := p.map (c * ·)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (smul a q) (0::mul p q)

def term (d : ℕ) (c : ℚ) : Poly := List.replicate d 0 ++ [c]

noncomputable def interp : Poly → Polynomial ℂ
  | [] => 0
  | a::p => C (a:ℂ) + X * interp p

theorem interp_add (p q : Poly) : interp (add p q) = interp p + interp q := by
  induction p generalizing q with
  | nil => simp [add, interp]
  | cons a p ih =>
    cases q with
    | nil => simp [add, interp]
    | cons b q => simp only [add, interp, ih, Rat.cast_add, map_add]; ring

theorem interp_smul (c : ℚ) (p : Poly) : interp (smul c p) = C (c:ℂ) * interp p := by
  induction p with
  | nil => simp [smul, interp]
  | cons a p ih =>
    simp only [smul, List.map_cons, interp, Rat.cast_mul, map_mul] at *
    rw [ih]
    ring

theorem interp_mul (p q : Poly) : interp (mul p q) = interp p * interp q := by
  induction p with
  | nil => simp [mul, interp]
  | cons a p ih =>
    simp only [mul, interp_add, interp_smul, interp, Rat.cast_zero, map_zero, zero_add, ih]
    ring

theorem interp_term (d : ℕ) (c : ℚ) : interp (term d c) = C (c:ℂ) * X^d := by
  induction d with
  | zero => simp [term, interp]
  | succ d ih =>
    simp only [term, List.replicate_succ, List.cons_append, interp]
    change C ((0:ℚ):ℂ) + X * interp (term d c) = _
    rw [ih]
    simp only [Rat.cast_zero, map_zero, zero_add, pow_succ]
    ring

def betaFrom (n : ℕ) (θ : ℚ) : ℕ → Poly → ℚ
  | _, [] => 0
  | d, c::p => c * (θ^(d+n) * d.factorial / (d+n).factorial) + betaFrom n θ (d+1) p

def beta (n : ℕ) (θ : ℚ) (p : Poly) : ℚ := betaFrom n θ 0 p

theorem betaEval_monomial (n d : ℕ) (θ : ℝ) (c : ℂ) :
    CoefficientEvaluator.betaEval n θ (C c * X^d) =
      c * ((θ:ℂ)^(d+n) * d.factorial / (d+n).factorial) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  by_cases hc : c = 0
  · simp [hc, CoefficientEvaluator.betaEval]
  · simp [CoefficientEvaluator.betaEval, Polynomial.support_monomial _ hc]

theorem betaEval_add (n : ℕ) (θ : ℝ) (p q : Polynomial ℂ) :
    CoefficientEvaluator.betaEval n θ (p+q) =
      CoefficientEvaluator.betaEval n θ p + CoefficientEvaluator.betaEval n θ q :=
  map_add (CoefficientEvaluator.betaMap n θ) p q

theorem betaFrom_correct (n d : ℕ) (θ : ℚ) (p : Poly) :
    (betaFrom n θ d p : ℂ) =
      CoefficientEvaluator.betaEval n (θ:ℝ) (X^d * interp p) := by
  induction p generalizing d with
  | nil => simp [betaFrom, interp, CoefficientEvaluator.betaEval]
  | cons c p ih =>
    have he : X^d * interp (c::p) = C (c:ℂ) * X^d + X^(d+1) * interp p := by
      simp only [interp, pow_succ]; ring
    rw [he, betaEval_add, betaEval_monomial]
    simp only [betaFrom, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, ih, Complex.ofReal_ratCast]

theorem beta_correct (n : ℕ) (θ : ℚ) (p : Poly) :
    (beta n θ p : ℂ) = CoefficientEvaluator.betaEval n (θ:ℝ) (interp p) := by
  simpa [beta] using betaFrom_correct n 0 θ p

def sumPoly (p : List Poly) : Poly := p.foldr add []

theorem interp_sumPoly (p : List Poly) :
    interp (sumPoly p) = (p.map interp).sum := by
  induction p with
  | nil => simp [sumPoly, interp]
  | cons a p ih => simpa [sumPoly, interp_add] using congrArg (interp a + ·) ih

def invCoeff (a j d : ℕ) (p A θ : ℚ) : ℚ :=
  p / θ^d * (-1)^a * (-A)^j * (a+j).factorial * d.factorial /
    ((a.factorial : ℚ) * j.factorial * (d+1+a+j).factorial)

theorem invCoeff_cast (a j d : ℕ) (p A θ : ℚ) :
    (invCoeff a j d p A θ : ℂ) =
      CoefficientEvaluator.inverseCoeff a j d p A θ := by
  simp [invCoeff, CoefficientEvaluator.inverseCoeff]

def inverseTerm (N a d : ℕ) (p A θ : ℚ) : Poly :=
  sumPoly ((List.range (N+1)).map (fun j => term (d+1+a+j) (invCoeff a j d p A θ)))

theorem inverseTerm_correct (N a d : ℕ) (p A θ : ℚ) :
    interp (inverseTerm N a d p A θ) =
      CoefficientEvaluator.inversePoly N a A θ (C (p:ℂ)*X^d) := by
  rw [inverseTerm, interp_sumPoly]
  simp only [List.map_map, Function.comp_def, interp_term, invCoeff_cast]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  by_cases hp : (p:ℂ) = 0
  · simp [hp, CoefficientEvaluator.inversePoly, CoefficientEvaluator.inverseCoeff]
  · simp [CoefficientEvaluator.inversePoly, Polynomial.support_monomial _ hp]

noncomputable def inverseMap (N a : ℕ) (A : ℂ) (θ : ℝ) :
    Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  Polynomial.lsum (fun d =>
    { toFun := fun c => ∑ j ∈ Finset.range (N+1),
        C (CoefficientEvaluator.inverseCoeff a j d c A θ) * X^(d+1+a+j)
      map_add' := by
        intro x y
        simp only [CoefficientEvaluator.inverseCoeff, add_div, add_mul,
          map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [smul_eq_mul, RingHom.id_apply, Polynomial.smul_eq_C_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← mul_assoc, ← map_mul]
        congr 2
        unfold CoefficientEvaluator.inverseCoeff
        ring })

theorem inverseMap_apply (N a : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) :
    inverseMap N a A θ F = CoefficientEvaluator.inversePoly N a A θ F := rfl

theorem fsPoly_add (N a : ℕ) (e : ℤ) (A : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    CoefficientEvaluator.fsPoly N e a A θ (F+G) =
      CoefficientEvaluator.fsPoly N e a A θ F +
      CoefficientEvaluator.fsPoly N e a A θ G := by
  have hi : CoefficientEvaluator.inversePoly N a A θ (F+G) =
      CoefficientEvaluator.inversePoly N a A θ F +
      CoefficientEvaluator.inversePoly N a A θ G := map_add (inverseMap N a A θ) F G
  unfold CoefficientEvaluator.fsPoly
  split_ifs <;> simp_all [CoefficientEvaluator.scale, Polynomial.add_comp, mul_add]
  ring

theorem fsPoly_zero (N a : ℕ) (e : ℤ) (A : ℂ) (θ : ℝ) :
    CoefficientEvaluator.fsPoly N e a A θ 0 = 0 := by
  have h := fsPoly_add N a e A θ 0 0
  simpa using h.symm

theorem scale_monomial (d : ℕ) (p : ℂ) (θ : ℝ) :
    CoefficientEvaluator.scale θ (C p * X^d) = C (p/(θ:ℂ)^d)*X^d := by
  simp [CoefficientEvaluator.scale, Polynomial.mul_comp, Polynomial.pow_comp,
    mul_pow, ← map_pow, ← mul_assoc, ← map_mul, div_eq_mul_inv]

def fsTerm (N a d : ℕ) (e : ℤ) (p A θ : ℚ) : Poly :=
  if e = -1 then inverseTerm N a d p A θ
  else if a = 0 then
    if e = 1 then add (term (d-1) ((p*d/θ^(d-1))/θ)) (term d (A*p/θ^d))
    else if e = 0 then term d (p/θ^d) else []
  else if e = 1 ∧ a = 1 then term d (p/θ^d) else []

theorem fsTerm_correct (N a d : ℕ) (e : ℤ) (p A θ : ℚ) :
    interp (fsTerm N a d e p A θ) =
      CoefficientEvaluator.fsPoly N e a A θ (C (p:ℂ)*X^d) := by
  unfold fsTerm CoefficientEvaluator.fsPoly
  split_ifs
  · exact inverseTerm_correct N a d p A θ
  · rw [interp_add, interp_term, interp_term, Polynomial.derivative_C_mul_X_pow,
      scale_monomial, scale_monomial]
    push_cast
    simp only [div_eq_mul_inv, map_mul]
    ring
  · simpa only [interp_term, Rat.cast_div, Rat.cast_pow, Complex.ofReal_ratCast]
      using (scale_monomial d (p:ℂ) (θ:ℝ)).symm
  · rfl
  · simpa only [interp_term, Rat.cast_div, Rat.cast_pow, Complex.ofReal_ratCast]
      using (scale_monomial d (p:ℂ) (θ:ℝ)).symm
  · rfl

abbrev Profile := List (ℕ × ℚ)
noncomputable def profile (p : Profile) : Polynomial ℂ :=
  (p.map (fun dc => C (dc.2:ℂ)*X^dc.1)).sum

def fs (N a : ℕ) (e : ℤ) (A θ : ℚ) (p : Profile) : Poly :=
  sumPoly (p.map (fun dc => fsTerm N a dc.1 e dc.2 A θ))

theorem fs_correct (N a : ℕ) (e : ℤ) (A θ : ℚ) (p : Profile) :
    interp (fs N a e A θ p) = CoefficientEvaluator.fsPoly N e a A θ (profile p) := by
  rw [fs, interp_sumPoly]
  simp only [List.map_map, Function.comp_def, fsTerm_correct]
  induction p with
  | nil => simp [profile, fsPoly_zero]
  | cons dc p ih =>
    simpa [profile, fsPoly_add] using ih

def opMinus (q : ℕ → ℚ) (i : ℕ) : ℚ := q i * (-1)^i * i.factorial
def opPlus (D : ℕ) (q : ℕ → ℚ) (i : ℕ) : ℚ :=
  i.factorial * ∑ a ∈ Finset.Ico i (D+1), q a * (a.choose i : ℚ)
def recip (s : ℚ) (i j : ℕ) : ℚ :=
  (-1)^(i+j) * ((i+j).choose i : ℚ) / s^(i+j+1)
def weight (D : ℕ) (op : ℕ → ℚ) (s : ℚ) (i j : ℕ) : ℚ :=
  ∑ a ∈ Finset.Ico i (D+1), ∑ b ∈ Finset.Ico j (D+1),
    op a * op b * recip s (a-i) (b-j)

theorem opMinus_cast (q : ℕ → ℚ) (i : ℕ) :
    (opMinus q i : ℂ) = FiniteJet.opMinus (fun i => (q i:ℂ)) i := by
  simp [opMinus, FiniteJet.opMinus]
theorem opPlus_cast (D : ℕ) (q : ℕ → ℚ) (i : ℕ) :
    (opPlus D q i : ℂ) = FiniteJet.opPlus D (fun i => (q i:ℂ)) i := by
  simp [opPlus, FiniteJet.opPlus]
theorem weight_cast (D : ℕ) (op : ℕ → ℚ) (s : ℚ) (i j : ℕ) :
    (weight D op s i j : ℂ) = FiniteJet.W D (fun i => (op i:ℂ)) s i j := by
  simp [weight, recip, FiniteJet.W, FiniteJet.reciprocalCoeff]

def fused (D : ℕ) (W : ℕ → ℕ → ℚ) (f g : ℕ → Poly) : Poly :=
  sumPoly ((List.range (D+1)).map fun i =>
    mul (f i) (sumPoly ((List.range (D+1)).map fun j => smul (W i j) (g j))))

theorem fused_correct (D : ℕ) (W : ℕ → ℕ → ℚ) (f g : ℕ → Poly) :
    interp (fused D W f g) = CoefficientEvaluator.fusedPoly D
      (fun i j => (W i j:ℂ)) (fun i => interp (f i)) (fun j => interp (g j)) := by
  rw [CoefficientEvaluator.fusedPoly_cached]
  simp only [fused, interp_sumPoly, List.map_map, Function.comp_def, interp_mul,
    interp_smul]
  simp only [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

def pole (l m : ℕ) (E : ℤ → ℤ → ℕ → ℚ) : ℚ :=
  ∑ k ∈ Finset.range (min l m+1), ∑ r ∈ Finset.range (l-k+1),
    ∑ t ∈ Finset.range (m-k+1),
      ((l.choose k : ℚ) * m.descFactorial k * (l-k).choose r * (m-k).choose t *
        (-1)^(l+m+r+t)) * E (1-(l:ℤ)+k+r) (1-(m:ℤ)+k+t) (1+2*k+r+t)

theorem pole_cast (l m : ℕ) (E : ℤ → ℤ → ℕ → ℚ) :
    (pole l m E : ℂ) = BetaKernel.poleSum l m (fun e f n => (E e f n:ℂ)) := by
  simp [pole, BetaKernel.poleSum]

def pair (N D l m : ℕ) (op : ℕ → ℚ) (A θ : ℚ) (F G : Profile) : ℚ :=
  pole l m (fun e f n => beta n θ (fused D (weight D op (2*A))
    (fun i => fs N i e A θ F) (fun j => fs N j f A θ G))) / θ^(l+m)

theorem pair_correct (N D l m : ℕ) (op : ℕ → ℚ) (A θ : ℚ) (F G : Profile) :
    (pair N D l m op A θ F G : ℂ) = CoefficientEvaluator.pairFusedEvaluator
      N D l m (fun i => (op i:ℂ)) A θ (profile F) (profile G) := by
  simp only [pair, Rat.cast_div, Rat.cast_pow, pole_cast, beta_correct,
    fused_correct, weight_cast, fs_correct, Rat.cast_mul, Rat.cast_ofNat,
    CoefficientEvaluator.pairFusedEvaluator, Complex.ofReal_ratCast]

def side (N D : ℕ) (op : ℕ → ℚ) (A θ : ℚ) (F G : Profile) : ℚ :=
  pair N D 0 0 op A θ F F + 2 * pair N D 0 2 op A θ F G + pair N D 2 2 op A θ G G

theorem side_correct (N D : ℕ) (op : ℕ → ℚ) (A θ : ℚ) (F G : Profile) :
    (side N D op A θ F G : ℂ) = CoefficientEvaluator.cachedSide
      N D (fun i => (op i:ℂ)) A θ (profile F) (profile G) := by
  simp [side, pair_correct, CoefficientEvaluator.cachedSide]

def R : ℚ := 1.04440033
def θ : ℚ := 4/7 - 1/1000000
def F : Profile := [(1,-0.30528514),(2,2.50038954),(3,-1.12177152),(4,-0.07333288)]
def G : Profile := [(1,1.89779072),(2,0.56594804),(3,0.07023055)]
def q : ℕ → ℚ
  | 0 => 1 | 1 => -2.27043254 | 2 => 0.304358115 | 3 => 0.16793368
  | 4 => 4.34152016 | 5 => -5.3105844 | 6 => 1.7701948 | _ => 0

def minusValue : ℚ := side 24 6 (opMinus q) (-R) θ F G
def plusValue : ℚ := side 24 6 (opPlus 6 q) R θ F G

theorem witness_parameters : (R:ℝ) = NumericalGate.R ∧ (θ:ℝ) = NumericalGate.θ := by
  norm_num [R, θ, NumericalGate.R, NumericalGate.θ]
theorem witness_profiles : profile F = NumericalGate.F ∧ profile G = NumericalGate.G := by
  norm_num [profile, F, G, NumericalGate.F, NumericalGate.G]
  constructor <;> ring
theorem witness_q : (fun i => (q i:ℂ)) = NumericalGate.qCoeff := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> norm_num [q, NumericalGate.qCoeff]
  split <;> (try omega)
  split <;> (try omega)
  norm_num

theorem finiteValue_exact : NumericalGate.finiteValue =
    (minusValue:ℂ) + Complex.exp (2*(NumericalGate.R:ℂ)) * (plusValue:ℂ) := by
  have hm : (fun i => (opMinus q i:ℂ)) = FiniteJet.opMinus NumericalGate.qCoeff := by
    funext i
    rw [opMinus_cast, witness_q]
  have hp : (fun i => (opPlus 6 q i:ℂ)) = FiniteJet.opPlus 6 NumericalGate.qCoeff := by
    funext i
    rw [opPlus_cast, witness_q]
  unfold minusValue plusValue NumericalGate.finiteValue CoefficientEvaluator.cachedEvaluator
  rw [side_correct, side_correct, hm, hp]
  simp only [witness_profiles.1, witness_profiles.2,
    Rat.cast_neg, ← Complex.ofReal_ratCast, witness_parameters.1, witness_parameters.2]

#print axioms finiteValue_exact
#print axioms fs_correct
#print axioms interp_add
#print axioms interp_mul
#print axioms beta_correct
end XiPrime8845.RationalEvaluator
