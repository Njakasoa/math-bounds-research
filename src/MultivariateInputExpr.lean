import CanonicalInputExpr

/-!
# Coefficient-normalized multivariate input syntax

The polynomial coefficients are grouped before the AST is constructed.  Thus
cancellation is reflected in the exact unit-box amplitude.  The finite support
lists are chosen noncomputably; no extraction claim is made for this constructor.
-/
namespace MultivariateInputExpr

open BoxPolynomialBounds
open scoped BigOperators

abbrev InputPoly (m : ℕ) := MvPolynomial (Fin m) ℚ
abbrev Exponent (m : ℕ) := Fin m →₀ ℕ
abbrev Syntax (m : ℕ) := BoxPolynomialBounds.Expr m 1

variable {m : ℕ}

/-- Rational coefficient ℓ¹ norm after grouping equal monomials. -/
def coeffL1 (p : InputPoly m) : ℚ :=
  ∑ e ∈ p.support, |p.coeff e|

noncomputable def realEval (p : InputPoly m) (u : Fin m → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) u p

noncomputable def complexEval (p : InputPoly m) (z : Fin m → ℂ) : ℂ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℂ) z p

lemma complexEval_ofReal (p : InputPoly m) (u : Fin m → ℝ) :
    complexEval p (fun i => (u i : ℂ)) = (realEval p u : ℂ) :=
  PolynomialReadoutAnalytic.eval_ofReal p u

/-- Compute the coefficient norm on any larger finite support. -/
theorem coeffL1_eq_sum_of_support_subset (p : InputPoly m) (s : Finset (Exponent m))
    (hs : p.support ⊆ s) : coeffL1 p = ∑ e ∈ s, |p.coeff e| := by
  classical
  apply Finset.sum_subset hs
  intro e _ he
  rw [MvPolynomial.notMem_support_iff.mp he, abs_zero]

@[simp] theorem coeffL1_monomial (e : Exponent m) (c : ℚ) :
    coeffL1 (MvPolynomial.monomial e c) = |c| := by
  rw [coeffL1_eq_sum_of_support_subset _ {e} MvPolynomial.support_monomial_subset]
  simp

/-- Exact norm for a finite sum with distinct exponent vectors. -/
theorem coeffL1_sum_monomials (s : Finset (Exponent m)) (c : Exponent m → ℚ) :
    coeffL1 (∑ e ∈ s, MvPolynomial.monomial e (c e)) = ∑ e ∈ s, |c e| := by
  classical
  have hs : (∑ e ∈ s, MvPolynomial.monomial e (c e)).support ⊆ s := by
    intro e he
    by_contra hen
    have hz : (∑ f ∈ s, MvPolynomial.monomial f (c f)).coeff e = 0 := by
      simp [MvPolynomial.coeff_monomial, hen]
    exact (MvPolynomial.mem_support_iff.mp he) hz
  rw [coeffL1_eq_sum_of_support_subset _ s hs]
  apply Finset.sum_congr rfl
  intro e he
  simp [MvPolynomial.coeff_monomial, he]

/-- Reindexing by distinct exponent vectors preserves the exact coefficient norm. -/
theorem coeffL1_sum_monomials_injective {ι : Type*} (s : Finset ι)
    (e : ι → Exponent m) (he : Function.Injective e) (c : ι → ℚ) :
    coeffL1 (∑ i ∈ s, MvPolynomial.monomial (e i) (c i)) = ∑ i ∈ s, |c i| := by
  classical
  let p : InputPoly m := ∑ i ∈ s, MvPolynomial.monomial (e i) (c i)
  have hs : p.support ⊆ s.image e := by
    intro d hd
    by_contra hn
    have hz : p.coeff d = 0 := by
      simp only [p, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro i hi
      have hne : e i ≠ d := by
        intro h
        exact hn (Finset.mem_image.mpr ⟨i, hi, h⟩)
      simp [MvPolynomial.coeff_monomial, hne]
    exact (MvPolynomial.mem_support_iff.mp hd) hz
  change coeffL1 p = _
  rw [coeffL1_eq_sum_of_support_subset p (s.image e) hs,
    Finset.sum_image (fun i _ j _ h => he h)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [p, MvPolynomial.coeff_monomial, he.eq_iff, hi]

@[simp] theorem coeffL1_C (c : ℚ) : coeffL1 (MvPolynomial.C c : InputPoly m) = |c| := by
  exact coeffL1_monomial 0 c

@[simp] theorem coeffL1_zero : coeffL1 (0 : InputPoly m) = 0 := by
  simp [coeffL1]

@[simp] theorem coeffL1_one : coeffL1 (1 : InputPoly m) = 1 := by
  simpa using (coeffL1_C (m := m) 1)

/-- Repeated multiplication of a single input coordinate. -/
def inputPow (i : Fin m) : ℕ → Syntax m
  | 0 => .const 1
  | k + 1 => .mul (inputPow i k) (.input i)

@[simp] theorem inputPow_amp (i : Fin m) (k : ℕ) (r : ℚ) :
    (inputPow i k).amp 1 r = 1 := by
  induction k <;> simp_all [inputPow, Expr.amp]

@[simp] theorem inputPow_lip (i : Fin m) (k : ℕ) (B r : ℚ) :
    (inputPow i k).lip B r = 0 := by
  induction k <;> simp_all [inputPow, Expr.lip]

@[simp] theorem inputPow_toMvPolynomial (i : Fin m) (k : ℕ) :
    (inputPow i k).toMvPolynomial = MvPolynomial.X (Sum.inl i) ^ k := by
  induction k <;> simp_all [inputPow, Expr.toMvPolynomial, pow_succ]

/-- Product of coordinate powers from a list of coordinates. -/
def fromFactors (e : Exponent m) : List (Fin m) → Syntax m
  | [] => .const 1
  | i :: is => .mul (inputPow i (e i)) (fromFactors e is)

@[simp] theorem fromFactors_amp (e : Exponent m) (is : List (Fin m)) (r : ℚ) :
    (fromFactors e is).amp 1 r = 1 := by
  induction is <;> simp_all [fromFactors, Expr.amp]

@[simp] theorem fromFactors_lip (e : Exponent m) (is : List (Fin m)) (B r : ℚ) :
    (fromFactors e is).lip B r = 0 := by
  induction is <;> simp_all [fromFactors, Expr.lip]

@[simp] theorem fromFactors_toMvPolynomial (e : Exponent m) (is : List (Fin m)) :
    (fromFactors e is).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin m → Fin m ⊕ Fin 1)
        ((is.map (fun i => (MvPolynomial.X i : InputPoly m) ^ (e i))).prod) := by
  induction is <;> simp_all [fromFactors, Expr.toMvPolynomial]

/-- The input monomial of a given exponent vector, including exponent zero. -/
noncomputable def inputMonomial (e : Exponent m) : Syntax m :=
  fromFactors e e.support.toList

@[simp] theorem inputMonomial_amp (e : Exponent m) (r : ℚ) :
    (inputMonomial e).amp 1 r = 1 := by
  simp [inputMonomial]

@[simp] theorem inputMonomial_lip (e : Exponent m) (B r : ℚ) :
    (inputMonomial e).lip B r = 0 := by
  simp [inputMonomial]

@[simp] theorem inputMonomial_toMvPolynomial (e : Exponent m) :
    (inputMonomial e).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin m → Fin m ⊕ Fin 1)
        (MvPolynomial.monomial e 1) := by
  simp [inputMonomial, Finset.prod_map_toList]

noncomputable def fromTerms (p : InputPoly m) : List (Exponent m) → Syntax m
  | [] => .const 0
  | e :: es => .add (.mul (.const (p.coeff e)) (inputMonomial e)) (fromTerms p es)

/-- Normalize from grouped coefficients; chosen support lists are noncomputable. -/
noncomputable def canon (p : InputPoly m) : Syntax m := fromTerms p p.support.toList

@[simp] theorem fromTerms_amp (p : InputPoly m) (es : List (Exponent m)) (r : ℚ) :
    (fromTerms p es).amp 1 r = (es.map (fun e => |p.coeff e|)).sum := by
  induction es <;> simp_all [fromTerms, Expr.amp]

@[simp] theorem fromTerms_lip (p : InputPoly m) (es : List (Exponent m)) (B r : ℚ) :
    (fromTerms p es).lip B r = 0 := by
  induction es <;> simp_all [fromTerms, Expr.lip]

@[simp] theorem canon_amp (p : InputPoly m) (r : ℚ) :
    (canon p).amp 1 r = coeffL1 p := by
  simp [canon, coeffL1, Finset.sum_map_toList]

@[simp] theorem canon_lip (p : InputPoly m) (B r : ℚ) :
    (canon p).lip B r = 0 := by
  simp [canon]

@[simp] theorem fromTerms_toMvPolynomial (p : InputPoly m) (es : List (Exponent m)) :
    (fromTerms p es).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin m → Fin m ⊕ Fin 1)
        ((es.map (fun e => MvPolynomial.monomial e (p.coeff e))).sum) := by
  induction es with
  | nil => simp [fromTerms, Expr.toMvPolynomial]
  | cons e es ih =>
    simp only [fromTerms, Expr.toMvPolynomial, inputMonomial_toMvPolynomial, ih,
      List.map_cons, List.sum_cons, map_add]
    congr 1
    rw [← MvPolynomial.rename_C, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

@[simp] theorem canon_toMvPolynomial (p : InputPoly m) :
    (canon p).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin m → Fin m ⊕ Fin 1) p := by
  simp [canon, Finset.sum_map_toList, MvPolynomial.support_sum_monomial_coeff]

@[simp] theorem canon_eval (p : InputPoly m) (u : Fin m → ℝ) (x : Fin 1 → ℝ) :
    (canon p).eval u x = realEval p u := by
  rw [← Expr.eval_toMvPolynomial, canon_toMvPolynomial, MvPolynomial.eval₂Hom_rename]
  rfl

@[simp] theorem canon_evalComplex (p : InputPoly m) (u : Fin m → ℂ) (x : Fin 1 → ℂ) :
    (canon p).evalComplex u x = complexEval p u := by
  rw [← Expr.evalComplex_toMvPolynomial, canon_toMvPolynomial, MvPolynomial.eval₂Hom_rename]
  rfl

theorem coeffL1_nonneg (p : InputPoly m) : 0 ≤ coeffL1 p := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Unit-box evaluation is controlled by the grouped coefficient norm. -/
theorem realEval_abs_le_coeffL1 (p : InputPoly m) (u : Fin m → ℝ)
    (hu : ∀ i, |u i| ≤ 1) : |realEval p u| ≤ (coeffL1 p : ℝ) := by
  have h := (canon p).eval_abs_le_amp (B := 1) (r := 0)
    (by norm_num) (by norm_num) (u := u) (x := fun _ => 0)
    (fun i => by simpa using hu i) (fun _ => by simp)
  simpa using h

/-- Closed unit-polydisc evaluation is controlled by the grouped coefficient norm. -/
theorem complexEval_norm_le_coeffL1 (p : InputPoly m) (z : Fin m → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) : ‖complexEval p z‖ ≤ (coeffL1 p : ℝ) := by
  have h := (canon p).evalComplex_norm_le_amp (B := 1) (r := 0)
    (by norm_num) (by norm_num) (u := z) (x := fun _ => 0)
    (fun i => by simpa using hz i) (fun _ => by simp)
  simpa using h

end MultivariateInputExpr
