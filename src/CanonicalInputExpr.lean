import GenericHolomorphicPole
import BoxPolynomialBounds

/-! A coefficient-normalized input syntax, with exact ℓ¹ magnitude bound. -/
namespace CanonicalInputExpr

open BoxPolynomialBounds GenericHolomorphicPole

abbrev Exponent := Fin 1 →₀ ℕ
abbrev Syntax := BoxPolynomialBounds.Expr 1 1

private theorem exponent_injective : Function.Injective (fun e : Exponent => e 0) := by
  intro a b hab
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using hab

private def degreeLE (a b : Exponent) : Prop := a 0 ≤ b 0
local instance : DecidableRel degreeLE := fun a b => inferInstanceAs (Decidable (a 0 ≤ b 0))
local instance : IsTrans Exponent degreeLE := ⟨fun _ _ _ => Nat.le_trans⟩
local instance : Std.Antisymm degreeLE :=
  ⟨fun _ _ hab hba => exponent_injective (Nat.le_antisymm hab hba)⟩
local instance : Std.Total degreeLE := ⟨fun a b => Nat.le_total (a 0) (b 0)⟩

private theorem sum_map_sort {A : Type*} [AddCommMonoid A]
    (s : Finset Exponent) (f : Exponent → A) :
    ((s.sort degreeLE).map f).sum = ∑ e ∈ s, f e := by
  have h := ((Finset.sort_perm_toList s degreeLE).map f).sum_eq
  simpa using h

/-- The rational coefficient ℓ¹ norm, after polynomial cancellation. -/
def coeffL1 (p : InputPoly) : ℚ :=
  ∑ e ∈ p.support, |p.coeff e|

/-- Compute the norm on any finite set containing the support. -/
theorem coeffL1_eq_sum_of_support_subset (p : InputPoly) (s : Finset Exponent)
    (hs : p.support ⊆ s) : coeffL1 p = ∑ e ∈ s, |p.coeff e| := by
  classical
  apply Finset.sum_subset hs
  intro e _ he
  rw [MvPolynomial.notMem_support_iff.mp he, abs_zero]

@[simp] theorem coeffL1_monomial (e : Exponent) (c : ℚ) :
    coeffL1 (MvPolynomial.monomial e c) = |c| := by
  rw [coeffL1_eq_sum_of_support_subset _ {e} MvPolynomial.support_monomial_subset]
  simp

/-- Distinct monomials can be used for exact coefficient calculations. -/
theorem coeffL1_sum_monomials (s : Finset Exponent) (c : Exponent → ℚ) :
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

/-- Exact ℓ¹ calculation for a normalized finite sum of univariate powers. -/
theorem coeffL1_sum_powers (s : Finset ℕ) (c : ℕ → ℚ) :
    coeffL1 (∑ k ∈ s, MvPolynomial.C (c k) * MvPolynomial.X (0 : Fin 1) ^ k) =
      ∑ k ∈ s, |c k| := by
  let f : ℕ ↪ Exponent := ⟨fun k => Finsupp.single 0 k, by
    intro a b hab
    have h := congrArg (fun e : Exponent => e 0) hab
    simpa using h⟩
  have h := coeffL1_sum_monomials (s.map f) (fun e => c (e 0))
  simp only [Finset.sum_map] at h
  change coeffL1 (∑ k ∈ s, MvPolynomial.monomial (Finsupp.single (0 : Fin 1) k)
      (c ((Finsupp.single (0 : Fin 1) k) 0))) =
    ∑ k ∈ s, |c ((Finsupp.single (0 : Fin 1) k) 0)| at h
  simpa [MvPolynomial.monomial_eq] using h

/-- Repeated multiplication gives the input monomial, including degree zero. -/
def inputPow : ℕ → Syntax
  | 0 => .const 1
  | k + 1 => .mul (inputPow k) (.input 0)

@[simp] theorem inputPow_amp (k : ℕ) (r : ℚ) :
    (inputPow k).amp 1 r = 1 := by
  induction k <;> simp_all [inputPow, Expr.amp]

@[simp] theorem inputPow_lip (k : ℕ) (B r : ℚ) :
    (inputPow k).lip B r = 0 := by
  induction k <;> simp_all [inputPow, Expr.lip]

@[simp] theorem inputPow_toMvPolynomial (k : ℕ) :
    (inputPow k).toMvPolynomial = MvPolynomial.X (Sum.inl (0 : Fin 1)) ^ k := by
  induction k <;> simp_all [inputPow, Expr.toMvPolynomial, pow_succ]

def fromTerms (p : InputPoly) : List Exponent → Syntax
  | [] => .const 0
  | e :: es => .add (.mul (.const (p.coeff e)) (inputPow (e 0))) (fromTerms p es)

/-- Translate normalized polynomial coefficients, rather than its source syntax. -/
def canon (p : InputPoly) : Syntax := fromTerms p (p.support.sort degreeLE)

@[simp] theorem fromTerms_amp (p : InputPoly) (es : List Exponent) (r : ℚ) :
    (fromTerms p es).amp 1 r = (es.map (fun e => |p.coeff e|)).sum := by
  induction es <;> simp_all [fromTerms, Expr.amp]

@[simp] theorem fromTerms_lip (p : InputPoly) (es : List Exponent) (B r : ℚ) :
    (fromTerms p es).lip B r = 0 := by
  induction es <;> simp_all [fromTerms, Expr.lip]

@[simp] theorem canon_amp (p : InputPoly) (r : ℚ) :
    (canon p).amp 1 r = coeffL1 p := by
  simp [canon, coeffL1, sum_map_sort]

@[simp] theorem canon_lip (p : InputPoly) (B r : ℚ) :
    (canon p).lip B r = 0 := by
  simp [canon]

lemma exponent_single (e : Exponent) : e = Finsupp.single 0 (e 0) := by
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

lemma monomial_eq_inputPow (e : Exponent) (c : ℚ) :
    MvPolynomial.monomial e c =
      MvPolynomial.C c * (MvPolynomial.X (0 : Fin 1)) ^ (e 0) := by
  conv_lhs => rw [exponent_single e]
  simp [MvPolynomial.monomial_eq]

@[simp] theorem fromTerms_toMvPolynomial (p : InputPoly) (es : List Exponent) :
    (fromTerms p es).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
        ((es.map (fun e => MvPolynomial.monomial e (p.coeff e))).sum) := by
  induction es <;> simp_all [fromTerms, Expr.toMvPolynomial, monomial_eq_inputPow]

@[simp] theorem canon_toMvPolynomial (p : InputPoly) :
    (canon p).toMvPolynomial =
      MvPolynomial.rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1) p := by
  simp [canon, sum_map_sort, MvPolynomial.support_sum_monomial_coeff]

@[simp] theorem canon_eval (p : InputPoly) (u x : Fin 1 → ℝ) :
    (canon p).eval u x = GenericHolomorphicPole.realEval p (u 0) := by
  rw [← Expr.eval_toMvPolynomial, canon_toMvPolynomial, MvPolynomial.eval₂Hom_rename]
  have hu : Sum.elim u x ∘ Sum.inl = fun _ : Fin 1 => u 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hu]
  rfl

@[simp] theorem canon_evalComplex (p : InputPoly) (u x : Fin 1 → ℂ) :
    (canon p).evalComplex u x = GenericHolomorphicPole.complexEval p (u 0) := by
  rw [← Expr.evalComplex_toMvPolynomial, canon_toMvPolynomial,
    MvPolynomial.eval₂Hom_rename]
  have hu : Sum.elim u x ∘ Sum.inl = fun _ : Fin 1 => u 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hu]
  rfl

theorem coeffL1_nonneg (p : InputPoly) : 0 ≤ coeffL1 p := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem realEval_abs_le_coeffL1 (p : InputPoly) (u : ℝ) (hu : |u| ≤ 1) :
    |GenericHolomorphicPole.realEval p u| ≤ (coeffL1 p : ℝ) := by
  have h := (canon p).eval_abs_le_amp (B := 1) (r := 0)
    (by norm_num) (by norm_num) (u := fun _ => u) (x := fun _ => 0)
    (fun _ => by simpa using hu) (fun _ => by simp)
  simpa using h

theorem complexEval_norm_le_coeffL1 (p : InputPoly) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖GenericHolomorphicPole.complexEval p z‖ ≤ (coeffL1 p : ℝ) := by
  have h := (canon p).evalComplex_norm_le_amp (B := 1) (r := 0)
    (by norm_num) (by norm_num) (u := fun _ => z) (x := fun _ => 0)
    (fun _ => by simpa using hz) (fun _ => by simp)
  simpa using h

end CanonicalInputExpr
