import MultivariateInputExpr
import ComplexCheckedFixedPoint

/-!
Finite rational coefficient witnesses for a multivariable polynomial family.
The witness is an explicit hypothesis, not inferred from absence of common zeros.
One common scalar state supplies all polynomial outputs. Real and complex
stationary existence and uniqueness are consequences of the same checker.
-/
namespace MultivariateBezoutRealization
open MultivariateInputExpr BoxPolynomialBounds
open scoped BigOperators
variable {m k : ℕ}

noncomputable def residual (S T : Fin k → InputPoly m) : InputPoly m :=
  1 - ∑ i, S i * T i
noncomputable def rate (S T : Fin k → InputPoly m) : ℚ := coeffL1 (residual S T)
noncomputable def radius (S T : Fin k → InputPoly m) : ℚ := 1 / (1 - rate S T)
noncomputable def stateMap (S T : Fin k → InputPoly m) : Fin 1 → Expr m 1 :=
  fun _ => .add (.const 1) (.mul (canon (residual S T)) (.state 0))
noncomputable def outputSyntax (T : Fin k → InputPoly m) (i : Fin k) : Expr m 1 :=
  .mul (canon (T i)) (.state 0)

lemma rate_nonneg (S T : Fin k → InputPoly m) : 0 ≤ rate S T := coeffL1_nonneg _
lemma radius_pos (S T : Fin k → InputPoly m) (hK : rate S T < 1) :
    0 < radius S T := div_pos (by norm_num) (sub_pos.mpr hK)
lemma radius_identity (S T : Fin k → InputPoly m) (hK : rate S T < 1) :
    1 + rate S T * radius S T = radius S T := by
  have hd : 1 - rate S T ≠ 0 := by linarith
  dsimp [radius]
  field_simp
  ring

/-- Normalize the residual before constructing its AST, to retain cancellation. -/
theorem stateMap_checked (S T : Fin k → InputPoly m) (hK : rate S T < 1) :
    BoxContractionChecker.check (stateMap S T) 1 (radius S T) (rate S T) = true := by
  rw [BoxContractionChecker.check_iff]
  refine ⟨by norm_num, (radius_pos S T hK).le, rate_nonneg S T, hK, ?_⟩
  intro i
  constructor
  · simpa [stateMap, Expr.amp, rate] using le_of_eq (radius_identity S T hK)
  · simp [stateMap, Expr.lip, rate]

@[simp] lemma residual_realEval (S T : Fin k → InputPoly m) (u : Fin m → ℝ) :
    realEval (residual S T) u = 1 - ∑ i, realEval (S i) u * realEval (T i) u := by
  simp [residual, realEval]
@[simp] lemma residual_complexEval (S T : Fin k → InputPoly m) (z : Fin m → ℂ) :
    complexEval (residual S T) z = 1 - ∑ i, complexEval (S i) z * complexEval (T i) z := by
  simp [residual, complexEval]

@[simp] lemma output_eval (T : Fin k → InputPoly m) (i : Fin k)
    (u : Fin m → ℝ) (x : Fin 1 → ℝ) :
    (outputSyntax T i).eval u x = realEval (T i) u * x 0 := by
  simp [outputSyntax, Expr.eval]
@[simp] lemma output_evalComplex (T : Fin k → InputPoly m) (i : Fin k)
    (z : Fin m → ℂ) (x : Fin 1 → ℂ) :
    (outputSyntax T i).evalComplex z x = complexEval (T i) z * x 0 := by
  simp [outputSyntax, Expr.evalComplex]

/-- Exact polynomial identity before any evaluation or fixed-point argument. -/
theorem output_polynomial_identity (S T : Fin k → InputPoly m) :
    (∑ i, MvPolynomial.rename (Sum.inl : Fin m → Fin m ⊕ Fin 1) (S i) *
      (outputSyntax T i).toMvPolynomial) - 1 =
    MvPolynomial.X (Sum.inr (0 : Fin 1)) - (stateMap S T 0).toMvPolynomial := by
  simp only [outputSyntax, stateMap, Expr.toMvPolynomial, canon_toMvPolynomial,
    residual, map_sub, map_one, map_sum, map_mul, ← mul_assoc, ← Finset.sum_mul]
  ring

/-- Pure algebra at any real fixed point, with no nonzero denominator assumption. -/
theorem stationary_bezout (S T : Fin k → InputPoly m)
    (u : Fin m → ℝ) (x : Fin 1 → ℝ)
    (hfix : BoxContractionChecker.map (stateMap S T) u x = x) :
    ∑ i, realEval (S i) u * (outputSyntax T i).eval u x = 1 := by
  have h := congrFun hfix 0
  simp only [BoxContractionChecker.map, stateMap, Expr.eval, canon_eval,
    Rat.cast_one, residual_realEval] at h
  simp only [output_eval, ← mul_assoc, ← Finset.sum_mul]
  nlinarith [h]

/-- The same algebraic output identity holds at the complex fixed point. -/
theorem stationary_complex_bezout (S T : Fin k → InputPoly m)
    (z : Fin m → ℂ) (x : Fin 1 → ℂ)
    (hfix : ComplexCheckedFixedPoint.map (stateMap S T) z x = x) :
    ∑ i, complexEval (S i) z * (outputSyntax T i).evalComplex z x = 1 := by
  have h := congrFun hfix 0
  simp only [ComplexCheckedFixedPoint.map, stateMap, Expr.evalComplex, canon_evalComplex,
    Rat.cast_one, residual_complexEval] at h
  simp only [output_evalComplex, ← mul_assoc, ← Finset.sum_mul]
  linear_combination -h

/-- Non-vacuous real existence, uniqueness in the box, and all output equations.
Every output uses the very same fixed point; no branch existence is postulated. -/
theorem exists_realization (S T : Fin k → InputPoly m) (hK : rate S T < 1) :
    BoxContractionChecker.check (stateMap S T) 1 (radius S T) (rate S T) = true ∧
    ∀ u ∈ BoxContractionChecker.boxSet m 1, ∃! x : Fin 1 → ℝ,
      x ∈ BoxContractionChecker.boxSet 1 (radius S T) ∧
      BoxContractionChecker.map (stateMap S T) u x = x ∧
      ∑ i, realEval (S i) u * (outputSyntax T i).eval u x = 1 := by
  have hc := stateMap_checked S T hK
  refine ⟨hc, ?_⟩
  intro u hu
  obtain ⟨x, hx, huniq⟩ := BoxContractionChecker.checked_uniform_existsUnique_mem
    (stateMap S T) hc u hu
  have hfix : BoxContractionChecker.map (stateMap S T) u x = x := by
    exact (sub_eq_zero.mp hx.2).symm
  refine ⟨x, ⟨hx.1,hfix,stationary_bezout S T u x hfix⟩, ?_⟩
  intro y hy
  apply huniq y
  exact ⟨hy.1, by simpa only [BoxContractionChecker.field, sub_eq_zero] using hy.2.1.symm⟩

/-- A stronger complex statement throughout the closed unit polydisc. -/
theorem exists_complex_realization (S T : Fin k → InputPoly m) (hK : rate S T < 1) :
    ∀ z ∈ ComplexCheckedFixedPoint.boxSet m 1, ∃! x : Fin 1 → ℂ,
      x ∈ ComplexCheckedFixedPoint.boxSet 1 (radius S T) ∧
      ComplexCheckedFixedPoint.map (stateMap S T) z x = x ∧
      ∑ i, complexEval (S i) z * (outputSyntax T i).evalComplex z x = 1 := by
  intro z hz
  obtain ⟨x,hx,huniq⟩ := ComplexCheckedFixedPoint.checked_uniform_existsUnique_mem
    (stateMap S T) (stateMap_checked S T hK) z hz
  refine ⟨x, ⟨hx.1,hx.2,stationary_complex_bezout S T z x hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1,hy.2.1⟩

/-- The finite witness already excludes common zeros on the closed polydisc.
No multivariable identity theorem or Wiener-algebra converse is used. -/
theorem witness_no_common_zero (S T : Fin k → InputPoly m) (hK : rate S T < 1)
    (z : Fin m → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    ∃ i, complexEval (S i) z ≠ 0 := by
  by_contra hn
  push Not at hn
  have hbound := complexEval_norm_le_coeffL1 (residual S T) z hz
  rw [residual_complexEval] at hbound
  have hKr : (rate S T : ℝ) < 1 := by exact_mod_cast hK
  change ‖1 - ∑ i, complexEval (S i) z * complexEval (T i) z‖ ≤ (rate S T : ℝ) at hbound
  simp [hn] at hbound
  linarith

/-- A common complex zero is a rejection certificate for every rational family T. -/
theorem no_witness_of_common_zero (S : Fin k → InputPoly m)
    (z : Fin m → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hzero : ∀ i, complexEval (S i) z = 0) :
    ¬ ∃ T : Fin k → InputPoly m, rate S T < 1 := by
  rintro ⟨T,hT⟩
  obtain ⟨i,hi⟩ := witness_no_common_zero S T hT z hz
  exact hi (hzero i)

/-- The empty family cannot meet the witness inequality, for any input dimension. -/
theorem no_empty_witness (S T : Fin 0 → InputPoly m) : ¬ rate S T < 1 := by
  intro h
  obtain ⟨i,_⟩ := witness_no_common_zero S T h (fun _ => 0) (by simp)
  exact Fin.elim0 i

end MultivariateBezoutRealization
