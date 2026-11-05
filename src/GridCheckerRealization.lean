import LocalAtlasRational
import MultivariateBezoutRealization

/-! A local strict coefficient certificate produces actual accepted checker
states and all polynomial Bézout outputs, with one shared state vector. -/
noncomputable section
open scoped BigOperators
namespace GridCheckerRealization
open MultivariateInputExpr MultivariateBezoutRealization
variable {m k : ℕ}

def localFamily (S : Fin k → InputPoly m) (c : Fin m → ℚ) (h : ℚ) :
    Fin k → InputPoly m := fun j => LocalAtlas.affineSubstitution (S j) c h

def constantWitness (i : Fin k) (t : ℚ) : Fin k → InputPoly m :=
  fun j => if j = i then MvPolynomial.C t else 0

theorem residual_eq (S : Fin k → InputPoly m) (c : Fin m → ℚ) (h : ℚ)
    (i : Fin k) (t : ℚ) :
    residual (localFamily S c h) (constantWitness i t) =
      1 - LocalAtlas.affineSubstitution (S i) c h * MvPolynomial.C t := by
  classical
  simp [MultivariateBezoutRealization.residual, localFamily, constantWitness, mul_ite]

theorem rate_lt_one (S : Fin k → InputPoly m) (c : Fin m → ℚ) (h : ℚ)
    (i : Fin k) (t : ℚ)
    (hcert : coeffL1 (1 - LocalAtlas.affineSubstitution (S i) c h * MvPolynomial.C t) < 1) :
    rate (localFamily S c h) (constantWitness i t) < 1 := by
  simpa only [rate, residual_eq] using hcert

/-- This is the archived realization theorem applied to the actual local
family and the sparse constant multiplier chosen by the grid certificate. -/
theorem checked_local_realization (S : Fin k → InputPoly m) (c : Fin m → ℚ) (h : ℚ)
    (i : Fin k) (t : ℚ)
    (hcert : coeffL1 (1 - LocalAtlas.affineSubstitution (S i) c h * MvPolynomial.C t) < 1) :
    BoxContractionChecker.check
      (stateMap (localFamily S c h) (constantWitness i t)) 1
      (radius (localFamily S c h) (constantWitness i t))
      (rate (localFamily S c h) (constantWitness i t)) = true ∧
    ∀ v ∈ BoxContractionChecker.boxSet m 1, ∃! x : Fin 1 → ℝ,
      x ∈ BoxContractionChecker.boxSet 1 (radius (localFamily S c h) (constantWitness i t)) ∧
      BoxContractionChecker.map (stateMap (localFamily S c h) (constantWitness i t)) v x = x ∧
      ∑ j, realEval (localFamily S c h j) v *
        (outputSyntax (constantWitness i t) j).eval v x = 1 := by
  exact exists_realization (localFamily S c h) (constantWitness i t)
    (rate_lt_one S c h i t hcert)

/-- Existential interface for use by a global finite-atlas theorem. -/
theorem exists_checked_witness (S : Fin k → InputPoly m) (c : Fin m → ℚ) (h : ℚ)
    (hcert : ∃ i : Fin k, ∃ t : ℚ,
      coeffL1 (1 - LocalAtlas.affineSubstitution (S i) c h * MvPolynomial.C t) < 1) :
    ∃ T : Fin k → InputPoly m,
      rate (localFamily S c h) T < 1 ∧
      BoxContractionChecker.check (stateMap (localFamily S c h) T) 1
        (radius (localFamily S c h) T) (rate (localFamily S c h) T) = true ∧
      ∀ v ∈ BoxContractionChecker.boxSet m 1, ∃! x : Fin 1 → ℝ,
        x ∈ BoxContractionChecker.boxSet 1 (radius (localFamily S c h) T) ∧
        BoxContractionChecker.map (stateMap (localFamily S c h) T) v x = x ∧
        ∑ j, realEval (localFamily S c h j) v * (outputSyntax T j).eval v x = 1 := by
  obtain ⟨i, t, ht⟩ := hcert
  exact ⟨constantWitness i t, rate_lt_one S c h i t ht,
    checked_local_realization S c h i t ht⟩

end GridCheckerRealization
