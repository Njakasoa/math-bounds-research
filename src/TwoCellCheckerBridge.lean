import BoxContractionChecker

/-! Executable acceptance of the normalized two-cell update, connected to
the archived checker's stationary existence theorem. -/
namespace TwoCellCheckerBridge
open BoxPolynomialBounds

def fourthPower : Expr 1 1 :=
  .mul (.mul (.input 0) (.input 0)) (.mul (.input 0) (.input 0))

def stateMap : Fin 1 → Expr 1 1 := fun _ =>
  .add (.const 1) (.mul (.mul (.const (-1/4)) fourthPower) (.state 0))

theorem checker_accepts :
    BoxContractionChecker.check stateMap 1 (4/3) (1/4) = true := by
  rw [BoxContractionChecker.check_iff]
  norm_num [BoxContractionChecker.Conditions, stateMap, fourthPower, Expr.amp, Expr.lip]

theorem amplitude : (stateMap 0).amp 1 (4/3) = 4/3 := by
  norm_num [stateMap, fourthPower, Expr.amp]

theorem lipschitz_bound : (stateMap 0).lip 1 (4/3) = 1/4 := by
  norm_num [stateMap, fourthPower, Expr.amp, Expr.lip]

theorem eval_formula (v x : Fin 1 → ℝ) :
    BoxContractionChecker.map stateMap v x 0 = 1 - v 0 ^ 4 / 4 * x 0 := by
  simp only [BoxContractionChecker.map, stateMap, fourthPower, Expr.eval]
  norm_num
  ring

theorem checked_unique_stationary (v : Fin 1 → ℝ)
    (hv : v ∈ BoxContractionChecker.boxSet 1 1) :
    ∃! x : Fin 1 → ℝ,
      x ∈ BoxContractionChecker.boxSet 1 (4/3) ∧
      BoxContractionChecker.field stateMap () v x = 0 :=
  BoxContractionChecker.checked_uniform_existsUnique_mem stateMap checker_accepts v hv

end TwoCellCheckerBridge
