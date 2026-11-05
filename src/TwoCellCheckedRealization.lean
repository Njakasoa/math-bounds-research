import TwoCellExample
import TwoCellCheckerBridge

/-! The exact scalar output uses the very vector state supplied by the archived
checker's soundness theorem. No independent fixed-state witness is substituted. -/
noncomputable section
namespace TwoCellCheckedRealization
open BoxPolynomialBounds

def inputVector (v : ℝ) : Fin 1 → ℝ := fun _ => v

def outputSyntax (s : ℚ) : Expr 1 1 :=
  .mul
    (.add (.add (.const (1/2)) (.mul (.const (-s/2)) (.input 0)))
      (.mul (.const (1/4)) (.mul (.input 0) (.input 0))))
    (.state 0)

theorem outputSyntax_eval (s : ℚ) (v : ℝ) (x : Fin 1 → ℝ) :
    (outputSyntax s).eval (inputVector v) x = TwoCell.output (s : ℝ) v (x 0) := by
  simp only [outputSyntax, Expr.eval, inputVector, TwoCell.output, TwoCell.multiplier]
  push_cast
  ring

theorem scalar_fixed_of_checker_fixed (v : ℝ) (x : Fin 1 → ℝ)
    (hx : BoxContractionChecker.map TwoCellCheckerBridge.stateMap (inputVector v) x = x) :
    TwoCell.stateMap v (x 0) = x 0 := by
  have h := congrFun hx 0
  rw [TwoCellCheckerBridge.eval_formula] at h
  dsimp [inputVector] at h
  unfold TwoCell.stateMap TwoCell.residual
  linarith

/-- Local uniqueness and output identity for the checker's own stationary vector. -/
theorem checked_local_realization (s v : ℝ) (hs : s^2 = 1) (hv : |v| ≤ 1) :
    ∃! x : Fin 1 → ℝ,
      x ∈ BoxContractionChecker.boxSet 1 (4/3) ∧
      BoxContractionChecker.map TwoCellCheckerBridge.stateMap (inputVector v) x = x ∧
      TwoCell.output s v (x 0) = 1 / TwoCell.denominator (TwoCell.chart s v) := by
  have hvin : inputVector v ∈ BoxContractionChecker.boxSet 1 1 := by
    apply (BoxContractionChecker.mem_boxSet_iff (by norm_num) _).2
    intro i
    simpa [inputVector] using hv
  obtain ⟨x, hx, huniq⟩ := TwoCellCheckerBridge.checked_unique_stationary (inputVector v) hvin
  have hfix : BoxContractionChecker.map TwoCellCheckerBridge.stateMap (inputVector v) x = x :=
    (sub_eq_zero.mp hx.2).symm
  refine ⟨x, ⟨hx.1, hfix, ?_⟩, ?_⟩
  · exact TwoCell.output_correct s v (x 0) hs (scalar_fixed_of_checker_fixed v x hfix)
  · intro y hy
    apply huniq y
    exact ⟨hy.1, by simpa only [BoxContractionChecker.field, sub_eq_zero] using hy.2.1.symm⟩

/-- Checker acceptance and realization on the entire original interval. -/
theorem checked_full_interval_realization :
    BoxContractionChecker.check TwoCellCheckerBridge.stateMap 1 (4/3) (1/4) = true ∧
    ∀ u : ℝ, |u| ≤ 1 → ∃ s v : ℝ,
      (s = -1 ∨ s = 1) ∧ |v| ≤ 1 ∧ TwoCell.chart s v = u ∧
      ∃! x : Fin 1 → ℝ,
        x ∈ BoxContractionChecker.boxSet 1 (4/3) ∧
        BoxContractionChecker.map TwoCellCheckerBridge.stateMap (inputVector v) x = x ∧
        TwoCell.output s v (x 0) = 1 / TwoCell.denominator u := by
  refine ⟨TwoCellCheckerBridge.checker_accepts, ?_⟩
  intro u hu
  obtain ⟨s, v, hs, hv, hc⟩ := TwoCell.chart_coverage u hu
  have hs2 : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨s, v, hs, hv, hc, ?_⟩
  simpa only [hc] using checked_local_realization s v hs2 hv

/-- The polynomial AST output agrees with the exact scalar target at any
checker fixed point, with rational chart sign s satisfying s²=1. -/
theorem checked_syntax_output (s : ℚ) (v : ℝ) (x : Fin 1 → ℝ)
    (hs : s^2 = 1)
    (hx : BoxContractionChecker.map TwoCellCheckerBridge.stateMap (inputVector v) x = x) :
    (outputSyntax s).eval (inputVector v) x =
      1 / TwoCell.denominator (TwoCell.chart (s : ℝ) v) := by
  rw [outputSyntax_eval]
  apply TwoCell.output_correct
  · exact_mod_cast hs
  · exact scalar_fixed_of_checker_fixed v x hx

end TwoCellCheckedRealization
