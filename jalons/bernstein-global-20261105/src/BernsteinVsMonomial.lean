import BoxContractionChecker

/-! The original absolute syntax checker rejects this same normalized update
in its original input coordinate u∈[-1,1]. This is a statement about this
explicit encoding, not a new impossibility theorem for all realizations. -/
namespace BernsteinVsMonomial
open BoxPolynomialBounds

def inputSquare : Expr 1 1 := .mul (.input 0) (.input 0)

def slope : Expr 1 1 := .add (.const (8/13)) (.mul (.const (-20/13)) inputSquare)

def update : Fin 1 → Expr 1 1 := fun _ =>
  .add (.const (5/13)) (.mul slope (.state 0))

theorem slope_amplitude (r : ℚ) : slope.amp 1 r = 28/13 := by
  norm_num [slope, inputSquare, Expr.amp]

theorem update_lipschitz (r : ℚ) : (update 0).lip 1 r = 28/13 := by
  norm_num [update, slope, inputSquare, Expr.amp, Expr.lip]

theorem original_checker_rejects (r K : ℚ) :
    BoxContractionChecker.check update 1 r K = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_,_,_,hK, hb⟩ := (BoxContractionChecker.check_iff update 1 r K).mp h
  have hbound := (hb 0).2
  rw [update_lipschitz] at hbound
  norm_num at hbound
  linarith

theorem update_eval (u x : Fin 1 → ℝ) :
    BoxContractionChecker.map update u x 0 =
      5/13 + (1-(5/13)*(1+4*(u 0)^2))*(x 0) := by
  simp only [BoxContractionChecker.map, update, slope, inputSquare, Expr.eval]
  norm_num <;> ring_nf <;> simp

end BernsteinVsMonomial
