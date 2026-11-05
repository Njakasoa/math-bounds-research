import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Exact rational polynomial certificates, with the sum of absolute values of
collected coefficients. This is not a statement about an expression-tree norm. -/
noncomputable section
namespace TwoCellPolynomial
open Polynomial

def Sminus : ℚ[X] := C 2 - C 2 * X + X^2
def Splus : ℚ[X] := C 2 + C 2 * X + X^2
def Tminus : ℚ[X] := C (1/2) + C (1/2) * X + C (1/4) * X^2
def Tplus : ℚ[X] := C (1/2) - C (1/2) * X + C (1/4) * X^2
def q : ℚ[X] := monomial 4 (-1/4)
def coefficientMass (p : ℚ[X]) : ℚ := p.sum (fun _ a => |a|)

theorem minus_product : Sminus * Tminus = 1 + C (1/4) * X^4 := by
  apply Polynomial.funext
  intro x
  simp [Sminus, Tminus]
  ring

theorem plus_product : Splus * Tplus = 1 + C (1/4) * X^4 := by
  apply Polynomial.funext
  intro x
  simp [Splus, Tplus]
  ring

theorem q_formula : q = -(C (1/4) * X^4) := by
  apply Polynomial.funext
  intro x
  simp [q]
  ring

theorem minus_residual : 1 - Sminus*Tminus = q := by
  rw [minus_product, q_formula]
  ring

theorem plus_residual : 1 - Splus*Tplus = q := by
  rw [plus_product, q_formula]
  ring

theorem coefficientMass_q : coefficientMass q = 1/4 := by
  unfold coefficientMass q
  rw [sum_monomial_index]
  · norm_num
  · simp

theorem contraction_rate : 0 ≤ coefficientMass q ∧ coefficientMass q < 1 := by
  rw [coefficientMass_q]
  norm_num

theorem certified_radius : (1:ℚ) + coefficientMass q * (4/3) = 4/3 := by
  rw [coefficientMass_q]
  norm_num

end TwoCellPolynomial
