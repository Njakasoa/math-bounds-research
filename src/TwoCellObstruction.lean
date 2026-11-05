import MultivariateBezoutRealization

/-! Obstruction only to full-unit-box coefficient certificates of the archived
Bézout form. This is not an impossibility theorem for general dynamical systems. -/
noncomputable section
namespace TwoCellObstruction
open MultivariateInputExpr MultivariateBezoutRealization

def originalFamily : Fin 1 → InputPoly 1 :=
  fun _ => 1 + MvPolynomial.C 4 * MvPolynomial.X 0 ^ 2

def complexRoot : Fin 1 → ℂ := fun _ => Complex.I / 2

theorem root_in_unit_polydisc : ∀ j, ‖complexRoot j‖ ≤ 1 := by
  intro j
  norm_num [complexRoot, norm_div]

theorem common_zero : ∀ i, complexEval (originalFamily i) complexRoot = 0 := by
  intro i
  simp [originalFamily, complexEval, complexRoot, div_pow, Complex.I_sq]
  norm_num

/-- No polynomial multiplier, of any degree, gives a strict coefficient ℓ¹
certificate on the original full unit box for the denominator 1+4u². -/
theorem no_full_box_witness :
    ¬ ∃ T : Fin 1 → InputPoly 1, rate originalFamily T < 1 :=
  no_witness_of_common_zero originalFamily complexRoot root_in_unit_polydisc common_zero

theorem no_full_box_multiplier (T : Fin 1 → InputPoly 1) :
    ¬ rate originalFamily T < 1 := by
  intro h
  exact no_full_box_witness ⟨T, h⟩

/-- Equivalent single-polynomial formulation, without family notation. -/
theorem no_scalar_multiplier (T : InputPoly 1) :
    ¬ coeffL1 (1 - (1 + MvPolynomial.C 4 * MvPolynomial.X 0 ^ 2) * T) < 1 := by
  have h := no_full_box_multiplier (fun _ => T)
  simpa [rate, MultivariateBezoutRealization.residual, originalFamily, Fin.sum_univ_one] using h

end TwoCellObstruction
