import Mathlib

namespace ReciprocalVariation

/-- A global rational Lipschitz bound for the reciprocal quadratic target.
The constant is deliberately convenient rather than optimal. -/
theorem target_lipschitz (u v : ℝ) :
    |1 / (1 + 4 * u ^ 2) - 1 / (1 + 4 * v ^ 2)| ≤ 2 * |u - v| := by
  have hu : 0 < 1 + 4 * u ^ 2 := by positivity
  have hv : 0 < 1 + 4 * v ^ 2 := by positivity
  have hua : 4 * |u| ≤ 1 + 4 * u ^ 2 := by
    nlinarith [sq_nonneg (2 * |u| - 1), sq_abs u]
  have hva : 4 * |v| ≤ 1 + 4 * v ^ 2 := by
    nlinarith [sq_nonneg (2 * |v| - 1), sq_abs v]
  have hprod : (1 + 4 * u ^ 2) + (1 + 4 * v ^ 2) ≤
      2 * ((1 + 4 * u ^ 2) * (1 + 4 * v ^ 2)) := by
    nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  have hsum : 2 * |u + v| ≤ (1 + 4 * u ^ 2) * (1 + 4 * v ^ 2) := by
    nlinarith [abs_add_le u v]
  have hid : 1 / (1 + 4 * u ^ 2) - 1 / (1 + 4 * v ^ 2) =
      -4 * (u - v) * (u + v) / ((1 + 4 * u ^ 2) * (1 + 4 * v ^ 2)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_mul, abs_mul, abs_of_pos (mul_pos hu hv)]
  norm_num
  apply (div_le_iff₀ (mul_pos hu hv)).mpr
  have h := mul_le_mul_of_nonneg_left hsum (abs_nonneg (u - v))
  nlinarith

end ReciprocalVariation

#print axioms ReciprocalVariation.target_lipschitz
