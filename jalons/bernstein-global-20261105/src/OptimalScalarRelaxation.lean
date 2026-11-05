import Mathlib

/-! Classical optimal scalar relaxation on a positive interval.
No claim of a new optimization method. -/
namespace OptimalScalarRelaxation

theorem positive_parameters (l H : ℝ) (hl : 0 < l) (hH : l ≤ H) :
    0 < 2/(l+H) ∧ 0 ≤ (H-l)/(l+H) ∧ (H-l)/(l+H) < 1 := by
  have hd : 0 < l+H := by linarith
  exact ⟨div_pos (by norm_num) hd,
    div_nonneg (sub_nonneg.mpr hH) hd.le,
    (div_lt_one hd).mpr (by linarith)⟩

theorem uniform_bound (l H s : ℝ) (hl : 0 < l) (hH : l ≤ H)
    (hsl : l ≤ s) (hsH : s ≤ H) :
    |1-(2/(l+H))*s| ≤ (H-l)/(l+H) := by
  have hd : 0 < l+H := by linarith
  have heq : 1-(2/(l+H))*s = (l+H-2*s)/(l+H) := by
    field_simp <;> ring
  rw [heq, abs_div, abs_of_pos hd]
  apply (div_le_div_iff_of_pos_right hd).2
  apply abs_le.mpr
  constructor <;> linarith

/-- No other scalar relaxation parameter can improve the certified worst
endpoint bound, when both endpoints are part of the coefficient data. -/
theorem lower_bound (l H η K : ℝ) (hl : 0 < l) (hH : l ≤ H)
    (hlo : |1-η*l| ≤ K) (hhi : |1-η*H| ≤ K) :
    (H-l)/(l+H) ≤ K := by
  have hd : 0 < l+H := by linarith
  apply (div_le_iff₀ hd).2
  have hlo' := (abs_le.mp hlo).2
  have hhi' := (abs_le.mp hhi).1
  calc
    H-l = H*(1-η*l)-l*(1-η*H) := by ring
    _ ≤ H*K-l*(-K) := sub_le_sub
      (mul_le_mul_of_nonneg_left hlo' (by linarith))
      (mul_le_mul_of_nonneg_left hhi' hl.le)
    _ = K*(l+H) := by ring

theorem invariant_radius_identity (l H : ℝ) (hl : 0 < l) (hH : l ≤ H) :
    2/(l+H) + ((H-l)/(l+H))*(1/l) = 1/l := by
  have hd : l+H ≠ 0 := ne_of_gt (by linarith)
  have hl0 : l ≠ 0 := ne_of_gt hl
  field_simp
  ring

theorem degree_five_best_bound (η K : ℝ)
    (hmin : |1-η*(1/5)| ≤ K) (hmax : |1-η*5| ≤ K) : 12/13 ≤ K := by
  have h := lower_bound (1/5) 5 η K (by norm_num) (by norm_num) hmin hmax
  norm_num at h
  exact h

end OptimalScalarRelaxation
