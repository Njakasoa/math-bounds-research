import ReactionBindingEuler
import TrackingRecurrence

namespace ReactionBindingTracking
open ReactionBindingEuler

noncomputable def reference (v : ℝ) : ℝ := 1/(1+v)

/-- Input sensitivity on nonnegative dimensionless ligand concentrations. -/
theorem reference_lipschitz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |reference u - reference v| ≤ |u-v| := by
  have hdu : 0 < 1+u := by linarith
  have hdv : 0 < 1+v := by linarith
  have hd : 0 < (1+u)*(1+v) := mul_pos hdu hdv
  have hone : 1 ≤ (1+u)*(1+v) := by nlinarith [mul_nonneg hu hv]
  have hid : reference u-reference v = (v-u)/((1+u)*(1+v)) := by
    unfold reference
    field_simp [ne_of_gt hdu, ne_of_gt hdv]
    ring
  rw [hid, abs_div, abs_of_pos hd, abs_sub_comm v u]
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_nonneg (abs_nonneg (u-v)) (sub_nonneg.mpr hone)]

theorem safe_contraction {v : ℝ} (hv : v ∈ Set.Icc 0 3) (x y : ℝ) :
    |E (1/3) v x-E (1/3) v y| ≤ (2/3 : ℝ)*|x-y| := by
  have hs : |1-(1/3 : ℝ)*(1+v)| ≤ (2/3 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hv.1,hv.2]
  have hid : E (1/3) v x-E (1/3) v y =
      (1-(1/3 : ℝ)*(1+v))*(x-y) := by unfold E; ring
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

theorem reference_fixed {v : ℝ} (hv : 0 ≤ v) :
    E (1/3) v (reference v) = reference v := by
  have hd : 0 < 1+v := by linarith
  unfold E reference
  field_simp [ne_of_gt hd]
  ring

noncomputable def trajectory (v : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n+1 => E (1/3) (v n) (trajectory v x0 n)

theorem trajectory_physical (v : ℕ → ℝ) (hv : ∀ n, v n ∈ Set.Icc 0 3)
    (x0 : ℝ) (hx : x0 ∈ Set.Icc 0 1) (n : ℕ) :
    trajectory v x0 n ∈ Set.Icc 0 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact safe_invariant (v n) (hv n).1 (hv n).2
      (trajectory v x0 n) ih.1 ih.2

noncomputable def error (v : ℕ → ℝ) (x0 : ℝ) (n : ℕ) : ℝ :=
  |trajectory v x0 n-reference (v n)|

theorem one_step (v : ℕ → ℝ) (hv : ∀ n, v n ∈ Set.Icc 0 3)
    (x0 : ℝ) (n : ℕ) :
    error v x0 (n+1) ≤ (2/3 : ℝ)*error v x0 n+|v (n+1)-v n| := by
  have hs := TrackingRecurrence.tracking_step
    (fun n => E (1/3) (v n)) (trajectory v x0) (fun n => reference (v n))
    (fun n => safe_contraction (hv n)) (fun n => reference_fixed (hv n).1)
    (fun n => rfl) n
  exact hs.trans (add_le_add (le_refl _) (reference_lipschitz (hv (n+1)).1 (hv n).1))

theorem tracking_bound (v : ℕ → ℝ) (hv : ∀ n, v n ∈ Set.Icc 0 3)
    (x0 δ : ℝ) (hδ : ∀ n, |v (n+1)-v n| ≤ δ) (n : ℕ) :
    error v x0 n ≤ (2/3 : ℝ)^n*error v x0 0+3*δ*(1-(2/3 : ℝ)^n) := by
  have hs : ∀ j, error v x0 (j+1) ≤ (2/3 : ℝ)*error v x0 j+δ := by
    intro j
    exact (one_step v hv x0 j).trans (add_le_add (le_refl _) (hδ j))
  have hb := TrackingRecurrence.recurrence_bounded_drift_closed
    (by norm_num : (0 : ℝ) ≤ 2/3) (by norm_num : (2/3 : ℝ) < 1)
    (error v x0) hs n
  convert hb using 1 <;> ring

#print axioms reference_lipschitz
#print axioms tracking_bound
end ReactionBindingTracking
