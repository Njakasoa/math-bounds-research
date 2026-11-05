import Mathlib

namespace GlobalScalarMap

def step (η b x : ℝ) : ℝ := η + b * x

noncomputable def fixedState (η b : ℝ) : ℝ := η / (1 - b)

theorem contraction {η b κ x y : ℝ} (hb : |b| ≤ κ) :
    |step η b x - step η b y| ≤ κ * |x - y| := by
  have he : step η b x - step η b y = b * (x - y) := by unfold step; ring
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

theorem preserves_box {η b κ r x : ℝ} (hk : 0 ≤ κ) (hb : |b| ≤ κ)
    (hbudget : |η| + κ * r ≤ r) (hx : |x| ≤ r) : |step η b x| ≤ r := by
  calc
    |step η b x| ≤ |η| + |b * x| := abs_add_le _ _
    _ = |η| + |b| * |x| := by rw [abs_mul]
    _ ≤ |η| + κ * |x| := by gcongr
    _ ≤ |η| + κ * r := by gcongr
    _ ≤ r := hbudget

theorem coefficient_lt_one {b κ : ℝ} (hb : |b| ≤ κ) (hk : κ < 1) : b < 1 :=
  lt_of_le_of_lt (le_trans (le_abs_self b) hb) hk

theorem denominator_pos {b κ : ℝ} (hb : |b| ≤ κ) (hk : κ < 1) : 0 < 1 - b :=
  sub_pos.mpr (coefficient_lt_one hb hk)

theorem fixedState_fixed {η b κ : ℝ} (hb : |b| ≤ κ) (hk : κ < 1) :
    step η b (fixedState η b) = fixedState η b := by
  have hd := ne_of_gt (denominator_pos hb hk)
  unfold step fixedState
  field_simp
  <;> ring

theorem fixedState_unique {η b κ x : ℝ} (hb : |b| ≤ κ) (hk : κ < 1)
    (hx : step η b x = x) : x = fixedState η b := by
  have hd := ne_of_gt (denominator_pos hb hk)
  unfold fixedState
  apply (eq_div_iff hd).mpr
  unfold step at hx
  nlinarith

theorem fixedState_in_box {η b κ r : ℝ} (hb : |b| ≤ κ) (hk : κ < 1)
    (hr : 0 ≤ r) (hbudget : |η| + κ * r ≤ r) : |fixedState η b| ≤ r := by
  have hd := denominator_pos hb hk
  unfold fixedState
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hbr : b * r ≤ κ * r := mul_le_mul_of_nonneg_right (le_trans (le_abs_self b) hb) hr
  nlinarith

/-- A uniform parameter family: all conclusions hold for each allowed parameter. -/
theorem family_contraction {T : Type*} (b : T → ℝ) (D : Set T) {η κ : ℝ}
    (hb : ∀ t ∈ D, |b t| ≤ κ) {t : T} (ht : t ∈ D) (x y : ℝ) :
    |step η (b t) x - step η (b t) y| ≤ κ * |x - y| :=
  contraction (hb t ht)

theorem reciprocal_positive {η b S κ : ℝ} (hη : 0 < η)
    (hid : b = 1 - η * S) (hb : |b| ≤ κ) (hk : κ < 1) : 0 < S := by
  have h := coefficient_lt_one hb hk
  nlinarith

theorem fixedState_solves {η b S κ : ℝ} (hη : 0 < η)
    (hid : b = 1 - η * S) (hb : |b| ≤ κ) (hk : κ < 1) :
    S * fixedState η b = 1 := by
  have hs := ne_of_gt (reciprocal_positive hη hid hb hk)
  have he := ne_of_gt hη
  unfold fixedState
  rw [hid]
  field_simp
  <;> ring

theorem fixedState_reciprocal {η b S κ : ℝ} (hη : 0 < η)
    (hid : b = 1 - η * S) (hb : |b| ≤ κ) (hk : κ < 1) :
    fixedState η b = 1 / S := by
  have hs := ne_of_gt (reciprocal_positive hη hid hb hk)
  apply (eq_div_iff hs).mpr
  simpa [mul_comm] using fixedState_solves hη hid hb hk

theorem readout_ratio {η b S κ R : ℝ} (hη : 0 < η)
    (hid : b = 1 - η * S) (hb : |b| ≤ κ) (hk : κ < 1) :
    R * fixedState η b = R / S := by
  rw [fixedState_reciprocal hη hid hb hk]
  ring

/-- Two trajectories with the same possibly switching coefficient sequence contract.
This does not claim tracking of a time-varying fixed state. -/
theorem switched_contraction {η κ : ℝ} (hk : 0 ≤ κ)
    (b x y : ℕ → ℝ) (hb : ∀ n, |b n| ≤ κ)
    (hx : ∀ n, x (n + 1) = step η (b n) (x n))
    (hy : ∀ n, y (n + 1) = step η (b n) (y n)) (n : ℕ) :
    |x n - y n| ≤ κ ^ n * |x 0 - y 0| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hx n, hy n]
    calc
      |step η (b n) (x n) - step η (b n) (y n)| ≤ κ * |x n - y n| :=
        contraction (hb n)
      _ ≤ κ * (κ ^ n * |x 0 - y 0|) := mul_le_mul_of_nonneg_left ih hk
      _ = κ ^ (n + 1) * |x 0 - y 0| := by rw [pow_succ]; ring

theorem switched_box {η κ r : ℝ} (hk : 0 ≤ κ)
    (hbudget : |η| + κ * r ≤ r) (b x : ℕ → ℝ)
    (hb : ∀ n, |b n| ≤ κ) (hx : ∀ n, x (n + 1) = step η (b n) (x n))
    (hzero : |x 0| ≤ r) (n : ℕ) : |x n| ≤ r := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    rw [hx n]
    exact preserves_box hk (hb n) hbudget ih

/-- Unique fixed state in the box, with uniqueness even among all real states. -/
theorem exists_unique_fixed {η b κ r : ℝ} (hb : |b| ≤ κ) (hk : κ < 1)
    (hr : 0 ≤ r) (hbudget : |η| + κ * r ≤ r) :
    ∃ x : ℝ, |x| ≤ r ∧ step η b x = x ∧ ∀ y, step η b y = y → y = x := by
  refine ⟨fixedState η b, fixedState_in_box hb hk hr hbudget,
    fixedState_fixed hb hk, ?_⟩
  intro y hy
  exact fixedState_unique hb hk hy

end GlobalScalarMap
