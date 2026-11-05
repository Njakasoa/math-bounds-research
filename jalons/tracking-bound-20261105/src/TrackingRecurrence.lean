import GlobalScalarMap

/-!
# Classical tracking bounds for moving fixed states

The state is updated with the map at time `n`, whereas the tracking error at
`n + 1` is measured against the fixed state of the map at time `n + 1`.
The resulting fixed-state drift is retained explicitly. These are classical
contraction/recurrence estimates, with no novelty claim.
-/

namespace TrackingRecurrence

/-- The finite forcing convolution, with the most recent forcing weighted by one. -/
noncomputable def convolution (κ : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) * d j

@[simp] theorem convolution_zero (κ : ℝ) (d : ℕ → ℝ) :
    convolution κ d 0 = 0 := by simp [convolution]

/-- An algebraic identity, requiring no sign or contraction assumptions. -/
theorem convolution_succ (κ : ℝ) (d : ℕ → ℝ) (n : ℕ) :
    convolution κ d (n + 1) = κ * convolution κ d n + d n := by
  unfold convolution
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have he : n - j = (n - 1 - j) + 1 := by omega
  rw [he, pow_succ]
  ring

/-- Exact finite convolution estimate for a scalar one-step inequality.
Neither the error sequence nor the forcing needs a sign assumption. -/
theorem recurrence_convolution {κ : ℝ} (hk : 0 ≤ κ)
    (e d : ℕ → ℝ) (hstep : ∀ n, e (n + 1) ≤ κ * e n + d n) (n : ℕ) :
    e n ≤ κ ^ n * e 0 + convolution κ d n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      e (n + 1) ≤ κ * e n + d n := hstep n
      _ ≤ κ * (κ ^ n * e 0 + convolution κ d n) + d n := by
        exact add_le_add (mul_le_mul_of_nonneg_left ih hk) le_rfl
      _ = κ ^ (n + 1) * e 0 + convolution κ d (n + 1) := by
        rw [convolution_succ, pow_succ]
        ring

/-- The standard finite geometric sum identity, including κ = 1. -/
theorem geometric_sum_identity (κ : ℝ) (n : ℕ) :
    (1 - κ) * (∑ j ∈ Finset.range n, κ ^ j) = 1 - κ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- One-step geometric-sum recurrence. -/
theorem geometric_sum_succ (κ : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), κ ^ j) =
      κ * (∑ j ∈ Finset.range n, κ ^ j) + 1 := by
  rw [Finset.sum_range_succ]
  have h := geometric_sum_identity κ n
  linarith

/-- Closed form of the finite geometric sum, for κ < 1. -/
theorem geometric_sum_eq {κ : ℝ} (hk : κ < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, κ ^ j) = (1 - κ ^ n) / (1 - κ) := by
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr hk))).mpr
  simpa [mul_comm] using geometric_sum_identity κ n

/-- Uniform geometric-sum bound under the standard contraction assumptions. -/
theorem geometric_sum_le {κ : ℝ} (hk0 : 0 ≤ κ) (hk1 : κ < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, κ ^ j) ≤ 1 / (1 - κ) := by
  rw [geometric_sum_eq hk1]
  exact div_le_div_of_nonneg_right (by have := pow_nonneg hk0 n; linarith)
    (le_of_lt (sub_pos.mpr hk1))

/-- Finite bounded-forcing estimate. The power-sum form also covers κ = 1. -/
theorem recurrence_bounded_drift {κ δ : ℝ} (hk : 0 ≤ κ)
    (e : ℕ → ℝ) (hstep : ∀ n, e (n + 1) ≤ κ * e n + δ) (n : ℕ) :
    e n ≤ κ ^ n * e 0 + δ * (∑ j ∈ Finset.range n, κ ^ j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      e (n + 1) ≤ κ * e n + δ := hstep n
      _ ≤ κ * (κ ^ n * e 0 + δ * (∑ j ∈ Finset.range n, κ ^ j)) + δ := by
        exact add_le_add (mul_le_mul_of_nonneg_left ih hk) le_rfl
      _ = κ ^ (n + 1) * e 0 + δ * (∑ j ∈ Finset.range (n + 1), κ ^ j) := by
        rw [geometric_sum_succ, pow_succ]
        ring

/-- Closed-form bounded-forcing estimate, retaining the finite-horizon factor. -/
theorem recurrence_bounded_drift_closed {κ δ : ℝ} (hk0 : 0 ≤ κ) (hk1 : κ < 1)
    (e : ℕ → ℝ) (hstep : ∀ n, e (n + 1) ≤ κ * e n + δ) (n : ℕ) :
    e n ≤ κ ^ n * e 0 + δ * ((1 - κ ^ n) / (1 - κ)) := by
  simpa [geometric_sum_eq hk1] using recurrence_bounded_drift hk0 e hstep n

/-- Uniform forcing contribution. The initial transient is still present. -/
theorem recurrence_uniform {κ δ : ℝ} (hk0 : 0 ≤ κ) (hk1 : κ < 1) (hδ : 0 ≤ δ)
    (e : ℕ → ℝ) (hstep : ∀ n, e (n + 1) ≤ κ * e n + δ) (n : ℕ) :
    e n ≤ κ ^ n * e 0 + δ / (1 - κ) := by
  calc
    e n ≤ κ ^ n * e 0 + δ * (∑ j ∈ Finset.range n, κ ^ j) :=
      recurrence_bounded_drift hk0 e hstep n
    _ ≤ κ ^ n * e 0 + δ * (1 / (1 - κ)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (geometric_sum_le hk0 hk1 n) hδ)
    _ = κ ^ n * e 0 + δ / (1 - κ) := by ring

/-- Tracking recurrence for a sequence of maps and their instantaneous fixed states. -/
theorem tracking_step {κ : ℝ} (G : ℕ → ℝ → ℝ) (x p : ℕ → ℝ)
    (hcontract : ∀ n a b, |G n a - G n b| ≤ κ * |a - b|)
    (hfixed : ∀ n, G n (p n) = p n)
    (htrajectory : ∀ n, x (n + 1) = G n (x n)) (n : ℕ) :
    |x (n + 1) - p (n + 1)| ≤ κ * |x n - p n| + |p (n + 1) - p n| := by
  calc
    |x (n + 1) - p (n + 1)| ≤ |x (n + 1) - p n| + |p n - p (n + 1)| :=
      abs_sub_le _ _ _
    _ = |G n (x n) - G n (p n)| + |p (n + 1) - p n| := by
      rw [htrajectory n, hfixed n, abs_sub_comm (p n)]
    _ ≤ κ * |x n - p n| + |p (n + 1) - p n| :=
      add_le_add (hcontract n (x n) (p n)) le_rfl

/-- Exact finite tracking estimate with the actual fixed-state drift at each step. -/
theorem tracking_convolution {κ : ℝ} (hk : 0 ≤ κ)
    (G : ℕ → ℝ → ℝ) (x p : ℕ → ℝ)
    (hcontract : ∀ n a b, |G n a - G n b| ≤ κ * |a - b|)
    (hfixed : ∀ n, G n (p n) = p n)
    (htrajectory : ∀ n, x (n + 1) = G n (x n)) (n : ℕ) :
    |x n - p n| ≤ κ ^ n * |x 0 - p 0| +
      ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) * |p (j + 1) - p j| := by
  exact recurrence_convolution hk (fun n => |x n - p n|)
    (fun n => |p (n + 1) - p n|) (tracking_step G x p hcontract hfixed htrajectory) n

/-- Finite tracking bound when every instantaneous fixed-state drift is at most δ. -/
theorem tracking_bounded_drift {κ δ : ℝ} (hk : 0 ≤ κ)
    (G : ℕ → ℝ → ℝ) (x p : ℕ → ℝ)
    (hcontract : ∀ n a b, |G n a - G n b| ≤ κ * |a - b|)
    (hfixed : ∀ n, G n (p n) = p n)
    (htrajectory : ∀ n, x (n + 1) = G n (x n))
    (hdrift : ∀ n, |p (n + 1) - p n| ≤ δ) (n : ℕ) :
    |x n - p n| ≤ κ ^ n * |x 0 - p 0| + δ * (∑ j ∈ Finset.range n, κ ^ j) := by
  apply recurrence_bounded_drift hk (fun n => |x n - p n|) _ n
  intro j
  exact (tracking_step G x p hcontract hfixed htrajectory j).trans
    (add_le_add le_rfl (hdrift j))

/-- Uniform tracking bound. Nonnegative δ follows from the drift hypothesis. -/
theorem tracking_uniform {κ δ : ℝ} (hk0 : 0 ≤ κ) (hk1 : κ < 1)
    (G : ℕ → ℝ → ℝ) (x p : ℕ → ℝ)
    (hcontract : ∀ n a b, |G n a - G n b| ≤ κ * |a - b|)
    (hfixed : ∀ n, G n (p n) = p n)
    (htrajectory : ∀ n, x (n + 1) = G n (x n))
    (hdrift : ∀ n, |p (n + 1) - p n| ≤ δ) (n : ℕ) :
    |x n - p n| ≤ κ ^ n * |x 0 - p 0| + δ / (1 - κ) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hdrift 0)
  apply recurrence_uniform hk0 hk1 hδ (fun n => |x n - p n|) _ n
  intro j
  exact (tracking_step G x p hcontract hfixed htrajectory j).trans
    (add_le_add le_rfl (hdrift j))

#print axioms recurrence_convolution
#print axioms recurrence_bounded_drift
#print axioms recurrence_bounded_drift_closed
#print axioms recurrence_uniform
#print axioms tracking_step
#print axioms tracking_convolution
#print axioms tracking_bounded_drift
#print axioms tracking_uniform

end TrackingRecurrence
