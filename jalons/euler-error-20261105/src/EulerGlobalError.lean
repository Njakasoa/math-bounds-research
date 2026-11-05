import MassActionBinding
import ReactionBindingEuler
import TrackingRecurrence
import EulerLocalError

/-!
# Forward-Euler global error on a mesh-aligned piecewise constant input

At step `n`, both recurrences use the same input `v n`, held constant over
that entire mesh interval. The exact recurrence `Y` is the endpoint value
of the explicit constant-input solution `MassActionBinding.sample`.
The imported `sample_initial` and `sample_derivative` verify that solution
on each interval. No claim is made for an arbitrary continuously varying
forcing, for general reaction-network trajectory equivalence, or for
biological validation. The error bounds are classical and are not sharp.
-/

namespace EulerGlobalError

/-- Forward-Euler mesh trajectory. -/
noncomputable def X (τ : ℝ) (v : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => ReactionBindingEuler.E τ (v n) (X τ v x0 n)

/-- Exact endpoint sampling for an input constant on each mesh interval. -/
noncomputable def Y (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) : ℕ → ℝ
  | 0 => y0
  | n + 1 => MassActionBinding.sample τ (v n) (Y τ v y0 n)

@[simp] theorem X_zero (τ : ℝ) (v : ℕ → ℝ) (x0 : ℝ) : X τ v x0 0 = x0 := rfl
@[simp] theorem Y_zero (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) : Y τ v y0 0 = y0 := rfl
@[simp] theorem X_succ (τ : ℝ) (v : ℕ → ℝ) (x0 : ℝ) (n : ℕ) :
    X τ v x0 (n + 1) = ReactionBindingEuler.E τ (v n) (X τ v x0 n) := rfl
@[simp] theorem Y_succ (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) (n : ℕ) :
    Y τ v y0 (n + 1) = MassActionBinding.sample τ (v n) (Y τ v y0 n) := rfl

/-- Exact evolution within mesh interval `n`, parameterized by local time `s`.
The input is held at `v n` on this interval. -/
noncomputable def segment (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  MassActionBinding.sample s (v n) (Y τ v y0 n)

@[simp] theorem segment_initial (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) (n : ℕ) :
    segment τ v y0 n 0 = Y τ v y0 n := by
  exact MassActionBinding.sample_initial _ _

/-- The next exact mesh sample is the endpoint of this constant-input segment. -/
theorem segment_endpoint (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) (n : ℕ) :
    segment τ v y0 n τ = Y τ v y0 (n + 1) := rfl

/-- Each exact segment solves the scalar constant-input equation. -/
theorem segment_derivative (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ)
    (hv : ∀ n, 0 ≤ v n) (n : ℕ) (s : ℝ) :
    HasDerivAt (segment τ v y0 n)
      (1 - (1 + v n) * segment τ v y0 n s) s := by
  exact MassActionBinding.sample_derivative s (v n) (Y τ v y0 n) (hv n)

/-- Adjacent exact segments agree at the shared mesh endpoint. -/
theorem segment_join (τ : ℝ) (v : ℕ → ℝ) (y0 : ℝ) (n : ℕ) :
    segment τ v y0 n τ = segment τ v y0 (n + 1) 0 := by
  rw [segment_endpoint, segment_initial]

/-- The monotone Euler step restriction also implies interval invariance. -/
theorem mesh_bounds {τ M : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hmesh : τ ≤ 1 / (1 + M)) : τ ≤ 1 ∧ τ * M ≤ 1 := by
  have hp : τ * (1 + M) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 + M)).mp hmesh
  have hτM : 0 ≤ τ * M := mul_nonneg hτ hM
  constructor <;> nlinarith

/-- Both ends of the uniform Euler slope interval are explicit. -/
theorem slope_bounds {τ M v : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hmesh : τ ≤ 1 / (1 + M)) (hv0 : 0 ≤ v) (hvM : v ≤ M) :
    0 ≤ ReactionBindingEuler.slope τ v ∧
      ReactionBindingEuler.slope τ v ≤ 1 - τ := by
  have hp : τ * (1 + M) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 + M)).mp hmesh
  have hm := mul_le_mul_of_nonneg_left hvM hτ
  have hv := mul_nonneg hτ hv0
  dsimp [ReactionBindingEuler.slope]
  constructor <;> nlinarith

/-- Uniform contraction in state, with factor `1 - τ`. -/
theorem E_contract {τ M v : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hmesh : τ ≤ 1 / (1 + M)) (hv0 : 0 ≤ v) (hvM : v ≤ M)
    (x y : ℝ) :
    |ReactionBindingEuler.E τ v x - ReactionBindingEuler.E τ v y| ≤
      (1 - τ) * |x - y| := by
  obtain ⟨hs0, hs1⟩ := slope_bounds hM hτ hmesh hv0 hvM
  rw [ReactionBindingEuler.E_sub, abs_mul, abs_of_nonneg hs0]
  exact mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)

/-- Euler states stay physical under the stated mesh restriction. -/
theorem X_mem_unit {τ M x0 : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hx : 0 ≤ x0 ∧ x0 ≤ 1) (n : ℕ) :
    0 ≤ X τ v x0 n ∧ X τ v x0 n ≤ 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact ((ReactionBindingEuler.invariant_iff hτ hM).mpr (mesh_bounds hM hτ hmesh))
      (v n) (hv n).1 (hv n).2 (X τ v x0 n) ih.1 ih.2

/-- Exact samples stay physical without any upper restriction on the step. -/
theorem Y_mem_unit {τ M y0 : ℝ} (hτ : 0 ≤ τ) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hy : 0 ≤ y0 ∧ y0 ≤ 1) (n : ℕ) :
    0 ≤ Y τ v y0 n ∧ Y τ v y0 n ≤ 1 := by
  induction n with
  | zero => exact hy
  | succ n ih =>
    exact MassActionBinding.sample_invariant hτ (hv n).1 ih.1 ih.2

/-- One-step global-error recurrence, using the local defect at the exact state.
The Euler initial state may be arbitrary for this estimate. -/
theorem error_step {τ M x0 y0 : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hy : 0 ≤ y0 ∧ y0 ≤ 1) (n : ℕ) :
    |X τ v x0 (n + 1) - Y τ v y0 (n + 1)| ≤
      (1 - τ) * |X τ v x0 n - Y τ v y0 n| + τ ^ 2 * (1 + M) ^ 2 / 2 := by
  obtain ⟨hy0, hy1⟩ := Y_mem_unit hτ v hv hy n
  rw [X_succ, Y_succ]
  calc
    |ReactionBindingEuler.E τ (v n) (X τ v x0 n) -
        MassActionBinding.sample τ (v n) (Y τ v y0 n)|
      ≤ |ReactionBindingEuler.E τ (v n) (X τ v x0 n) -
            ReactionBindingEuler.E τ (v n) (Y τ v y0 n)| +
          |ReactionBindingEuler.E τ (v n) (Y τ v y0 n) -
            MassActionBinding.sample τ (v n) (Y τ v y0 n)| := abs_sub_le _ _ _
    _ ≤ (1 - τ) * |X τ v x0 n - Y τ v y0 n| + τ ^ 2 * (1 + M) ^ 2 / 2 :=
      add_le_add (E_contract hM hτ hmesh (hv n).1 (hv n).2 _ _)
        (EulerLocalError.local_error hτ (hv n).1 (hv n).2 hy0 hy1)

/-- Finite-horizon global error, retaining the initial mismatch and geometric factor.
Only the exact initial state needs to be physical for this stronger estimate. -/
theorem global_error_closed {τ M x0 y0 : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hy : 0 ≤ y0 ∧ y0 ≤ 1) (n : ℕ) :
    |X τ v x0 n - Y τ v y0 n| ≤ (1 - τ) ^ n * |x0 - y0| +
      τ * (1 + M) ^ 2 / 2 * (1 - (1 - τ) ^ n) := by
  have hk0 : 0 ≤ 1 - τ := by
    have := (mesh_bounds hM (le_of_lt hτ) hmesh).1
    linarith
  have hk1 : 1 - τ < 1 := by linarith
  have h := TrackingRecurrence.recurrence_bounded_drift_closed hk0 hk1
    (fun j => |X τ v x0 j - Y τ v y0 j|)
    (error_step hM (le_of_lt hτ) hmesh v hv hy) n
  have heq : τ ^ 2 * (1 + M) ^ 2 / 2 *
      ((1 - (1 - τ) ^ n) / (1 - (1 - τ))) =
      τ * (1 + M) ^ 2 / 2 * (1 - (1 - τ) ^ n) := by
    rw [show 1 - (1 - τ) = τ by ring]
    field_simp [ne_of_gt hτ]
  simpa only [X_zero, Y_zero, heq] using h

/-- Time-uniform forcing contribution, with the decaying initial mismatch retained. -/
theorem global_error_uniform {τ M x0 y0 : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hy : 0 ≤ y0 ∧ y0 ≤ 1) (n : ℕ) :
    |X τ v x0 n - Y τ v y0 n| ≤
      (1 - τ) ^ n * |x0 - y0| + τ * (1 + M) ^ 2 / 2 := by
  have hk0 : 0 ≤ 1 - τ := by
    have := (mesh_bounds hM (le_of_lt hτ) hmesh).1
    linarith
  have hk1 : 1 - τ < 1 := by linarith
  have hδ : 0 ≤ τ ^ 2 * (1 + M) ^ 2 / 2 := by positivity
  have h := TrackingRecurrence.recurrence_uniform hk0 hk1 hδ
    (fun j => |X τ v x0 j - Y τ v y0 j|)
    (error_step hM (le_of_lt hτ) hmesh v hv hy) n
  have heq : (τ ^ 2 * (1 + M) ^ 2 / 2) / (1 - (1 - τ)) =
      τ * (1 + M) ^ 2 / 2 := by
    rw [show 1 - (1 - τ) = τ by ring]
    field_simp [ne_of_gt hτ]
  simpa only [X_zero, Y_zero, heq] using h

/-- A joint physical-state and error certificate for distinct physical starts. -/
theorem physical_global_error {τ M x0 y0 : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M)
    (hx : 0 ≤ x0 ∧ x0 ≤ 1) (hy : 0 ≤ y0 ∧ y0 ≤ 1) (n : ℕ) :
    (0 ≤ X τ v x0 n ∧ X τ v x0 n ≤ 1) ∧
    (0 ≤ Y τ v y0 n ∧ Y τ v y0 n ≤ 1) ∧
    |X τ v x0 n - Y τ v y0 n| ≤ (1 - τ) ^ n * |x0 - y0| +
      τ * (1 + M) ^ 2 / 2 * (1 - (1 - τ) ^ n) := by
  exact ⟨X_mem_unit hM (le_of_lt hτ) hmesh v hv hx n,
    Y_mem_unit (le_of_lt hτ) v hv hy n,
    global_error_closed hM hτ hmesh v hv hy n⟩

/-- Matching physical initial states remove the initial-mismatch term. -/
theorem same_initial_error_closed {τ M x0 : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hx : 0 ≤ x0 ∧ x0 ≤ 1) (n : ℕ) :
    |X τ v x0 n - Y τ v x0 n| ≤
      τ * (1 + M) ^ 2 / 2 * (1 - (1 - τ) ^ n) := by
  simpa using global_error_closed (x0 := x0) hM hτ hmesh v hv hx n

/-- Classical all-time `O(τ)` estimate for matching physical initial states. -/
theorem same_initial_error {τ M x0 : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hmesh : τ ≤ 1 / (1 + M)) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (hx : 0 ≤ x0 ∧ x0 ≤ 1) (n : ℕ) :
    |X τ v x0 n - Y τ v x0 n| ≤ τ * (1 + M) ^ 2 / 2 := by
  simpa using global_error_uniform (x0 := x0) hM hτ hmesh v hv hx n

#print axioms segment_derivative
#print axioms segment_join
#print axioms slope_bounds
#print axioms E_contract
#print axioms X_mem_unit
#print axioms Y_mem_unit
#print axioms error_step
#print axioms global_error_closed
#print axioms global_error_uniform
#print axioms physical_global_error
#print axioms same_initial_error_closed
#print axioms same_initial_error

end EulerGlobalError
