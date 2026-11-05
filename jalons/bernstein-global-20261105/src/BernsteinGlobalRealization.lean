import BernsteinGlobalExample
import GlobalScalarMap

namespace BernsteinGlobalRealization

/-- The coefficient of the actual accepted degree-five Bernstein update. -/
noncomputable def b (u : ℝ) : ℝ :=
  BernsteinCertificate.q BernsteinGlobalExample.coeff ((u+1)/2)

noncomputable def update (u x : ℝ) : ℝ := GlobalScalarMap.step (5/13) (b u) x
noncomputable def equilibrium (u : ℝ) : ℝ := GlobalScalarMap.fixedState (5/13) (b u)

theorem b_identity (u : ℝ) : b u = 1 - (5/13 : ℝ)*(1+4*u^2) := by
  unfold b
  rw [BernsteinGlobalExample.q_target]
  ring

theorem b_bound {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) : |b u| ≤ 12/13 := by
  rw [b_identity]
  exact BernsteinGlobalExample.global_contraction_bound hu

theorem update_formula (u x : ℝ) : update u x =
    (5/13 : ℝ) + BernsteinCertificate.q BernsteinGlobalExample.coeff ((u+1)/2)*x := rfl

theorem update_preserves_box {u x : ℝ} (hu : u ∈ Set.Icc (-1) 1)
    (hx : |x| ≤ 5) : |update u x| ≤ 5 := by
  exact GlobalScalarMap.preserves_box (by norm_num) (b_bound hu) (by norm_num) hx

theorem update_contracts {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) (x y : ℝ) :
    |update u x - update u y| ≤ (12/13)*|x-y| :=
  GlobalScalarMap.contraction (b_bound hu)

theorem equilibrium_target {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    equilibrium u = 1/(1+4*u^2) :=
  GlobalScalarMap.fixedState_reciprocal (by norm_num) (b_identity u) (b_bound hu) (by norm_num)

theorem equilibrium_fixed {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    update u (equilibrium u) = equilibrium u :=
  GlobalScalarMap.fixedState_fixed (b_bound hu) (by norm_num)

theorem equilibrium_in_box {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    |equilibrium u| ≤ 5 :=
  GlobalScalarMap.fixedState_in_box (b_bound hu) (by norm_num) (by norm_num) (by norm_num)

theorem equilibrium_unique {u x : ℝ} (hu : u ∈ Set.Icc (-1) 1)
    (hx : update u x = x) : x = equilibrium u :=
  GlobalScalarMap.fixedState_unique (b_bound hu) (by norm_num) hx

/-- One state, one invariant box, and the fixed target of the certified update. -/
theorem stationary_realization {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    ∃ x : ℝ, |x| ≤ 5 ∧ update u x = x ∧ x = 1/(1+4*u^2) ∧
      ∀ y : ℝ, update u y = y → y = x := by
  exact ⟨equilibrium u, equilibrium_in_box hu, equilibrium_fixed hu,
    equilibrium_target hu, fun y hy => equilibrium_unique hu hy⟩

theorem polynomial_readout (R : Polynomial ℝ) {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    R.eval u * equilibrium u = R.eval u / (1+4*u^2) :=
  GlobalScalarMap.readout_ratio (by norm_num) (b_identity u) (b_bound hu) (by norm_num)

/-- The same scalar state is updated for every input in the driving sequence. -/
noncomputable def trajectory (u : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n+1 => update (u n) (trajectory u x0 n)

theorem trajectory_in_box (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (-1) 1)
    (x0 : ℝ) (hx0 : |x0| ≤ 5) (n : ℕ) : |trajectory u x0 n| ≤ 5 := by
  apply GlobalScalarMap.switched_box (κ := 12/13) (by norm_num) (by norm_num)
    (fun n => b (u n)) (trajectory u x0) (fun n => b_bound (hu n))
    (fun _ => rfl) hx0 n

/-- Synchronized contraction, not tracking of changing instantaneous equilibria. -/
theorem trajectories_contract (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (-1) 1)
    (x0 y0 : ℝ) (n : ℕ) :
    |trajectory u x0 n - trajectory u y0 n| ≤ (12/13 : ℝ)^n * |x0-y0| := by
  exact GlobalScalarMap.switched_contraction (κ := 12/13) (by norm_num)
    (fun n => b (u n)) (trajectory u x0) (trajectory u y0)
    (fun n => b_bound (hu n)) (fun _ => rfl) (fun _ => rfl) n

/-- Fixed-input error bound to the target of this very update. -/
theorem stationary_error {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) (x0 : ℝ) (n : ℕ) :
    |trajectory (fun _ => u) x0 n - 1/(1+4*u^2)| ≤
      (12/13 : ℝ)^n * |x0-1/(1+4*u^2)| := by
  have hc : ∀ n, trajectory (fun _ => u) (equilibrium u) n = equilibrium u := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [trajectory, ih] using equilibrium_fixed hu
  have h := trajectories_contract (fun _ => u) (fun _ => hu) x0 (equilibrium u) n
  rw [hc n, equilibrium_target hu] at h
  exact h

#print axioms stationary_realization
#print axioms polynomial_readout
#print axioms trajectory_in_box
#print axioms trajectories_contract
#print axioms stationary_error

end BernsteinGlobalRealization
