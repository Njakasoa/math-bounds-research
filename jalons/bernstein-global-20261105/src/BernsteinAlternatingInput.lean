import BernsteinGlobalRealization

/-! Explicit limit of the switching guarantee: common-state contraction does
not imply exact tracking of a moving instantaneous equilibrium. -/
namespace BernsteinAlternatingInput
open BernsteinGlobalRealization

theorem cycle_first : update 0 (1/53) = 21/53 := by
  norm_num [update, GlobalScalarMap.step, b_identity]

theorem cycle_second : update 1 (21/53) = 1/53 := by
  norm_num [update, GlobalScalarMap.step, b_identity]

def alternatingInput (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1
noncomputable def cycleState (n : ℕ) : ℝ := if n % 2 = 0 then 1/53 else 21/53

theorem alternating_admissible (n : ℕ) : alternatingInput n ∈ Set.Icc (-1) 1 := by
  unfold alternatingInput
  split_ifs <;> norm_num

theorem cycle_recurrence (n : ℕ) :
    cycleState (n+1) = update (alternatingInput n) (cycleState n) := by
  by_cases h : n % 2 = 0
  · have hn : (n+1)%2 ≠ 0 := by omega
    simp only [cycleState, alternatingInput, h, hn, if_true, if_false]
    exact cycle_first.symm
  · have hn : (n+1)%2 = 0 := by omega
    simp only [cycleState, alternatingInput, h, hn, if_true, if_false]
    exact cycle_second.symm

theorem actual_trajectory (n : ℕ) : trajectory alternatingInput (1/53) n = cycleState n := by
  induction n with
  | zero => norm_num [trajectory, cycleState]
  | succ n ih =>
    rw [trajectory, ih]
    exact (cycle_recurrence n).symm

/-- The error to the current equilibrium is persistently nonzero at every
even time, despite uniform synchronized contraction. -/
theorem persistent_even_error (n : ℕ) :
    |trajectory alternatingInput (1/53) (2*n) -
      1/(1+4*(alternatingInput (2*n))^2)| = 52/53 := by
  rw [actual_trajectory]
  norm_num [alternatingInput, cycleState]

end BernsteinAlternatingInput
