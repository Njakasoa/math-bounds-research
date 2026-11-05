import MassActionBinding
import ReactionBindingEuler

/-!
# Local error of forward Euler for the normalized binding toy equation

The bounds concern a scalar constant-input ODE and its elementary exponential
solution. They are classical numerical-analysis statements, not empirical
validation of a chemical model.
-/

namespace EulerLocalError

/-- The elementary quadratic remainder bound on the negative exponential ray. -/
theorem exp_remainder {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Real.exp (-z) - 1 + z ∧
    Real.exp (-z) - 1 + z ≤ z ^ 2 / 2 := by
  have hder (t : ℝ) :
      HasDerivAt (fun s : ℝ => 1 - s + s ^ 2 / 2 - Real.exp (-s))
        (t - 1 + Real.exp (-t)) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
        ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg) using 1
    · rfl
    · dsimp
      ring
  have hmono : Monotone (fun s : ℝ => 1 - s + s ^ 2 / 2 - Real.exp (-s)) := by
    apply monotone_of_hasDerivAt_nonneg hder
    intro t
    have h := Real.add_one_le_exp (-t)
    dsimp
    linarith
  have hh := hmono hz
  norm_num at hh
  constructor
  · have h := Real.add_one_le_exp (-z)
    linarith
  · linarith

/-- Uniform one-step defect for input in `[0,M]` and state in `[0,1]`.
No Euler stability or step-size restriction is needed for this local bound. -/
theorem local_error {τ M v x : ℝ} (hτ : 0 ≤ τ) (hv0 : 0 ≤ v)
    (hvM : v ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |ReactionBindingEuler.E τ v x - MassActionBinding.sample τ v x| ≤
      τ ^ 2 * (1 + M) ^ 2 / 2 := by
  have hd : 0 < 1 + v := by linarith
  have hf0 : 0 ≤ MassActionBinding.fixedFraction v := by
    unfold MassActionBinding.fixedFraction
    positivity
  have hf1 : MassActionBinding.fixedFraction v ≤ 1 := by
    unfold MassActionBinding.fixedFraction
    apply (div_le_iff₀ hd).mpr
    linarith
  have hxf : |x - MassActionBinding.fixedFraction v| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hz : 0 ≤ τ * (1 + v) := mul_nonneg hτ (le_of_lt hd)
  obtain ⟨hr0, hr1⟩ := exp_remainder hz
  have hdiff : ReactionBindingEuler.E τ v x - MassActionBinding.sample τ v x =
      -(x - MassActionBinding.fixedFraction v) *
        (Real.exp (-(τ * (1 + v))) - 1 + τ * (1 + v)) := by
    unfold ReactionBindingEuler.E MassActionBinding.sample MassActionBinding.fixedFraction
    rw [show -(1 + v) * τ = -(τ * (1 + v)) by ring]
    field_simp [ne_of_gt hd]
    ring
  rw [hdiff, abs_mul, abs_neg, abs_of_nonneg hr0]
  calc
    |x - MassActionBinding.fixedFraction v| *
        (Real.exp (-(τ * (1 + v))) - 1 + τ * (1 + v))
      ≤ 1 * (Real.exp (-(τ * (1 + v))) - 1 + τ * (1 + v)) :=
        mul_le_mul_of_nonneg_right hxf hr0
    _ ≤ (τ * (1 + v)) ^ 2 / 2 := by simpa using hr1
    _ ≤ τ ^ 2 * (1 + M) ^ 2 / 2 := by
      have hh : (1 + v) ^ 2 ≤ (1 + M) ^ 2 := by nlinarith
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg τ)
      nlinarith

#print axioms exp_remainder
#print axioms local_error

end EulerLocalError
