import Mathlib

/-! Algebraic bridge for R+L ⇌ C with externally imposed ligand.
No assertion of empirical validity or ODE-solver verification is made. -/
namespace MassActionBinding

/-- a = k_on L, b = k_off; the two receptor forms have opposite fluxes. -/
def freeRate (a b r c : ℝ) := -a*r+b*c
def boundRate (a b r c : ℝ) := a*r-b*c

theorem receptor_conservation (a b r c : ℝ) :
    freeRate a b r c + boundRate a b r c = 0 := by
  unfold freeRate boundRate
  ring

/-- Substitution r=R*x, c=R*(1-x), dimensionless time s=b*t. -/
theorem normalized_vector_field (a b R x : ℝ) (hb : 0 < b) (hR : 0 < R) :
    freeRate a b (R*x) (R*(1-x))/(b*R) = 1-(1+a/b)*x := by
  unfold freeRate
  field_simp [ne_of_gt hb, ne_of_gt hR]
  ring

noncomputable def fixedFraction (v : ℝ) : ℝ := 1/(1+v)
/-- Analytic constant-input sampling expression, distinct from Euler. -/
noncomputable def sample (τ v x : ℝ) : ℝ :=
  fixedFraction v+(x-fixedFraction v)*Real.exp (-(1+v)*τ)

theorem sample_invariant {τ v x : ℝ} (hτ : 0 ≤ τ) (hv : 0 ≤ v)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ sample τ v x ∧ sample τ v x ≤ 1 := by
  have hf0 : 0 ≤ fixedFraction v := by unfold fixedFraction; positivity
  have hf1 : fixedFraction v ≤ 1 := by
    unfold fixedFraction
    apply (div_le_iff₀ (by linarith : (0:ℝ)<1+v)).mpr
    linarith
  have hq0 : 0 ≤ Real.exp (-(1+v)*τ) := le_of_lt (Real.exp_pos _)
  have hq1 : Real.exp (-(1+v)*τ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  unfold sample
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hf0,
      mul_nonneg hq0 hx0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hf1),
      mul_nonneg hq0 (sub_nonneg.mpr hx1)]

theorem sample_initial (v x : ℝ) : sample 0 v x = x := by
  simp [sample]

/-- Verification of the constant-input ODE, not an approximation claim. -/
theorem sample_derivative (τ v x : ℝ) (hv : 0 ≤ v) :
    HasDerivAt (fun t => sample t v x) (1-(1+v)*sample τ v x) τ := by
  have hd : 0 < 1+v := by linarith
  have h := (Real.hasDerivAt_exp (-(1+v)*τ)).comp τ
    ((hasDerivAt_id τ).const_mul (-(1+v)))
  have hh := (h.const_mul (x-fixedFraction v)).const_add (fixedFraction v)
  convert hh using 1
  · ext t
    simp [sample]
  · dsimp [sample, fixedFraction]
    field_simp [ne_of_gt hd]
    ring

#print axioms sample_derivative
#print axioms receptor_conservation
#print axioms normalized_vector_field
#print axioms sample_invariant
end MassActionBinding
