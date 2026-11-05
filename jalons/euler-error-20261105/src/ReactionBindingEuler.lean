import BernsteinCertificate
import Mathlib.Tactic

/-!
# Forward Euler for normalized reversible single-site binding

The normalized free fraction has scalar vector field `1 - (1 + v) * x`,
with nonnegative chemostatted input `v`. This file concerns its classical
forward-Euler map. It does not claim to formalize an actual chemical
experiment, the continuous-time solution, or a general reaction network.

The exact invariant-interval restriction is weaker than the restriction
that makes every Euler map nondecreasing. A signed-radius contraction
certificate alone does not establish preservation of `[0, 1]`.
-/

namespace ReactionBindingEuler

/-- The normalized scalar vector field, with time scaled by the off-rate. -/
def vectorField (v x : ℝ) : ℝ := 1 - (1 + v) * x

/-- Classical forward-Euler update. -/
def E (τ v x : ℝ) : ℝ := τ + (1 - τ * (1 + v)) * x

/-- The derivative of the affine Euler map with respect to its state. -/
def slope (τ v : ℝ) : ℝ := 1 - τ * (1 + v)

/-- Every input in `[0,M]` maps every state in `[0,1]` into `[0,1]`. -/
def Invariant (τ M : ℝ) : Prop :=
  ∀ v : ℝ, 0 ≤ v → v ≤ M → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    0 ≤ E τ v x ∧ E τ v x ≤ 1

theorem E_as_euler (τ v x : ℝ) : E τ v x = x + τ * vectorField v x := by
  dsimp [E, vectorField]
  ring

/-- An affine combination of the endpoint values `τ` and `1 - τ*v`. -/
theorem E_convex_form (τ v x : ℝ) :
    E τ v x = τ * (1 - x) + (1 - τ * v) * x := by
  dsimp [E]
  ring

/-- Exact uniform interval-invariance criterion. No monotonicity hypothesis is used. -/
theorem invariant_iff {τ M : ℝ} (hτ : 0 ≤ τ) (hM : 0 ≤ M) :
    Invariant τ M ↔ τ ≤ 1 ∧ τ * M ≤ 1 := by
  constructor
  · intro h
    have hzero := h 0 (by norm_num) hM 0 (by norm_num) (by norm_num)
    have hone := h M hM (le_refl M) 1 (by norm_num) (by norm_num)
    dsimp [E] at hzero hone
    constructor <;> nlinarith
  · rintro ⟨hτ1, hτM⟩ v hv0 hvM x hx0 hx1
    have hτv : τ * v ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hvM hτ) hτM
    have hτv0 : 0 ≤ τ * v := mul_nonneg hτ hv0
    have hxcomp : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    rw [E_convex_form]
    constructor
    · exact add_nonneg (mul_nonneg hτ hxcomp)
        (mul_nonneg (sub_nonneg.mpr hτv) hx0)
    · have ha := mul_le_mul_of_nonneg_right hτ1 hxcomp
      have hb := mul_le_mul_of_nonneg_right (show 1 - τ * v ≤ 1 by linarith) hx0
      nlinarith

/-- Monotonicity of one affine map is precisely nonnegativity of its slope. -/
theorem monotone_E_iff (τ v : ℝ) : Monotone (E τ v) ↔ 0 ≤ slope τ v := by
  constructor
  · intro h
    have h01 := h (show (0 : ℝ) ≤ 1 by norm_num)
    dsimp [E, slope] at *
    nlinarith
  · intro hs a b hab
    have h := mul_le_mul_of_nonneg_left hab hs
    dsimp [E, slope] at *
    linarith

/-- The uniform monotonicity condition is distinct from interval invariance. -/
theorem monotone_iff {τ M : ℝ} (hτ : 0 ≤ τ) (hM : 0 ≤ M) :
    (∀ v : ℝ, 0 ≤ v → v ≤ M → Monotone (E τ v)) ↔ τ ≤ 1 / (1 + M) := by
  have hden : 0 < 1 + M := by linarith
  rw [le_div_iff₀ hden]
  constructor
  · intro h
    have hs := (monotone_E_iff τ M).mp (h M hM (le_refl M))
    dsimp [slope] at hs
    linarith
  · intro h v _ hvM
    apply (monotone_E_iff τ v).mpr
    have hm := mul_le_mul_of_nonneg_left (show 1 + v ≤ 1 + M by linarith) hτ
    dsimp [slope]
    linarith

/-- The fixed-input equilibrium fraction. -/
noncomputable def fixedResponse (v : ℝ) : ℝ := 1 / (1 + v)

theorem fixedResponse_mem_unit {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ fixedResponse v ∧ fixedResponse v ≤ 1 := by
  have hden : 0 < 1 + v := by linarith
  dsimp [fixedResponse]
  constructor
  · positivity
  · apply (div_le_iff₀ hden).mpr
    linarith

theorem vectorField_fixedResponse {v : ℝ} (hv : 0 ≤ v) :
    vectorField v (fixedResponse v) = 0 := by
  have hden : 1 + v ≠ 0 := ne_of_gt (by linarith : 0 < 1 + v)
  dsimp [vectorField, fixedResponse]
  field_simp
  ring

theorem E_fixedResponse (τ : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    E τ v (fixedResponse v) = fixedResponse v := by
  rw [E_as_euler, vectorField_fixedResponse hv]
  ring

/-- Rational endpoint coefficients for the affine slope on input `v = 3*t`. -/
def coeff (τ : ℚ) : Fin 2 → ℚ := ![1 - τ, 1 - 4 * τ]

/-- The Bernstein certificate is attached to the actual Euler slope. -/
theorem q_coeff_eq_slope (τ : ℚ) (t : ℝ) :
    BernsteinCertificate.q (coeff τ) t = slope (τ : ℝ) (3 * t) := by
  norm_num [BernsteinCertificate.q, BernsteinCertificate.combination,
    BernsteinCertificate.weight, Fin.sum_univ_succ, coeff,
    bernsteinPolynomial, Nat.choose, slope]
  ring

/-- A checker certificate bounds the actual Euler slope on all inputs in `[0,3]`. -/
theorem slope_bound_of_check {τ κ r : ℚ}
    (h : BernsteinCertificate.check (coeff τ) τ κ r = true)
    {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    |slope (τ : ℝ) v| ≤ (κ : ℝ) := by
  have hs := (BernsteinCertificate.check_sound (coeff τ) τ κ r h).2.2.2.1
    (v / 3) (by linarith) (by linarith)
  rw [q_coeff_eq_slope] at hs
  have hscale : 3 * (v / 3) = v := by ring
  simpa only [hscale] using hs

theorem E_sub (τ v x y : ℝ) :
    E τ v x - E τ v y = slope τ v * (x - y) := by
  dsimp [E, slope]
  ring

/-- The original checker does give a contraction bound, even in the unsafe example. -/
theorem contraction_of_check {τ κ r : ℚ}
    (h : BernsteinCertificate.check (coeff τ) τ κ r = true)
    {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) (x y : ℝ) :
    |E (τ : ℝ) v x - E (τ : ℝ) v y| ≤ (κ : ℝ) * |x - y| := by
  rw [E_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (slope_bound_of_check h hv0 hv3) (abs_nonneg _)

/-- A finite rational guard for the physically meaningful interval. -/
def physicalGuard (τ M : ℚ) : Bool :=
  decide (0 ≤ τ ∧ 0 ≤ M ∧ τ ≤ 1 ∧ τ * M ≤ 1)

/-- The old signed-radius checker augmented with the physical interval guard.
The guard is independent of coefficient-to-slope realization; that identity
is established separately for the concrete coefficients below. -/
def checkPhys {n : ℕ} (c : Fin (n + 1) → ℚ) (τ M κ r : ℚ) : Bool :=
  BernsteinCertificate.check c τ κ r && physicalGuard τ M

theorem physicalGuard_iff (τ M : ℚ) :
    physicalGuard τ M = true ↔ 0 ≤ τ ∧ 0 ≤ M ∧ τ ≤ 1 ∧ τ * M ≤ 1 := by
  simp [physicalGuard]

theorem physicalGuard_sound {τ M : ℚ} (h : physicalGuard τ M = true) :
    Invariant (τ : ℝ) (M : ℝ) := by
  obtain ⟨hτ, hM, hτ1, hτM⟩ := (physicalGuard_iff τ M).mp h
  apply (invariant_iff (by exact_mod_cast hτ) (by exact_mod_cast hM)).mpr
  constructor
  · exact_mod_cast hτ1
  · exact_mod_cast hτM

theorem physicalGuard_complete {τ M : ℚ} (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (h : Invariant (τ : ℝ) (M : ℝ)) : physicalGuard τ M = true := by
  have hh := (invariant_iff (by exact_mod_cast hτ) (by exact_mod_cast hM)).mp h
  apply (physicalGuard_iff τ M).mpr
  refine ⟨hτ, hM, ?_, ?_⟩
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem checkPhys_invariant {n : ℕ} {c : Fin (n + 1) → ℚ} {τ M κ r : ℚ}
    (h : checkPhys c τ M κ r = true) : Invariant (τ : ℝ) (M : ℝ) := by
  have hh : BernsteinCertificate.check c τ κ r = true ∧ physicalGuard τ M = true := by
    simpa only [checkPhys, Bool.and_eq_true] using h
  exact physicalGuard_sound hh.2

/-- The unsafe step still passes the old signed-radius checker exactly. -/
theorem unsafe_check :
    BernsteinCertificate.check (coeff (2/5)) (2/5) (3/5) 1 = true := by
  rw [BernsteinCertificate.check_iff]
  norm_num [coeff, Fin.forall_fin_succ]

theorem unsafe_coeff : coeff (2/5) = ![(3/5 : ℚ), -(3/5)] := by
  funext i
  fin_cases i <;> norm_num [coeff]

theorem unsafe_output : E (2/5) 3 1 = (-1/5 : ℝ) := by norm_num [E]

theorem unsafe_not_invariant : ¬ Invariant (2/5) 3 := by
  intro h
  have hh := h 3 (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num)
  rw [unsafe_output] at hh
  norm_num at hh

theorem unsafe_guard_rejects : physicalGuard (2/5) 3 = false := by norm_num [physicalGuard]

theorem unsafe_checkPhys_rejects : checkPhys (coeff (2/5)) (2/5) 3 (3/5) 1 = false := by
  unfold checkPhys
  rw [unsafe_guard_rejects]
  simp

/-- A safe step passes both checkers. -/
theorem safe_check :
    BernsteinCertificate.check (coeff (1/3)) (1/3) (2/3) 1 = true := by
  rw [BernsteinCertificate.check_iff]
  norm_num [coeff, Fin.forall_fin_succ]

theorem safe_coeff : coeff (1/3) = ![(2/3 : ℚ), -(1/3)] := by
  funext i
  fin_cases i <;> norm_num [coeff]

theorem safe_guard_accepts : physicalGuard (1/3) 3 = true := by norm_num [physicalGuard]

theorem safe_checkPhys_accepts : checkPhys (coeff (1/3)) (1/3) 3 (2/3) 1 = true := by
  unfold checkPhys
  rw [safe_check, safe_guard_accepts]
  rfl

theorem safe_invariant : Invariant (1/3) 3 := by
  have h := physicalGuard_sound safe_guard_accepts
  norm_num at h
  exact h

/-- A safe interval-preserving Euler map need not be nondecreasing. -/
theorem safe_not_monotone : ¬ Monotone (E (1/3) 3) := by
  rw [monotone_E_iff]
  norm_num [slope]

/-- The exact uniform monotonicity threshold at `M = 3` is `1/4`. -/
theorem monotone_threshold_three {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ v : ℝ, 0 ≤ v → v ≤ 3 → Monotone (E τ v)) ↔ τ ≤ 1/4 := by
  have h := monotone_iff hτ (by norm_num : (0 : ℝ) ≤ 3)
  norm_num at h
  exact h

#eval BernsteinCertificate.check (coeff (2/5)) (2/5) (3/5) 1
#eval physicalGuard (2/5) 3
#eval checkPhys (coeff (2/5)) (2/5) 3 (3/5) 1
#eval BernsteinCertificate.check (coeff (1/3)) (1/3) (2/3) 1
#eval physicalGuard (1/3) 3
#eval checkPhys (coeff (1/3)) (1/3) 3 (2/3) 1

end ReactionBindingEuler
