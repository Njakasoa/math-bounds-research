import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! Explicit two-cell realization of `1 / (1 + 4*u^2)`.
All bounds below are real scalar bounds, not the archived checker's certificate.
The unique fixed point is proved by its explicit formula, without invoking Banach.
-/
noncomputable section
namespace TwoCell

def chart (s v : ℝ) : ℝ := s / 2 + v / 2

def denominator (u : ℝ) : ℝ := 1 + 4 * u ^ 2

def localDenominator (s v : ℝ) : ℝ := 2 + 2*s*v + v^2

def multiplier (s v : ℝ) : ℝ := 1/2 - s*v/2 + v^2/4

def residual (v : ℝ) : ℝ := -(v^4)/4

def stateMap (v x : ℝ) : ℝ := 1 + residual v * x

def fixedState (v : ℝ) : ℝ := 1 / (1 + v^4/4)

def output (s v x : ℝ) : ℝ := multiplier s v * x

theorem denominator_positive (u : ℝ) : 0 < denominator u := by
  unfold denominator
  positivity

theorem chart_identity (s v : ℝ) (hs : s^2 = 1) :
    denominator (chart s v) = localDenominator s v := by
  unfold denominator chart localDenominator
  nlinarith [hs]

theorem product_identity (s v : ℝ) (hs : s^2 = 1) :
    localDenominator s v * multiplier s v = 1 + v^4/4 := by
  unfold localDenominator multiplier
  nlinarith [congrArg (fun z : ℝ => z * v^2) hs]

theorem residual_identity (s v : ℝ) (hs : s^2 = 1) :
    1 - denominator (chart s v) * multiplier s v = residual v := by
  rw [chart_identity s v hs, product_identity s v hs]
  unfold residual
  ring

theorem residual_bound (v : ℝ) (hv : |v| ≤ 1) : |residual v| ≤ 1/4 := by
  rcases abs_le.mp hv with ⟨hlo, hhi⟩
  have hv2 : v^2 ≤ 1 := by nlinarith
  have hv4 : v^4 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv2)]
  unfold residual
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ v^4)]
  norm_num
  linarith

theorem stateMap_lipschitz (v x y : ℝ) (hv : |v| ≤ 1) :
    |stateMap v x - stateMap v y| ≤ (1/4) * |x-y| := by
  have h : stateMap v x - stateMap v y = residual v * (x-y) := by
    unfold stateMap
    ring
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_right (residual_bound v hv) (abs_nonneg _)

theorem stateMap_invariant (v x : ℝ) (hv : |v| ≤ 1) (hx : |x| ≤ 4/3) :
    |stateMap v x| ≤ 4/3 := by
  calc
    |stateMap v x| = |1 + residual v * x| := rfl
    _ ≤ |(1:ℝ)| + |residual v * x| := abs_add_le _ _
    _ = 1 + |residual v| * |x| := by rw [abs_mul]; norm_num
    _ ≤ 1 + (1/4) * (4/3) := by
      gcongr
      exact residual_bound v hv
    _ = 4/3 := by norm_num

theorem fixedState_fixed (v : ℝ) : stateMap v (fixedState v) = fixedState v := by
  have hd : (1 + v^4/4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold stateMap residual fixedState
  field_simp
  ring

theorem fixedState_bound (v : ℝ) : |fixedState v| ≤ 4/3 := by
  have hd : (0 : ℝ) < 1 + v^4/4 := by positivity
  unfold fixedState
  rw [abs_of_pos (by positivity)]
  apply (div_le_iff₀ hd).2
  nlinarith [pow_nonneg (sq_nonneg v) 2]

theorem fixedState_unique (v x : ℝ) (hx : stateMap v x = x) : x = fixedState v := by
  have hd : (1 + v^4/4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold stateMap residual at hx
  unfold fixedState
  apply (eq_div_iff hd).2
  nlinarith [hx]

theorem existsUnique_fixedState (v : ℝ) :
    ∃! x : ℝ, |x| ≤ 4/3 ∧ stateMap v x = x := by
  refine ⟨fixedState v, ⟨fixedState_bound v, fixedState_fixed v⟩, ?_⟩
  intro x hx
  exact fixedState_unique v x hx.2

theorem output_correct (s v x : ℝ) (hs : s^2 = 1)
    (hx : stateMap v x = x) : output s v x = 1 / denominator (chart s v) := by
  rw [fixedState_unique v x hx]
  have hp := product_identity s v hs
  have hd := denominator_positive (chart s v)
  rw [chart_identity s v hs] at hd ⊢
  unfold output fixedState
  apply (eq_div_iff (ne_of_gt hd)).2
  have hq : (1 + v^4/4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  nlinarith [hp]

theorem chart_maps_interval (s v : ℝ) (hs : s = -1 ∨ s = 1) (hv : |v| ≤ 1) :
    |chart s v| ≤ 1 := by
  rcases abs_le.mp hv with ⟨hlo, hhi⟩
  rcases hs with rfl | rfl <;> unfold chart <;> rw [abs_le] <;> constructor <;> linarith

theorem chart_coverage (u : ℝ) (hu : |u| ≤ 1) :
    ∃ s v : ℝ, (s = -1 ∨ s = 1) ∧ |v| ≤ 1 ∧ chart s v = u := by
  rcases abs_le.mp hu with ⟨hlo, hhi⟩
  by_cases h : u ≤ 0
  · refine ⟨-1, 2*u+1, Or.inl rfl, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · unfold chart; ring
  · refine ⟨1, 2*u-1, Or.inr rfl, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · unfold chart; ring

theorem boundary_agreement :
    output (-1) 1 (fixedState 1) = 1 ∧ output 1 (-1) (fixedState (-1)) = 1 := by
  norm_num [output, multiplier, fixedState]

/-- Every input in the full interval is realized by one certified local state. -/
theorem full_interval_realization (u : ℝ) (hu : |u| ≤ 1) :
    ∃ s v x : ℝ,
      (s = -1 ∨ s = 1) ∧ |v| ≤ 1 ∧ chart s v = u ∧
      |x| ≤ 4/3 ∧ stateMap v x = x ∧
      output s v x = 1 / denominator u := by
  obtain ⟨s, v, hs, hv, hc⟩ := chart_coverage u hu
  have hs2 : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨s, v, fixedState v, hs, hv, hc, fixedState_bound v,
    fixedState_fixed v, ?_⟩
  rw [output_correct s v (fixedState v) hs2 (fixedState_fixed v), hc]

end TwoCell
