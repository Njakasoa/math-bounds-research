import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

noncomputable section
namespace LocalAtlas

/-- Rational centers of the uniform subdivision of `[-1,1]`. -/
def gridCenter (N : ℕ) (a : Fin N) : ℚ := -1 + (2 * (a.val : ℚ) + 1) / N

lemma exists_grid_index (N : ℕ) (hN : 0 < N) (u : ℝ) (hu : |u| ≤ 1) :
    ∃ a : Fin N, (a.val : ℝ) ≤ (u + 1) * N / 2 ∧
      (u + 1) * N / 2 ≤ (a.val : ℝ) + 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  by_cases he : u = 1
  · refine ⟨⟨N - 1, by omega⟩, ?_⟩
    have hs : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      exact_mod_cast (Nat.sub_add_cancel hN)
    subst u
    constructor <;> nlinarith
  · have hx : 0 ≤ (u + 1) * (N : ℝ) / 2 :=
      div_nonneg (mul_nonneg (by linarith) (le_of_lt hn)) (by norm_num)
    have hu1 : u < 1 := lt_of_le_of_ne hr he
    have hxN : (u + 1) * (N : ℝ) / 2 < N := by nlinarith
    refine ⟨⟨⌊(u + 1) * (N : ℝ) / 2⌋₊, (Nat.floor_lt hx).2 hxN⟩, ?_, ?_⟩
    · exact Nat.floor_le hx
    · exact le_of_lt (Nat.lt_floor_add_one _)

lemma gridCenter_mem (N : ℕ) (hN : 0 < N) (a : Fin N) :
    |(gridCenter N a : ℝ)| ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (a.val : ℝ) < N := by exact_mod_cast a.isLt
  have ha0 : (0 : ℝ) ≤ a.val := by positivity
  simp only [gridCenter, Rat.cast_add, Rat.cast_neg, Rat.cast_one,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
  have hlow : 0 ≤ (2 * (a.val : ℝ) + 1) / N := by positivity
  have hhigh : (2 * (a.val : ℝ) + 1) / N ≤ 2 := by
    apply (div_le_iff₀ hn).2
    have hstep : (a.val : ℝ) + 1 ≤ N := by exact_mod_cast a.isLt
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every point of the cube belongs to one of its rational grid subcubes. -/
theorem grid_coverage (m N : ℕ) (hN : 0 < N) (u : Fin m → ℝ)
    (hu : ∀ j, |u j| ≤ 1) :
    ∃ a : Fin m → Fin N, ∃ v : Fin m → ℝ,
      (∀ j, |v j| ≤ 1) ∧
      ∀ j, u j = (gridCenter N (a j) : ℝ) + (1 / (N : ℝ)) * v j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  choose a ha hb using fun j => exists_grid_index N hN (u j) (hu j)
  refine ⟨a, fun j => (u j + 1) * N - (2 * ((a j).val : ℝ) + 1), ?_, ?_⟩
  · intro j
    apply abs_le.mpr
    constructor <;> nlinarith [ha j, hb j]
  · intro j
    simp only [gridCenter, Rat.cast_add, Rat.cast_neg, Rat.cast_one,
      Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    field_simp
    ring

/-- The subdivision uses only finitely many rational center vectors. -/
theorem grid_centers_finite (m N : ℕ) :
    (Set.range (fun a : Fin m → Fin N => fun j => gridCenter N (a j))).Finite :=
  Set.finite_range _

end LocalAtlas
