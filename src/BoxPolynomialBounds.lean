import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Executable rational bounds for polynomial expressions on a box

A finite syntax tree gives a computable, sufficient magnitude and state-Lipschitz
bound. These bounds need no derivative oracle or unproved certification procedure.
The norm on finite real state vectors is the ordinary supremum norm.
-/
namespace BoxPolynomialBounds

/-- Polynomial syntax with separate input and state coordinates. -/
inductive Expr (m n : ℕ) where
  | const : ℚ → Expr m n
  | input : Fin m → Expr m n
  | state : Fin n → Expr m n
  | add : Expr m n → Expr m n → Expr m n
  | mul : Expr m n → Expr m n → Expr m n
  deriving DecidableEq, Repr

namespace Expr
variable {m n : ℕ}

/-- An executable rational magnitude bound on the input/state box. -/
def amp (B r : ℚ) : Expr m n → ℚ
  | const c => |c|
  | input _ => B
  | state _ => r
  | add p q => p.amp B r + q.amp B r
  | mul p q => p.amp B r * q.amp B r

/-- An executable rational state-Lipschitz bound on the same box. -/
def lip (B r : ℚ) : Expr m n → ℚ
  | const _ => 0
  | input _ => 0
  | state _ => 1
  | add p q => p.lip B r + q.lip B r
  | mul p q => p.amp B r * q.lip B r + q.amp B r * p.lip B r

/-- Interpretation over the reals. Only this semantic interpretation is noncomputable. -/
noncomputable def eval (u : Fin m → ℝ) (x : Fin n → ℝ) : Expr m n → ℝ
  | const c => c
  | input i => u i
  | state i => x i
  | add p q => p.eval u x + q.eval u x
  | mul p q => p.eval u x * q.eval u x

/-- The actual rational polynomial denoted by the syntax tree. -/
noncomputable def toMvPolynomial : Expr m n → MvPolynomial (Fin m ⊕ Fin n) ℚ
  | const c => MvPolynomial.C c
  | input i => MvPolynomial.X (Sum.inl i)
  | state i => MvPolynomial.X (Sum.inr i)
  | add p q => p.toMvPolynomial + q.toMvPolynomial
  | mul p q => p.toMvPolynomial * q.toMvPolynomial

/-- The syntax and actual polynomial have exactly the same real evaluation. -/
theorem eval_toMvPolynomial (p : Expr m n) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval₂Hom (Rat.castHom ℝ) (Sum.elim u x) p.toMvPolynomial = p.eval u x := by
  induction p <;> simp_all [toMvPolynomial, eval]

theorem amp_nonneg (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r) :
    0 ≤ p.amp B r := by
  induction p with
  | const c => exact abs_nonneg c
  | input i => exact hB
  | state i => exact hr
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

theorem lip_nonneg (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r) :
    0 ≤ p.lip B r := by
  induction p with
  | const c => exact le_rfl
  | input i => exact le_rfl
  | state i => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    exact add_nonneg (mul_nonneg (p.amp_nonneg hB hr) hq)
      (mul_nonneg (q.amp_nonneg hB hr) hp)

/-- Every syntax tree has its computed magnitude bound throughout the box. -/
theorem eval_abs_le_amp (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hu : ∀ i, |u i| ≤ (B : ℝ)) (hx : ∀ i, |x i| ≤ (r : ℝ)) :
    |p.eval u x| ≤ (p.amp B r : ℝ) := by
  induction p with
  | const c => simp [eval, amp]
  | input i => exact hu i
  | state i => exact hx i
  | add p q hp hq =>
    simp only [eval, amp, Rat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    simp only [eval, amp, Rat.cast_mul, abs_mul]
    exact mul_le_mul hp hq (abs_nonneg _) (by exact_mod_cast p.amp_nonneg hB hr)

/-- Each coordinate difference is bounded by the supremum distance. -/
lemma coordinate_abs_sub_le_dist (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ dist x y := by
  simpa [Real.dist_eq] using (dist_le_pi_dist x y i)

/-- The computed rational Lipschitz bound controls every pair in the box,
uniformly over all admissible inputs. -/
theorem eval_sub_abs_le_lip (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    {u : Fin m → ℝ} {x y : Fin n → ℝ}
    (hu : ∀ i, |u i| ≤ (B : ℝ)) (hx : ∀ i, |x i| ≤ (r : ℝ))
    (hy : ∀ i, |y i| ≤ (r : ℝ)) :
    |p.eval u x - p.eval u y| ≤ (p.lip B r : ℝ) * dist x y := by
  induction p with
  | const c => simp [eval, lip]
  | input i => simp [eval, lip]
  | state i => simpa [eval, lip] using coordinate_abs_sub_le_dist x y i
  | add p q hp hq =>
    simp only [eval, lip, Rat.cast_add]
    calc
      |p.eval u x + q.eval u x - (p.eval u y + q.eval u y)| =
          |(p.eval u x - p.eval u y) + (q.eval u x - q.eval u y)| := by congr 1; ring
      _ ≤ |p.eval u x - p.eval u y| + |q.eval u x - q.eval u y| := abs_add_le _ _
      _ ≤ (p.lip B r : ℝ) * dist x y + (q.lip B r : ℝ) * dist x y := add_le_add hp hq
      _ = ((p.lip B r : ℝ) + (q.lip B r : ℝ)) * dist x y := by ring
  | mul p q hp hq =>
    have hpamp := p.eval_abs_le_amp hB hr hu hx
    have hqamp := q.eval_abs_le_amp hB hr hu hy
    have hpnonneg : 0 ≤ (p.amp B r : ℝ) := by exact_mod_cast p.amp_nonneg hB hr
    have hqnonneg : 0 ≤ (q.amp B r : ℝ) := by exact_mod_cast q.amp_nonneg hB hr
    simp only [eval, lip, Rat.cast_add, Rat.cast_mul]
    calc
      |p.eval u x * q.eval u x - p.eval u y * q.eval u y| =
          |p.eval u x * (q.eval u x - q.eval u y) + q.eval u y * (p.eval u x - p.eval u y)| := by
            congr 1; ring
      _ ≤ |p.eval u x * (q.eval u x - q.eval u y)| +
          |q.eval u y * (p.eval u x - p.eval u y)| := abs_add_le _ _
      _ = |p.eval u x| * |q.eval u x - q.eval u y| +
          |q.eval u y| * |p.eval u x - p.eval u y| := by rw [abs_mul, abs_mul]
      _ ≤ (p.amp B r : ℝ) * ((q.lip B r : ℝ) * dist x y) +
          (q.amp B r : ℝ) * ((p.lip B r : ℝ) * dist x y) :=
        add_le_add (mul_le_mul hpamp hq (abs_nonneg _) hpnonneg)
          (mul_le_mul hqamp hp (abs_nonneg _) hqnonneg)
      _ = ((p.amp B r : ℝ) * (q.lip B r : ℝ) +
          (q.amp B r : ℝ) * (p.lip B r : ℝ)) * dist x y := by ring

end Expr
end BoxPolynomialBounds
