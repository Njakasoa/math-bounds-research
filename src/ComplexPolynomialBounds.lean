import BoxPolynomialBounds
import Mathlib.Analysis.Complex.Basic

/-!
# Complex validity of the syntactic polynomial bounds

The same executable rational `amp` and `lip` bounds control the complex
interpretation on the polydisc. This is a structural induction on the syntax,
not an additional certificate hypothesis.
-/
namespace BoxPolynomialBounds
namespace Expr
variable {m n : ℕ}

/-- Interpretation of the rational polynomial syntax over the complex numbers. -/
noncomputable def evalComplex (u : Fin m → ℂ) (x : Fin n → ℂ) : Expr m n → ℂ
  | const c => c
  | input i => u i
  | state i => x i
  | add p q => p.evalComplex u x + q.evalComplex u x
  | mul p q => p.evalComplex u x * q.evalComplex u x

/-- The syntax and its rational multivariate polynomial have the same complex evaluation. -/
theorem evalComplex_toMvPolynomial (p : Expr m n) (u : Fin m → ℂ) (x : Fin n → ℂ) :
    MvPolynomial.eval₂Hom (Rat.castHom ℂ) (Sum.elim u x) p.toMvPolynomial =
      p.evalComplex u x := by
  induction p <;> simp_all [toMvPolynomial, evalComplex]

/-- Real inputs and real states embed compatibly into the complex interpretation. -/
theorem evalComplex_ofReal (p : Expr m n) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    p.evalComplex (fun i => (u i : ℂ)) (fun i => (x i : ℂ)) = (p.eval u x : ℂ) := by
  induction p <;> simp_all [evalComplex, eval]

/-- The syntactically computed magnitude bound also holds on the complex polydisc. -/
theorem evalComplex_norm_le_amp (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    {u : Fin m → ℂ} {x : Fin n → ℂ}
    (hu : ∀ i, ‖u i‖ ≤ (B : ℝ)) (hx : ∀ i, ‖x i‖ ≤ (r : ℝ)) :
    ‖p.evalComplex u x‖ ≤ (p.amp B r : ℝ) := by
  induction p with
  | const c => simp [evalComplex, amp]
  | input i => exact hu i
  | state i => exact hx i
  | add p q hp hq =>
    simp only [evalComplex, amp, Rat.cast_add]
    exact (norm_add_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    simp only [evalComplex, amp, Rat.cast_mul, norm_mul]
    exact mul_le_mul hp hq (norm_nonneg _) (by exact_mod_cast p.amp_nonneg hB hr)

/-- Every coordinate difference is bounded by the complex supremum distance. -/
lemma coordinate_norm_sub_le_dist (x y : Fin n → ℂ) (i : Fin n) :
    ‖x i - y i‖ ≤ dist x y := by
  simpa only [dist_eq_norm] using (dist_le_pi_dist x y i)

/-- The same rational state-Lipschitz bound holds uniformly on complex inputs and states. -/
theorem evalComplex_sub_norm_le_lip (p : Expr m n) {B r : ℚ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    {u : Fin m → ℂ} {x y : Fin n → ℂ}
    (hu : ∀ i, ‖u i‖ ≤ (B : ℝ)) (hx : ∀ i, ‖x i‖ ≤ (r : ℝ))
    (hy : ∀ i, ‖y i‖ ≤ (r : ℝ)) :
    ‖p.evalComplex u x - p.evalComplex u y‖ ≤ (p.lip B r : ℝ) * dist x y := by
  induction p with
  | const c => simp [evalComplex, lip]
  | input i => simp [evalComplex, lip]
  | state i => simpa [evalComplex, lip] using coordinate_norm_sub_le_dist x y i
  | add p q hp hq =>
    simp only [evalComplex, lip, Rat.cast_add]
    calc
      ‖p.evalComplex u x + q.evalComplex u x -
          (p.evalComplex u y + q.evalComplex u y)‖ =
          ‖(p.evalComplex u x - p.evalComplex u y) +
            (q.evalComplex u x - q.evalComplex u y)‖ := by congr 1; ring
      _ ≤ ‖p.evalComplex u x - p.evalComplex u y‖ +
          ‖q.evalComplex u x - q.evalComplex u y‖ := norm_add_le _ _
      _ ≤ (p.lip B r : ℝ) * dist x y + (q.lip B r : ℝ) * dist x y := add_le_add hp hq
      _ = ((p.lip B r : ℝ) + (q.lip B r : ℝ)) * dist x y := by ring
  | mul p q hp hq =>
    have hpamp := p.evalComplex_norm_le_amp hB hr hu hx
    have hqamp := q.evalComplex_norm_le_amp hB hr hu hy
    have hpnonneg : 0 ≤ (p.amp B r : ℝ) := by exact_mod_cast p.amp_nonneg hB hr
    have hqnonneg : 0 ≤ (q.amp B r : ℝ) := by exact_mod_cast q.amp_nonneg hB hr
    simp only [evalComplex, lip, Rat.cast_add, Rat.cast_mul]
    calc
      ‖p.evalComplex u x * q.evalComplex u x - p.evalComplex u y * q.evalComplex u y‖ =
          ‖p.evalComplex u x * (q.evalComplex u x - q.evalComplex u y) +
            q.evalComplex u y * (p.evalComplex u x - p.evalComplex u y)‖ := by congr 1; ring
      _ ≤ ‖p.evalComplex u x * (q.evalComplex u x - q.evalComplex u y)‖ +
          ‖q.evalComplex u y * (p.evalComplex u x - p.evalComplex u y)‖ := norm_add_le _ _
      _ = ‖p.evalComplex u x‖ * ‖q.evalComplex u x - q.evalComplex u y‖ +
          ‖q.evalComplex u y‖ * ‖p.evalComplex u x - p.evalComplex u y‖ := by
            rw [norm_mul, norm_mul]
      _ ≤ (p.amp B r : ℝ) * ((q.lip B r : ℝ) * dist x y) +
          (q.amp B r : ℝ) * ((p.lip B r : ℝ) * dist x y) :=
        add_le_add (mul_le_mul hpamp hq (norm_nonneg _) hpnonneg)
          (mul_le_mul hqamp hp (norm_nonneg _) hqnonneg)
      _ = ((p.amp B r : ℝ) * (q.lip B r : ℝ) +
          (q.amp B r : ℝ) * (p.lip B r : ℝ)) * dist x y := by ring

end Expr
end BoxPolynomialBounds
