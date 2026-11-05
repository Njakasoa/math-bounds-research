import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic

namespace BernsteinCertificate

/-- A finite rational checker. No polynomial equality or analytic oracle is evaluated. -/
def check {n : ℕ} (c : Fin (n + 1) → ℚ) (η κ r : ℚ) : Bool :=
  decide (0 ≤ r ∧ 0 ≤ κ ∧ κ < 1 ∧ (∀ i, |c i| ≤ κ) ∧ |η| + κ * r ≤ r)

noncomputable def weight (n : ℕ) (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n i).eval t

noncomputable def combination {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * weight n i t

noncomputable def q {n : ℕ} (c : Fin (n + 1) → ℚ) (t : ℝ) : ℝ :=
  combination (fun i => (c i : ℝ)) t

lemma weight_nonneg {n : ℕ} (i : Fin (n + 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ weight n i t := by
  simpa [weight, bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap] using
    (bernstein_nonneg (n := n) (ν := i) (x := ⟨t, ht0, ht1⟩))

lemma sum_weight (n : ℕ) (t : ℝ) : ∑ i : Fin (n + 1), weight n i t = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval t) (bernsteinPolynomial.sum ℝ n)
  simpa [weight, Finset.sum_range, Polynomial.eval_finsetSum] using h

/-- Every Bernstein combination lies in the closed hull of its coefficients. -/
theorem coefficient_hull {n : ℕ} (c : Fin (n + 1) → ℝ) (lo hi t : ℝ)
    (hc : ∀ i, lo ≤ c i ∧ c i ≤ hi) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lo ≤ combination c t ∧ combination c t ≤ hi := by
  have hl : (∑ i, lo * weight n i t) = lo := by rw [← Finset.mul_sum, sum_weight, mul_one]
  have hh : (∑ i, hi * weight n i t) = hi := by rw [← Finset.mul_sum, sum_weight, mul_one]
  constructor
  · rw [← hl]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i).1 (weight_nonneg i ht0 ht1)
  · rw [← hh]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i).2 (weight_nonneg i ht0 ht1)

lemma check_iff {n : ℕ} (c : Fin (n + 1) → ℚ) (η κ r : ℚ) :
    check c η κ r = true ↔
    0 ≤ r ∧ 0 ≤ κ ∧ κ < 1 ∧ (∀ i, |c i| ≤ κ) ∧ |η| + κ * r ≤ r := by
  simp [check]

 theorem q_abs_le {n : ℕ} (c : Fin (n + 1) → ℚ) (κ : ℚ)
    (hc : ∀ i, |c i| ≤ κ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |q c t| ≤ (κ : ℝ) := by
  apply abs_le.mpr
  apply coefficient_hull (fun i => (c i : ℝ)) (-(κ : ℝ)) (κ : ℝ) t _ ht0 ht1
  intro i
  have h : |(c i : ℝ)| ≤ (κ : ℝ) := by exact_mod_cast hc i
  exact abs_le.mp h

 theorem check_sound {n : ℕ} (c : Fin (n + 1) → ℚ) (η κ r : ℚ)
    (h : check c η κ r = true) :
    0 ≤ (r : ℝ) ∧ 0 ≤ (κ : ℝ) ∧ (κ : ℝ) < 1 ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → |q c t| ≤ (κ : ℝ)) ∧
    |(η : ℝ)| + (κ : ℝ) * (r : ℝ) ≤ (r : ℝ) := by
  obtain ⟨hr, hk0, hk1, hc, hclose⟩ := (check_iff c η κ r).mp h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hr
  · exact_mod_cast hk0
  · exact_mod_cast hk1
  · exact fun t ht0 ht1 => q_abs_le c κ hc ht0 ht1
  · exact_mod_cast hclose

noncomputable def qPolynomial {n : ℕ} (c : Fin (n + 1) → ℚ) : Polynomial ℚ :=
  ∑ i, Polynomial.C (c i) * bernsteinPolynomial ℚ n i

lemma qPolynomial_eval {n : ℕ} (c : Fin (n + 1) → ℚ) (t : ℝ) :
    (qPolynomial c).eval₂ (Rat.castHom ℝ) t = q c t := by
  simp [qPolynomial, q, combination, weight, bernsteinPolynomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_sub]

#eval check (n := 2) ![(1/4 : ℚ), -(1/3), 1/2] (1/4) (1/2) 1
#eval check (n := 2) ![(1/4 : ℚ), -(1/3), 3/4] (1/4) (1/2) 1

end BernsteinCertificate
