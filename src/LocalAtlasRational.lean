import LocalAtlasPerturbation
import LocalAtlasRationalNorm
import MultivariateInputExpr

noncomputable section
open scoped BigOperators
namespace LocalAtlas
open LocalAtlasRational MultivariateInputExpr

lemma rat_norm (q : ℚ) : ‖q‖ = |(q : ℝ)| := by
  rw [← Rat.norm_cast_real, Real.norm_eq_abs]

lemma rationalCoeffL1_eq_coeffL1 {m : ℕ} (p : InputPoly m) :
    rationalCoeffL1 p = (coeffL1 p : ℝ) := by
  simp only [rationalCoeffL1, coeffL1, Rat.cast_sum, Rat.cast_abs, rat_norm]

/-- Exact rational affine substitution. -/
def affineSubstitution {m : ℕ} (p : InputPoly m) (c : Fin m → ℚ) (h : ℚ) : InputPoly m :=
  p.eval₂ MvPolynomial.C (fun i => MvPolynomial.C (c i) + MvPolynomial.C h * MvPolynomial.X i)

/-- Explicit computable rational coefficient variation bound. -/
def variationConstant {m : ℕ} (p : InputPoly m) : ℚ :=
  ∑ e ∈ p.support, |p.coeff e| * (2 ^ (∑ i ∈ e.support, e i) - 1)

theorem rational_affine_bound {m : ℕ} (p : InputPoly m) (c : Fin m → ℚ)
    (h : ℚ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hc : ∀ i, |c i| ≤ 1) :
    coeffL1 (affineSubstitution p c h - MvPolynomial.C (MvPolynomial.eval c p)) ≤
      h * variationConstant p := by
  let f : ℚ →+* RationalPolyL1 m := RationalPolyL1.ofPolynomial.toRingHom.comp MvPolynomial.C
  have hf (q : ℚ) : ‖f q‖ = ‖q‖ := rationalCoeffL1_C q
  have hcr (i : Fin m) : ‖f (c i)‖ ≤ 1 := by
    rw [hf, rat_norm]
    exact_mod_cast hc i
  have hhr : 0 ≤ (h : ℝ) := by exact_mod_cast hh
  have hh1r : (h : ℝ) ≤ 1 := by exact_mod_cast hh1
  have hb (i : Fin m) :
      ‖(f (c i) + f h * RationalPolyL1.ofPolynomial (MvPolynomial.X i)) - f (c i)‖ ≤ (h : ℝ) := by
    simp only [add_sub_cancel_left]
    calc
      _ ≤ ‖f h‖ * ‖RationalPolyL1.ofPolynomial (MvPolynomial.X i)‖ := norm_mul_le _ _
      _ = (h : ℝ) := by rw [hf, RationalPolyL1.norm_X, mul_one, rat_norm, abs_of_nonneg hhr]
  have hbnd := polynomial_perturbation p f (fun i => f (c i))
    (fun i => f (c i) + f h * RationalPolyL1.ofPolynomial (MvPolynomial.X i))
    (h : ℝ) hhr hh1r hcr hb
  have hid : p.eval₂ f (fun i => f (c i)) =
      RationalPolyL1.ofPolynomial (MvPolynomial.C (MvPolynomial.eval c p)) := by
    exact (MvPolynomial.eval₂_comp f c p).symm
  rw [hid] at hbnd
  have hleft : p.eval₂ f (fun i => f (c i) + f h * RationalPolyL1.ofPolynomial (MvPolynomial.X i)) =
      RationalPolyL1.ofPolynomial (affineSubstitution p c h) := by
    rfl
  rw [hleft, ← map_sub, RationalPolyL1.norm_ofPolynomial, rationalCoeffL1_eq_coeffL1] at hbnd
  simp only [hf, rat_norm] at hbnd
  change (coeffL1 _ : ℝ) ≤ _ at hbnd
  unfold variationConstant
  exact_mod_cast hbnd

lemma variationConstant_nonneg {m : ℕ} (p : InputPoly m) : 0 ≤ variationConstant p := by
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))

lemma coeffL1_C_mul {m : ℕ} (q : InputPoly m) (t : ℚ) :
    coeffL1 (MvPolynomial.C t * q) = |t| * coeffL1 q := by
  have he := rationalCoeffL1_smul t q
  rw [← MvPolynomial.C_mul', rationalCoeffL1_eq_coeffL1,
    rationalCoeffL1_eq_coeffL1, rat_norm] at he
  exact_mod_cast he

lemma coeffL1_neg {m : ℕ} (q : InputPoly m) : coeffL1 (-q) = coeffL1 q := by
  have he := rationalCoeffL1_neg q
  rw [rationalCoeffL1_eq_coeffL1, rationalCoeffL1_eq_coeffL1] at he
  exact_mod_cast he

/-- The local constant multiplier gives a strict rational certificate whenever
the explicit variation budget is smaller than the value at the center. -/
theorem normalized_residual_lt {m : ℕ} (p : InputPoly m) (c : Fin m → ℚ)
    (h : ℚ) (hc : ∀ i, |c i| ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hsmall : h * variationConstant p < |MvPolynomial.eval c p|) :
    coeffL1 (1 - affineSubstitution p c h *
      MvPolynomial.C ((MvPolynomial.eval c p)⁻¹)) < 1 := by
  have hspos : 0 < |MvPolynomial.eval c p| :=
    lt_of_le_of_lt (mul_nonneg hh (variationConstant_nonneg p)) hsmall
  have hs : MvPolynomial.eval c p ≠ 0 := abs_pos.mp hspos
  have hid : 1 - affineSubstitution p c h * MvPolynomial.C ((MvPolynomial.eval c p)⁻¹) =
      -(MvPolynomial.C ((MvPolynomial.eval c p)⁻¹) *
        (affineSubstitution p c h - MvPolynomial.C (MvPolynomial.eval c p))) := by
    have hinv : MvPolynomial.C ((MvPolynomial.eval c p)⁻¹) *
        MvPolynomial.C (MvPolynomial.eval c p) = (1 : InputPoly m) := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    linear_combination -hinv
  rw [hid, coeffL1_neg, coeffL1_C_mul, abs_inv]
  calc
    _ ≤ |MvPolynomial.eval c p|⁻¹ * (h * variationConstant p) :=
      mul_le_mul_of_nonneg_left (rational_affine_bound p c h hh hh1 hc) (inv_nonneg.mpr (abs_nonneg _))
    _ < 1 := by
      rw [inv_mul_eq_div]
      exact (div_lt_one hspos).mpr hsmall

end LocalAtlas
