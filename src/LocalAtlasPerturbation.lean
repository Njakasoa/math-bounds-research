import LocalAtlasCoefficientNorm
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative finite-product perturbation, including the grouped coefficient
ℓ¹ norm via `ComplexPolyL1`. No certificate-existence hypothesis is used. -/
noncomputable section
open scoped BigOperators
namespace LocalAtlas

variable {A : Type*} [NormedCommRing A] [NormOneClass A]

/-- A unit-size factor perturbed by at most `h` has powers differing by at
most `h * (2^n - 1)`, uniformly for `0 ≤ h ≤ 1`. -/
theorem power_perturbation (a b : A) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b - a‖ ≤ h) (n : ℕ) :
    ‖b ^ n - a ^ n‖ ≤ h * (2 ^ n - 1) := by
  have hbn : ‖b‖ ≤ 2 := by
    calc
      ‖b‖ = ‖(b-a)+a‖ := by congr 1; ring
      _ ≤ ‖b-a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hap (k : ℕ) : ‖a ^ k‖ ≤ 1 := by
    calc
      _ ≤ ‖a‖ ^ k := norm_pow_le _ _
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : b ^ (n+1) - a ^ (n+1) = b * (b^n-a^n) + (b-a)*a^n := by ring
    rw [heq]
    calc
      _ ≤ ‖b * (b^n-a^n)‖ + ‖(b-a)*a^n‖ := norm_add_le _ _
      _ ≤ ‖b‖ * ‖b^n-a^n‖ + ‖b-a‖ * ‖a^n‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2 * (h * (2^n-1)) + h * 1 := by
        exact add_le_add (mul_le_mul hbn ih (norm_nonneg _) (by norm_num))
          (mul_le_mul hb (hap n) (norm_nonneg _) hh)
      _ = h * (2^(n+1)-1) := by ring

/-- Finite products of powers have perturbation controlled by total degree. -/
theorem product_perturbation {ι : Type*} (s : Finset ι) (a b : ι → A)
    (d : ι → ℕ) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i-a i‖ ≤ h) :
    ‖(∏ i ∈ s, b i ^ d i) - (∏ i ∈ s, a i ^ d i)‖ ≤
      h * (2 ^ (∑ i ∈ s, d i) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, ‖b j-a j‖ ≤ h := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hb2 : ‖b i‖ ≤ 2 := by
      calc
        ‖b i‖ = ‖(b i-a i)+a i‖ := by congr 1; ring
        _ ≤ ‖b i-a i‖ + ‖a i‖ := norm_add_le _ _
        _ ≤ 2 := by linarith
    have hbp : ‖b i ^ d i‖ ≤ 2 ^ d i :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hb2 _)
    have hap : ‖∏ j ∈ s, a j ^ d j‖ ≤ 1 := by
      apply (Finset.norm_prod_le _ _).trans
      apply Finset.prod_le_one₀
      · intro j hj; exact norm_nonneg _
      · intro j hj
        exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (has j hj))
    have hd := power_perturbation (a i) (b i) h hh hh1 hai hbi (d i)
    have hd0 : 0 ≤ h * (2 ^ d i - 1) := mul_nonneg hh (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have heq : b i ^ d i * (∏ j ∈ s, b j ^ d j) - a i ^ d i * (∏ j ∈ s, a j ^ d j) =
        b i ^ d i * ((∏ j ∈ s, b j ^ d j) - (∏ j ∈ s, a j ^ d j)) +
        (b i ^ d i-a i ^ d i) * (∏ j ∈ s, a j ^ d j) := by ring
    rw [heq]
    calc
      _ ≤ ‖b i ^ d i‖ * ‖(∏ j ∈ s, b j ^ d j) - (∏ j ∈ s, a j ^ d j)‖ +
          ‖b i ^ d i-a i ^ d i‖ * ‖∏ j ∈ s, a j ^ d j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 2 ^ d i * (h * (2 ^ (∑ j ∈ s, d j)-1)) + h * (2 ^ d i-1) * 1 :=
        add_le_add (mul_le_mul hbp (ih has hbs) (norm_nonneg _) (by positivity))
          (mul_le_mul hd hap (norm_nonneg _) hd0)
      _ = h * (2 ^ (d i + ∑ j ∈ s, d j)-1) := by rw [pow_add]; ring

end LocalAtlas

namespace LocalAtlas
variable {A : Type*} [NormedCommRing A] [NormOneClass A]

/-- Universal polynomial substitution bound, with the exact grouped input
coefficients and total degree of each supported monomial. -/
theorem polynomial_perturbation {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (f : R →+* A) (a b : σ → A)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i-a i‖ ≤ h) :
    ‖p.eval₂ f b - p.eval₂ f a‖ ≤
      h * ∑ e ∈ p.support, ‖f (p.coeff e)‖ * (2 ^ (∑ i ∈ e.support, e i)-1) := by
  classical
  simp only [MvPolynomial.eval₂_eq, ← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ e ∈ p.support, ‖f (p.coeff e)‖ * (h * (2 ^ (∑ i ∈ e.support, e i)-1)) := by
      apply Finset.sum_le_sum
      intro e he
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (product_perturbation e.support a b e h hh hh1 (fun i _ => ha i) (fun i _ => hb i))
        (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e he; ring

open MultivariateWiener
/-- Concrete coefficient-ℓ¹ affine-substitution estimate. Constants and variables
live in the coefficient-normed polynomial wrapper, so no norm inequality is assumed. -/
theorem affine_coefficient_bound {m : ℕ} (p : MvPolynomial (Fin m) ℂ)
    (c : Fin m → ℂ) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hc : ∀ i, ‖c i‖ ≤ 1) :
    let f : ℂ →+* ComplexPolyL1 m :=
      ComplexPolyL1.ofPolynomial.toRingHom.comp MvPolynomial.C
    let a : Fin m → ComplexPolyL1 m := fun i => f (c i)
    let b : Fin m → ComplexPolyL1 m := fun i => a i + f (h : ℂ) *
      ComplexPolyL1.ofPolynomial (MvPolynomial.X i)
    ‖p.eval₂ f b - p.eval₂ f a‖ ≤
      h * ∑ e ∈ p.support, ‖p.coeff e‖ * (2 ^ (∑ i ∈ e.support, e i)-1) := by
  dsimp only
  let f : ℂ →+* ComplexPolyL1 m :=
    ComplexPolyL1.ofPolynomial.toRingHom.comp MvPolynomial.C
  have hf (z : ℂ) : ‖f z‖ = ‖z‖ := complexCoeffL1_C z
  have result := polynomial_perturbation p f (fun i => f (c i))
    (fun i => f (c i) + f (h : ℂ) * ComplexPolyL1.ofPolynomial (MvPolynomial.X i))
    h hh hh1 (fun i => (hf (c i)).trans_le (hc i)) (by
      intro i
      simp only [add_sub_cancel_left]
      calc
        _ ≤ ‖f (h : ℂ)‖ * ‖ComplexPolyL1.ofPolynomial (MvPolynomial.X i)‖ := norm_mul_le _ _
        _ = h := by rw [hf, ComplexPolyL1.norm_X, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh])
  simpa only [hf] using result

end LocalAtlas
