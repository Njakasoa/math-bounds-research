import BernsteinCertificate
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

open scoped BigOperators
open Polynomial
namespace BernsteinGlobalExample

def sCoeff : Fin 6 → ℚ := ![5, 9/5, 1/5, 1/5, 9/5, 5]
def coeff : Fin 6 → ℚ := ![-12/13, 4/13, 12/13, 12/13, 4/13, -12/13]
def baselineCoeff : Fin 6 → ℚ := ![-2/3, 2/5, 14/15, 14/15, 2/5, -2/3]

noncomputable def sPolynomial : ℚ[X] := 5 - 16 * X + 16 * X^2
noncomputable def qPolynomial : ℚ[X] := 1 - C (5/13) * sPolynomial

theorem s_bernstein_identity :
    (∑ i : Fin 6, C (sCoeff i) * bernsteinPolynomial ℚ 5 i) = sPolynomial := by
  apply Polynomial.funext
  intro x
  norm_num [Polynomial.eval_finsetSum, Fin.sum_univ_succ, sCoeff, bernsteinPolynomial, Nat.choose, sPolynomial]
  ring

theorem q_bernstein_identity :
    (∑ i : Fin 6, C (coeff i) * bernsteinPolynomial ℚ 5 i) = qPolynomial := by
  apply Polynomial.funext
  intro x
  norm_num [Polynomial.eval_finsetSum, Fin.sum_univ_succ, coeff, bernsteinPolynomial, Nat.choose, qPolynomial,
    sPolynomial, map_div₀]
  ring

theorem baseline_bernstein_identity :
    (∑ i : Fin 6, C (baselineCoeff i) * bernsteinPolynomial ℚ 5 i) =
      1 - C (1/3) * sPolynomial := by
  apply Polynomial.funext
  intro x
  norm_num [Polynomial.eval_finsetSum, Fin.sum_univ_succ, baselineCoeff, bernsteinPolynomial, Nat.choose,
    sPolynomial, map_div₀]
  ring

theorem domain_transform (u : ℝ) :
    (5 - 16 * ((u+1)/2) + 16 * ((u+1)/2)^2) = 1 + 4*u^2 := by ring

theorem target_identity (t : ℝ) :
    (5 - 16*t + 16*t^2) = 1 + 4*(2*t-1)^2 := by ring

theorem transform_mem_unit {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    (u+1)/2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]

theorem optimized_radius : |(5/13 : ℚ)| + (12/13)*5 = 5 := by norm_num

theorem baseline_radius : |(1/3 : ℚ)| + (14/15)*5 = 5 := by norm_num

theorem optimized_check : BernsteinCertificate.check coeff (5/13) (12/13) 5 = true := by
  rw [BernsteinCertificate.check_iff]
  norm_num [coeff, baselineCoeff, Fin.forall_fin_succ]

theorem baseline_check : BernsteinCertificate.check baselineCoeff (1/3) (14/15) 5 = true := by
  rw [BernsteinCertificate.check_iff]
  norm_num [coeff, baselineCoeff, Fin.forall_fin_succ]

theorem q_target (t : ℝ) :
    BernsteinCertificate.q coeff t = 1 - (5/13 : ℝ) * (1 + 4*(2*t-1)^2) := by
  rw [← BernsteinCertificate.qPolynomial_eval]
  change (∑ i : Fin 6, C (coeff i) * bernsteinPolynomial ℚ 5 i).eval₂ _ t = _
  rw [q_bernstein_identity]
  norm_num [qPolynomial, sPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow]
  ring

theorem global_contraction_bound {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    |1 - (5/13 : ℝ) * (1 + 4*u^2)| ≤ 12/13 := by
  have ht := transform_mem_unit hu
  have h := (BernsteinCertificate.check_sound coeff (5/13) (12/13) 5 optimized_check).2.2.2.1
    ((u+1)/2) ht.1 ht.2
  rw [q_target] at h
  norm_num at h
  convert h using 1
  congr 1
  ring

#eval BernsteinCertificate.check coeff (5/13) (12/13) 5
#eval BernsteinCertificate.check baselineCoeff (1/3) (14/15) 5

end BernsteinGlobalExample
