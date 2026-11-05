import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Module.Completion

/-! Rational multivariate polynomials with their coefficient ℓ¹ norm. -/

noncomputable section
open scoped BigOperators

namespace LocalAtlasRational

variable {m : ℕ}

/-- Coefficient ℓ¹ norm on rational polynomials, with equal monomials grouped. -/
def rationalCoeffL1 (p : MvPolynomial (Fin m) ℚ) : ℝ :=
  ∑ e ∈ p.support, ‖p.coeff e‖

theorem rationalCoeffL1_eq_sum_of_support_subset (p : MvPolynomial (Fin m) ℚ)
    (s : Finset (Fin m →₀ ℕ)) (hs : p.support ⊆ s) :
    rationalCoeffL1 p = ∑ e ∈ s, ‖p.coeff e‖ := by
  classical
  apply Finset.sum_subset hs
  intro e _ he
  rw [MvPolynomial.notMem_support_iff.mp he, norm_zero]

@[simp] theorem rationalCoeffL1_monomial (e : Fin m →₀ ℕ) (c : ℚ) :
    rationalCoeffL1 (MvPolynomial.monomial e c) = ‖c‖ := by
  rw [rationalCoeffL1_eq_sum_of_support_subset _ {e} MvPolynomial.support_monomial_subset]
  simp

@[simp] theorem rationalCoeffL1_zero :
    rationalCoeffL1 (0 : MvPolynomial (Fin m) ℚ) = 0 := by
  simp [rationalCoeffL1]

@[simp] theorem rationalCoeffL1_C (c : ℚ) :
    rationalCoeffL1 (MvPolynomial.C c : MvPolynomial (Fin m) ℚ) = ‖c‖ :=
  rationalCoeffL1_monomial 0 c

@[simp] theorem rationalCoeffL1_one :
    rationalCoeffL1 (1 : MvPolynomial (Fin m) ℚ) = 1 := by
  simpa using (rationalCoeffL1_C (m := m) 1)

@[simp] theorem rationalCoeffL1_X (i : Fin m) :
    rationalCoeffL1 (MvPolynomial.X i : MvPolynomial (Fin m) ℚ) = 1 := by
  simp [MvPolynomial.X]

lemma rationalCoeffL1_nonneg (p : MvPolynomial (Fin m) ℚ) : 0 ≤ rationalCoeffL1 p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma norm_coeff_le_rationalCoeffL1 (p : MvPolynomial (Fin m) ℚ) (e : Fin m →₀ ℕ) :
    ‖p.coeff e‖ ≤ rationalCoeffL1 p := by
  classical
  by_cases he : e ∈ p.support
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _) he
  · rw [MvPolynomial.notMem_support_iff.mp he, norm_zero]
    exact rationalCoeffL1_nonneg p

lemma rationalCoeffL1_eq_zero (p : MvPolynomial (Fin m) ℚ)
    (hp : rationalCoeffL1 p = 0) : p = 0 := by
  classical
  ext e
  by_cases he : e ∈ p.support
  · have hle : ‖p.coeff e‖ ≤ rationalCoeffL1 p :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) he
    exact norm_eq_zero.mp (le_antisymm (hp ▸ hle) (norm_nonneg _))
  · exact MvPolynomial.notMem_support_iff.mp he

lemma rationalCoeffL1_add_le (p q : MvPolynomial (Fin m) ℚ) :
    rationalCoeffL1 (p + q) ≤ rationalCoeffL1 p + rationalCoeffL1 q := by
  classical
  rw [rationalCoeffL1_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    MvPolynomial.support_add,
    rationalCoeffL1_eq_sum_of_support_subset p _ Finset.subset_union_left,
    rationalCoeffL1_eq_sum_of_support_subset q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _ => by simpa using norm_add_le (p.coeff e) (q.coeff e))

@[simp] lemma rationalCoeffL1_neg (p : MvPolynomial (Fin m) ℚ) :
    rationalCoeffL1 (-p) = rationalCoeffL1 p := by
  have hs : (-p).support = p.support := by
    ext e
    simp [MvPolynomial.mem_support_iff]
  simp [rationalCoeffL1, hs]

lemma rationalCoeffL1_sum_le {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin m) ℚ) :
    rationalCoeffL1 (∑ i ∈ s, p i) ≤ ∑ i ∈ s, rationalCoeffL1 (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (rationalCoeffL1_add_le _ _).trans (add_le_add (le_refl _) ih)

lemma rationalCoeffL1_mul_le (p q : MvPolynomial (Fin m) ℚ) :
    rationalCoeffL1 (p * q) ≤ rationalCoeffL1 p * rationalCoeffL1 q := by
  classical
  rw [MvPolynomial.mul_def, Finsupp.sum, MvPolynomial.finsupp_support_eq_support]
  apply (rationalCoeffL1_sum_le _ _).trans
  calc
    _ ≤ ∑ e ∈ p.support, ∑ f ∈ q.support, ‖p.coeff e‖ * ‖q.coeff f‖ := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [Finsupp.sum, MvPolynomial.finsupp_support_eq_support, rationalCoeffL1_monomial, norm_mul] using
        rationalCoeffL1_sum_le q.support
          (fun f => MvPolynomial.monomial (e + f) (p.coeff e * q.coeff f))
    _ = rationalCoeffL1 p * rationalCoeffL1 q := by
      simp only [rationalCoeffL1, Finset.sum_mul_sum]

lemma rationalCoeffL1_smul (c : ℚ) (p : MvPolynomial (Fin m) ℚ) :
    rationalCoeffL1 (c • p) = ‖c‖ * rationalCoeffL1 p := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · simp only [rationalCoeffL1, MvPolynomial.support_smul_eq hc,
      MvPolynomial.coeff_smul, norm_smul, Finset.mul_sum]

/-- Exact norm for a finitely supported sum with no repeated exponent vectors. -/
lemma rationalCoeffL1_sum_monomials (s : Finset (Fin m →₀ ℕ)) (c : (Fin m →₀ ℕ) → ℚ) :
    rationalCoeffL1 (∑ e ∈ s, MvPolynomial.monomial e (c e)) = ∑ e ∈ s, ‖c e‖ := by
  classical
  have hs : (∑ e ∈ s, MvPolynomial.monomial e (c e)).support ⊆ s := by
    intro e he
    by_contra hen
    have hz : (∑ f ∈ s, MvPolynomial.monomial f (c f)).coeff e = 0 := by
      simp [MvPolynomial.coeff_monomial, hen]
    exact (MvPolynomial.mem_support_iff.mp he) hz
  rw [rationalCoeffL1_eq_sum_of_support_subset _ s hs]
  apply Finset.sum_congr rfl
  intro e he
  simp [MvPolynomial.coeff_monomial, he]

/-- A type synonym separates the ℓ¹ norm from any other polynomial topology. -/
def RationalPolyL1 (m : ℕ) := MvPolynomial (Fin m) ℚ

namespace RationalPolyL1

instance : CommRing (RationalPolyL1 m) := inferInstanceAs (CommRing (MvPolynomial (Fin m) ℚ))
instance : Algebra ℚ (RationalPolyL1 m) :=
  inferInstanceAs (Algebra ℚ (MvPolynomial (Fin m) ℚ))

/-- The identity algebra equivalence, viewed in the coefficient-normed type. -/
def ofPolynomial : MvPolynomial (Fin m) ℚ ≃ₐ[ℚ] RationalPolyL1 m :=
  AlgEquiv.refl

/-- The coefficient ring norm. -/
def ringNorm : RingNorm (RationalPolyL1 m) where
  toFun := rationalCoeffL1
  map_zero' := rationalCoeffL1_zero
  add_le' := rationalCoeffL1_add_le
  neg' := rationalCoeffL1_neg
  mul_le' := rationalCoeffL1_mul_le
  eq_zero_of_map_eq_zero' := rationalCoeffL1_eq_zero

instance : NormedCommRing (RationalPolyL1 m) where
  __ := ringNorm.toNormedRing
  __ := (inferInstance : CommRing (RationalPolyL1 m))

instance : NormedAlgebra ℚ (RationalPolyL1 m) where
  norm_smul_le c p := (rationalCoeffL1_smul c p).le

theorem norm_eq (p : RationalPolyL1 m) : ‖p‖ = rationalCoeffL1 p := rfl

@[simp] theorem norm_ofPolynomial (p : MvPolynomial (Fin m) ℚ) :
    ‖ofPolynomial p‖ = rationalCoeffL1 p := rfl

instance : NormOneClass (RationalPolyL1 m) where
  norm_one := rationalCoeffL1_one

@[simp] theorem norm_X (i : Fin m) :
    ‖ofPolynomial (MvPolynomial.X i)‖ = 1 := rationalCoeffL1_X i

end RationalPolyL1

end LocalAtlasRational
