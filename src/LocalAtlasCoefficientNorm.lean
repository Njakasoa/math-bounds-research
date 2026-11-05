import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Module.Completion

/-! Complex multivariate polynomials with their coefficient ℓ¹ norm. -/

noncomputable section
open scoped BigOperators

namespace MultivariateWiener

variable {m : ℕ}

/-- Coefficient ℓ¹ norm on complex polynomials, with equal monomials grouped. -/
def complexCoeffL1 (p : MvPolynomial (Fin m) ℂ) : ℝ :=
  ∑ e ∈ p.support, ‖p.coeff e‖

theorem complexCoeffL1_eq_sum_of_support_subset (p : MvPolynomial (Fin m) ℂ)
    (s : Finset (Fin m →₀ ℕ)) (hs : p.support ⊆ s) :
    complexCoeffL1 p = ∑ e ∈ s, ‖p.coeff e‖ := by
  classical
  apply Finset.sum_subset hs
  intro e _ he
  rw [MvPolynomial.notMem_support_iff.mp he, norm_zero]

@[simp] theorem complexCoeffL1_monomial (e : Fin m →₀ ℕ) (c : ℂ) :
    complexCoeffL1 (MvPolynomial.monomial e c) = ‖c‖ := by
  rw [complexCoeffL1_eq_sum_of_support_subset _ {e} MvPolynomial.support_monomial_subset]
  simp

@[simp] theorem complexCoeffL1_zero :
    complexCoeffL1 (0 : MvPolynomial (Fin m) ℂ) = 0 := by
  simp [complexCoeffL1]

@[simp] theorem complexCoeffL1_C (c : ℂ) :
    complexCoeffL1 (MvPolynomial.C c : MvPolynomial (Fin m) ℂ) = ‖c‖ :=
  complexCoeffL1_monomial 0 c

@[simp] theorem complexCoeffL1_one :
    complexCoeffL1 (1 : MvPolynomial (Fin m) ℂ) = 1 := by
  simpa using (complexCoeffL1_C (m := m) 1)

@[simp] theorem complexCoeffL1_X (i : Fin m) :
    complexCoeffL1 (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) = 1 := by
  simp [MvPolynomial.X]

lemma complexCoeffL1_nonneg (p : MvPolynomial (Fin m) ℂ) : 0 ≤ complexCoeffL1 p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma norm_coeff_le_complexCoeffL1 (p : MvPolynomial (Fin m) ℂ) (e : Fin m →₀ ℕ) :
    ‖p.coeff e‖ ≤ complexCoeffL1 p := by
  classical
  by_cases he : e ∈ p.support
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _) he
  · rw [MvPolynomial.notMem_support_iff.mp he, norm_zero]
    exact complexCoeffL1_nonneg p

lemma complexCoeffL1_eq_zero (p : MvPolynomial (Fin m) ℂ)
    (hp : complexCoeffL1 p = 0) : p = 0 := by
  classical
  ext e
  by_cases he : e ∈ p.support
  · have hle : ‖p.coeff e‖ ≤ complexCoeffL1 p :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) he
    exact norm_eq_zero.mp (le_antisymm (hp ▸ hle) (norm_nonneg _))
  · exact MvPolynomial.notMem_support_iff.mp he

lemma complexCoeffL1_add_le (p q : MvPolynomial (Fin m) ℂ) :
    complexCoeffL1 (p + q) ≤ complexCoeffL1 p + complexCoeffL1 q := by
  classical
  rw [complexCoeffL1_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    MvPolynomial.support_add,
    complexCoeffL1_eq_sum_of_support_subset p _ Finset.subset_union_left,
    complexCoeffL1_eq_sum_of_support_subset q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _ => by simpa using norm_add_le (p.coeff e) (q.coeff e))

@[simp] lemma complexCoeffL1_neg (p : MvPolynomial (Fin m) ℂ) :
    complexCoeffL1 (-p) = complexCoeffL1 p := by
  have hs : (-p).support = p.support := by
    ext e
    simp [MvPolynomial.mem_support_iff]
  simp [complexCoeffL1, hs]

lemma complexCoeffL1_sum_le {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin m) ℂ) :
    complexCoeffL1 (∑ i ∈ s, p i) ≤ ∑ i ∈ s, complexCoeffL1 (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (complexCoeffL1_add_le _ _).trans (add_le_add (le_refl _) ih)

lemma complexCoeffL1_mul_le (p q : MvPolynomial (Fin m) ℂ) :
    complexCoeffL1 (p * q) ≤ complexCoeffL1 p * complexCoeffL1 q := by
  classical
  rw [MvPolynomial.mul_def, Finsupp.sum, MvPolynomial.finsupp_support_eq_support]
  apply (complexCoeffL1_sum_le _ _).trans
  calc
    _ ≤ ∑ e ∈ p.support, ∑ f ∈ q.support, ‖p.coeff e‖ * ‖q.coeff f‖ := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [Finsupp.sum, MvPolynomial.finsupp_support_eq_support, complexCoeffL1_monomial, norm_mul] using
        complexCoeffL1_sum_le q.support
          (fun f => MvPolynomial.monomial (e + f) (p.coeff e * q.coeff f))
    _ = complexCoeffL1 p * complexCoeffL1 q := by
      simp only [complexCoeffL1, Finset.sum_mul_sum]

lemma complexCoeffL1_smul (c : ℂ) (p : MvPolynomial (Fin m) ℂ) :
    complexCoeffL1 (c • p) = ‖c‖ * complexCoeffL1 p := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · simp only [complexCoeffL1, MvPolynomial.support_smul_eq hc,
      MvPolynomial.coeff_smul, norm_smul, Finset.mul_sum]

/-- Exact norm for a finitely supported sum with no repeated exponent vectors. -/
lemma complexCoeffL1_sum_monomials (s : Finset (Fin m →₀ ℕ)) (c : (Fin m →₀ ℕ) → ℂ) :
    complexCoeffL1 (∑ e ∈ s, MvPolynomial.monomial e (c e)) = ∑ e ∈ s, ‖c e‖ := by
  classical
  have hs : (∑ e ∈ s, MvPolynomial.monomial e (c e)).support ⊆ s := by
    intro e he
    by_contra hen
    have hz : (∑ f ∈ s, MvPolynomial.monomial f (c f)).coeff e = 0 := by
      simp [MvPolynomial.coeff_monomial, hen]
    exact (MvPolynomial.mem_support_iff.mp he) hz
  rw [complexCoeffL1_eq_sum_of_support_subset _ s hs]
  apply Finset.sum_congr rfl
  intro e he
  simp [MvPolynomial.coeff_monomial, he]

/-- A type synonym separates the ℓ¹ norm from any other polynomial topology. -/
def ComplexPolyL1 (m : ℕ) := MvPolynomial (Fin m) ℂ

namespace ComplexPolyL1

instance : CommRing (ComplexPolyL1 m) := inferInstanceAs (CommRing (MvPolynomial (Fin m) ℂ))
instance : Algebra ℂ (ComplexPolyL1 m) :=
  inferInstanceAs (Algebra ℂ (MvPolynomial (Fin m) ℂ))

/-- The identity algebra equivalence, viewed in the coefficient-normed type. -/
def ofPolynomial : MvPolynomial (Fin m) ℂ ≃ₐ[ℂ] ComplexPolyL1 m :=
  AlgEquiv.refl

/-- The coefficient ring norm. -/
def ringNorm : RingNorm (ComplexPolyL1 m) where
  toFun := complexCoeffL1
  map_zero' := complexCoeffL1_zero
  add_le' := complexCoeffL1_add_le
  neg' := complexCoeffL1_neg
  mul_le' := complexCoeffL1_mul_le
  eq_zero_of_map_eq_zero' := complexCoeffL1_eq_zero

instance : NormedCommRing (ComplexPolyL1 m) where
  __ := ringNorm.toNormedRing
  __ := (inferInstance : CommRing (ComplexPolyL1 m))

instance : NormedAlgebra ℂ (ComplexPolyL1 m) where
  norm_smul_le c p := (complexCoeffL1_smul c p).le

theorem norm_eq (p : ComplexPolyL1 m) : ‖p‖ = complexCoeffL1 p := rfl

@[simp] theorem norm_ofPolynomial (p : MvPolynomial (Fin m) ℂ) :
    ‖ofPolynomial p‖ = complexCoeffL1 p := rfl

instance : NormOneClass (ComplexPolyL1 m) where
  norm_one := complexCoeffL1_one

@[simp] theorem norm_X (i : Fin m) :
    ‖ofPolynomial (MvPolynomial.X i)‖ = 1 := complexCoeffL1_X i

end ComplexPolyL1

end MultivariateWiener
