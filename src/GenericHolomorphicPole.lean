import PolynomialReadoutAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# A generic interior-pole obstruction

A holomorphic function on the unit disc cannot agree, on a real set with an
interior accumulation point, with a rational polynomial quotient having a
non-removable pole in that disc. Both numerator and denominator are arbitrary
rational univariate multivariate polynomials. The proof clears the denominator
only where it is known to be nonzero, then applies the analytic identity theorem.
-/
namespace GenericHolomorphicPole

open Set Filter
open scoped Topology

abbrev InputPoly := MvPolynomial (Fin 1) ℚ

noncomputable def realEval (Q : InputPoly) (u : ℝ) : ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (fun _ => u) Q

noncomputable def complexEval (Q : InputPoly) (z : ℂ) : ℂ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℂ) (fun _ => z) Q

lemma complexEval_ofReal (Q : InputPoly) (u : ℝ) :
    complexEval Q (u : ℂ) = (realEval Q u : ℂ) :=
  PolynomialReadoutAnalytic.eval_ofReal Q (fun _ => u)

lemma differentiableOn_complexEval (Q : InputPoly) (U : Set ℂ) :
    DifferentiableOn ℂ (complexEval Q) U :=
  PolynomialReadoutAnalytic.differentiableOn_eval Q (fun z _ => z)
    (fun _ => differentiableOn_id)

/-- Clearing a real, nonzero denominator commutes with the embedding into ℂ. -/
lemma cleared_identity (R S : InputPoly) (f : ℂ → ℂ) (u : ℝ)
    (hS : realEval S u ≠ 0)
    (hf : f (u : ℂ) = ((realEval R u / realEval S u : ℝ) : ℂ)) :
    complexEval S (u : ℂ) * f (u : ℂ) - complexEval R (u : ℂ) = 0 := by
  rw [hf, complexEval_ofReal, complexEval_ofReal]
  have h : realEval S u * (realEval R u / realEval S u) - realEval R u = 0 := by
    field_simp
    ring
  exact_mod_cast h

/-- Real accumulation transfers to accumulation of the cleared complex zeros. -/
lemma mem_closure_cleared_zeros (R S : InputPoly) (f : ℂ → ℂ)
    (E : Set ℝ) (a : ℝ) (hacc : a ∈ closure (E \ {a}))
    (hS : ∀ u ∈ E, realEval S u ≠ 0)
    (hreal : ∀ u ∈ E, f (u : ℂ) = ((realEval R u / realEval S u : ℝ) : ℂ)) :
    (a : ℂ) ∈ closure
      ({z : ℂ | complexEval S z * f z - complexEval R z = 0} \ {(a : ℂ)}) := by
  have hi : (a : ℂ) ∈ closure (Complex.ofReal '' (E \ {a})) :=
    mem_closure_image Complex.continuous_ofReal.continuousAt hacc
  apply closure_mono ?_ hi
  rintro z ⟨u, hu, rfl⟩
  refine ⟨cleared_identity R S f u (hS u hu.1) (hreal u hu.1), ?_⟩
  simpa only [mem_singleton_iff, Complex.ofReal_inj] using hu.2

/-- Generic pole obstruction from any real equality set with a real interior
accumulation point. No global nonvanishing or polynomial identity is assumed. -/
theorem no_holomorphic_extension_of_accumulation (R S : InputPoly) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (E : Set ℝ) (a : ℝ) (ha : (a : ℂ) ∈ Metric.ball 0 1)
    (hacc : a ∈ closure (E \ {a}))
    (hS : ∀ u ∈ E, realEval S u ≠ 0)
    (hreal : ∀ u ∈ E, f (u : ℂ) = ((realEval R u / realEval S u : ℝ) : ℂ))
    (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.ball 0 1)
    (hSz₀ : complexEval S z₀ = 0) (hRz₀ : complexEval R z₀ ≠ 0) : False := by
  let F : ℂ → ℂ := fun z => complexEval S z * f z - complexEval R z
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 1) :=
    (((differentiableOn_complexEval S _).mul hf).sub
      (differentiableOn_complexEval R _)).analyticOnNhd Metric.isOpen_ball
  have hzero : EqOn F 0 (Metric.ball (0 : ℂ) 1) :=
    hF.eqOn_zero_of_preconnected_of_mem_closure
      (convex_ball (0 : ℂ) 1).isPreconnected ha
      (mem_closure_cleared_zeros R S f E a hacc hS hreal)
  have hp := hzero hz₀
  change complexEval S z₀ * f z₀ - complexEval R z₀ = 0 at hp
  exact hRz₀ (by simpa only [hSz₀, zero_mul, zero_sub, neg_eq_zero] using hp)

/-- The midpoint of a nonempty open interval is an accumulation point after
removing that midpoint. This supplies an explicit, non-vacuous equality set. -/
lemma midpoint_mem_closure_punctured_Ioo (a b : ℝ) (hab : a < b) :
    (a + b) / 2 ∈ closure (Ioo a b \ {(a + b) / 2}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min ε ((b - a) / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by
    dsimp [δ]
    have := min_le_left ε ((b - a) / 2)
    linarith
  have hδb : δ < (b - a) / 2 := by
    dsimp [δ]
    have := min_le_right ε ((b - a) / 2)
    linarith
  refine ⟨(a + b) / 2 + δ, ⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simp only [mem_singleton_iff]
    linarith
  · rw [Real.dist_eq]
    have heq : (a + b) / 2 - ((a + b) / 2 + δ) = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδ]
    exact hδε

/-- Interval interface: any nonempty open interval inside the real unit
interval suffices, even when the denominator has zeros elsewhere on ℝ. -/
theorem no_holomorphic_extension_on_Ioo (R S : InputPoly) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (a b : ℝ) (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hS : ∀ u ∈ Ioo a b, realEval S u ≠ 0)
    (hreal : ∀ u ∈ Ioo a b,
      f (u : ℂ) = ((realEval R u / realEval S u : ℝ) : ℂ))
    (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.ball 0 1)
    (hSz₀ : complexEval S z₀ = 0) (hRz₀ : complexEval R z₀ ≠ 0) : False := by
  apply no_holomorphic_extension_of_accumulation R S f hf
    (Ioo a b) ((a + b) / 2) ?_
    (midpoint_mem_closure_punctured_Ioo a b hab) hS hreal z₀ hz₀ hSz₀ hRz₀
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

end GenericHolomorphicPole
