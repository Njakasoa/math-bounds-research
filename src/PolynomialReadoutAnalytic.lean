import ComplexCheckedFixedPoint
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Polynomial readout compatibility and holomorphy, independent of the
construction of the stationary selector. No output identity is assumed. -/
namespace PolynomialReadoutAnalytic
open BoxPolynomialBounds
variable {σ : Type*} {m n : ℕ}

/-- A rational polynomial evaluated along coordinatewise holomorphic curves
is holomorphic. The readout can be any MvPolynomial, not only an AST expression. -/
theorem differentiableOn_eval (H : MvPolynomial σ ℚ) {U : Set ℂ}
    (v : ℂ → σ → ℂ) (hv : ∀ i, DifferentiableOn ℂ (fun z => v z i) U) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval₂Hom (Rat.castHom ℂ) (v z) H) U := by
  induction H using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂Hom_C] using (differentiableOn_const ((Rat.castHom ℂ) c) :
      DifferentiableOn ℂ (fun _ : ℂ => (Rat.castHom ℂ) c) U)
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval₂Hom_X'] using hp.fun_mul (hv i)

/-- Real evaluation followed by the canonical embedding agrees with complex
evaluation of exactly the same rational polynomial. -/
theorem eval_ofReal (H : MvPolynomial σ ℚ) (v : σ → ℝ) :
    MvPolynomial.eval₂Hom (Rat.castHom ℂ) (fun i => (v i : ℂ)) H =
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) v H : ℂ) := by
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Complex.ofReal_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval₂Hom_X', Complex.ofReal_mul, hp]

lemma complex_box_of_real_box {d : ℕ} {r : ℚ} {x : Fin d → ℝ}
    (hr : 0 ≤ r) (hx : x ∈ BoxContractionChecker.boxSet d r) :
    (fun i => (x i : ℂ)) ∈ ComplexCheckedFixedPoint.boxSet d r := by
  apply (ComplexCheckedFixedPoint.mem_boxSet_iff hr _).mpr
  intro i
  simpa only [Complex.norm_real, Real.norm_eq_abs] using BoxContractionChecker.coordinate_bound hx i

/-- Uniqueness in the complex certified box identifies a complex fixed point
with every real in-box fixed point, after embedding. No conjugation or choice
of a separate analytic branch is hidden in this comparison. -/
theorem complex_fixed_matches_real (P : Fin n → Expr m n) {B r K : ℚ}
    (hc : BoxContractionChecker.check P B r K = true)
    (u : Fin m → ℝ) (hu : u ∈ BoxContractionChecker.boxSet m B)
    (x : Fin n → ℝ) (hx : x ∈ BoxContractionChecker.boxSet n r)
    (hfix : BoxContractionChecker.map P u x = x)
    (p : Fin n → ℂ) (hp : p ∈ ComplexCheckedFixedPoint.boxSet n r)
    (hpfix : ComplexCheckedFixedPoint.map P (fun i => (u i : ℂ)) p = p) :
    p = fun i => (x i : ℂ) := by
  obtain ⟨hB,hr,_⟩ := (BoxContractionChecker.check_iff P B r K).mp hc
  have huc := complex_box_of_real_box hB hu
  have hxc := complex_box_of_real_box hr hx
  have hcf : ComplexCheckedFixedPoint.map P (fun i => (u i : ℂ)) (fun i => (x i : ℂ)) =
      fun i => (x i : ℂ) := by
    funext i
    have hi := congrFun hfix i
    change (P i).eval u x = x i at hi
    change (P i).evalComplex (fun i => (u i : ℂ)) (fun i => (x i : ℂ)) = (x i : ℂ)
    rw [Expr.evalComplex_ofReal, hi]
  obtain ⟨w, _, hwuniq⟩ := ComplexCheckedFixedPoint.checked_uniform_existsUnique_mem P hc
    (fun i => (u i : ℂ)) huc
  exact (hwuniq p ⟨hp,hpfix⟩).trans (hwuniq _ ⟨hxc,hcf⟩).symm

end PolynomialReadoutAnalytic
