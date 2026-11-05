import LocalAtlasCompleteness
import GridCheckerRealization

noncomputable section
open scoped BigOperators
namespace LocalAtlas
open MultivariateInputExpr MultivariateBezoutRealization GridCheckerRealization

/-- The absence of a common real zero alone produces a finite rational grid
of accepted one-state systems and all their stationary Bézout outputs. -/
theorem exists_checked_grid {m k : ℕ} (S : Fin k → InputPoly m)
    (hS : NoCommonRealZero S) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : Fin m → Fin N,
      let c : Fin m → ℚ := fun j => gridCenter N (a j)
      let A := localFamily S c (1/N)
      ∃ T : Fin k → InputPoly m,
        rate A T < 1 ∧
        BoxContractionChecker.check (stateMap A T) 1 (radius A T) (rate A T) = true ∧
        ∀ v ∈ BoxContractionChecker.boxSet m 1, ∃! x : Fin 1 → ℝ,
          x ∈ BoxContractionChecker.boxSet 1 (radius A T) ∧
          BoxContractionChecker.map (stateMap A T) v x = x ∧
          ∑ j, realEval (S j) (fun l => (c l:ℝ) + ((1/(N:ℚ):ℚ):ℝ)*v l) *
            (outputSyntax T j).eval v x = 1 := by
  obtain ⟨N,hN,hcert⟩ := no_common_real_zero_has_grid S hS
  refine ⟨N,hN,?_⟩
  intro a
  obtain ⟨T,hRate,hCheck,hReal⟩ := exists_checked_witness S
    (fun j => gridCenter N (a j)) (1/N) (hcert a)
  refine ⟨T,hRate,hCheck,?_⟩
  simpa only [localFamily, realEval_affineSubstitution] using hReal

end LocalAtlas
