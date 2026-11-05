import LocalAtlasCompactMargin
import MultivariateInputExpr

noncomputable section
namespace LocalAtlas
open MultivariateInputExpr

theorem realEval_continuous {m : ℕ} (p : InputPoly m) :
    Continuous (realEval p) := by
  change Continuous (fun u => MvPolynomial.eval₂ (Rat.castHom ℝ) u p)
  simp_rw [MvPolynomial.eval₂_eq_eval_map]
  exact (p.map (Rat.castHom ℝ)).continuous_eval

theorem realEval_rational {m : ℕ} (p : InputPoly m) (c : Fin m → ℚ) :
    realEval p (fun j => (c j : ℝ)) = (MvPolynomial.eval c p : ℝ) := by
  exact (MvPolynomial.eval₂_comp_left (Rat.castHom ℝ) (RingHom.id ℚ) c p).symm

theorem rational_family_margin {m k : ℕ} (hk : 0 < k)
    (S : Fin k → InputPoly m)
    (hnz : ∀ u : Fin m → ℝ, (∀ j, |u j| ≤ 1) → ∃ i, realEval (S i) u ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Fin m → ℝ,
      (∀ j, |u j| ≤ 1) → ∃ i, δ ≤ |realEval (S i) u| := by
  let K : Set (Fin m → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hK : IsCompact K := isCompact_Icc
  have hne : K.Nonempty := ⟨0, by constructor <;> intro j <;> norm_num⟩
  have hmem (u : Fin m → ℝ) : u ∈ K ↔ ∀ j, |u j| ≤ 1 := by
    simp only [K, Set.mem_Icc, Pi.le_def, abs_le]
    aesop
  obtain ⟨δ, hδ, hbound⟩ := uniform_family_margin hk K hK hne
    (fun i => realEval (S i))
    (fun i => (realEval_continuous (S i)).continuousOn)
    (fun u hu => hnz u ((hmem u).mp hu))
  exact ⟨δ, hδ, fun u hu => hbound u ((hmem u).mpr hu)⟩

end LocalAtlas
