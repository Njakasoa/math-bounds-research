import Mathlib

/-! A compact continuous finite family with no common zero has a uniform
positive component margin. This does not assume a certificate. -/
open scoped BigOperators
namespace LocalAtlas

theorem uniform_family_margin {X : Type*} [TopologicalSpace X]
    {k : ℕ} (hk : 0 < k) (K : Set X) (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin k → X → ℝ) (hf : ∀ i, ContinuousOn (f i) K)
    (hnz : ∀ u ∈ K, ∃ i, f i u ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ K, ∃ i, δ ≤ |f i u| := by
  classical
  let g : X → ℝ := fun u => ∑ i : Fin k, |f i u|
  have hg : ContinuousOn g K := by
    apply continuousOn_finsetSum
    intro i hi
    exact (hf i).abs
  have hgpos (u : X) (hu : u ∈ K) : 0 < g u := by
    obtain ⟨i, hi⟩ := hnz u hu
    exact Finset.sum_pos' (fun j _ => abs_nonneg (f j u))
      ⟨i, Finset.mem_univ _, abs_pos.mpr hi⟩
  obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hne hg
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  refine ⟨g u₀ / k, div_pos (hgpos u₀ hu₀) hkR, ?_⟩
  intro u hu
  by_contra hn
  push Not at hn
  have hlt : g u < ∑ _i : Fin k, g u₀ / k := by
    apply Finset.sum_lt_sum
    · intro i hi; exact le_of_lt (hn i)
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _, hn ⟨0, hk⟩⟩
  have heq : (∑ _i : Fin k, g u₀ / (k:ℝ)) = g u₀ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [heq] at hlt
  exact (not_lt_of_ge (hmin hu)) hlt

theorem polynomial_family_margin {m k : ℕ} (hk : 0 < k)
    (S : Fin k → MvPolynomial (Fin m) ℝ)
    (hnz : ∀ u : Fin m → ℝ, (∀ j, |u j| ≤ 1) → ∃ i, MvPolynomial.eval u (S i) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Fin m → ℝ,
      (∀ j, |u j| ≤ 1) → ∃ i, δ ≤ |MvPolynomial.eval u (S i)| := by
  let K : Set (Fin m → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hK : IsCompact K := isCompact_Icc
  have hne : K.Nonempty := ⟨0, by constructor <;> intro j <;> norm_num⟩
  have hmem (u : Fin m → ℝ) : u ∈ K ↔ ∀ j, |u j| ≤ 1 := by
    simp only [K, Set.mem_Icc, Pi.le_def, abs_le]
    aesop
  obtain ⟨δ, hδ, hbound⟩ := uniform_family_margin hk K hK hne
    (fun i u => MvPolynomial.eval u (S i))
    (fun i => (S i).continuous_eval.continuousOn)
    (fun u hu => hnz u ((hmem u).mp hu))
  exact ⟨δ, hδ, fun u hu => hbound u ((hmem u).mpr hu)⟩

end LocalAtlas
