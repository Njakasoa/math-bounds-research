import LocalAtlasRational
import LocalAtlasRealEvaluation
import GridCoverage

noncomputable section
open scoped BigOperators
namespace LocalAtlas
open MultivariateInputExpr

def NoCommonRealZero {m k : ℕ} (S : Fin k → InputPoly m) : Prop :=
  ∀ u : Fin m → ℝ, (∀ j, |u j| ≤ 1) → ∃ i, realEval (S i) u ≠ 0

def ConstantGridCertificates {m k : ℕ} (S : Fin k → InputPoly m) (N : ℕ) : Prop :=
  0 < N ∧ ∀ a : Fin m → Fin N, ∃ i : Fin k, ∃ t : ℚ,
    coeffL1 (1 - affineSubstitution (S i) (fun j => gridCenter N (a j)) (1/N) *
      MvPolynomial.C t) < 1

theorem no_common_real_zero_has_grid {m k : ℕ} (S : Fin k → InputPoly m)
    (hS : NoCommonRealZero S) : ∃ N, ConstantGridCertificates S N := by
  classical
  obtain ⟨i₀, _⟩ := hS 0 (by simp)
  have hk : 0 < k := Fin.pos i₀
  obtain ⟨δ, hδ, hmargin⟩ := rational_family_margin hk S hS
  let C : ℚ := ∑ i, variationConstant (S i)
  have hCi (i : Fin k) : variationConstant (S i) ≤ C := by
    exact Finset.single_le_sum (fun j _ => variationConstant_nonneg (S j)) (Finset.mem_univ i)
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((C : ℝ)/δ) 1)
  have hN1 : (1:ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNposR : (0:ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hratio : (C:ℝ)/δ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hCN : (C:ℝ) < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hratio
  refine ⟨N, hNpos, ?_⟩
  intro a
  let c : Fin m → ℚ := fun j => gridCenter N (a j)
  have hcR (j : Fin m) : |(c j : ℝ)| ≤ 1 := gridCenter_mem N hNpos (a j)
  have hc (j : Fin m) : |c j| ≤ 1 := by exact_mod_cast hcR j
  obtain ⟨i, hi⟩ := hmargin (fun j => (c j : ℝ)) hcR
  rw [realEval_rational] at hi
  have hCiR : (variationConstant (S i):ℝ) ≤ (C:ℝ) := by exact_mod_cast hCi i
  have hsmallR : (1/(N:ℝ)) * (variationConstant (S i):ℝ) <
      |(MvPolynomial.eval c (S i):ℝ)| := by
    apply lt_of_lt_of_le _ hi
    have hd : (variationConstant (S i):ℝ)/(N:ℝ) < δ :=
      (div_lt_iff₀ hNposR).mpr (by linarith)
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hd
  have hsmall : (1/(N:ℚ)) * variationConstant (S i) < |MvPolynomial.eval c (S i)| := by
    have hcast : (((1/(N:ℚ))*variationConstant (S i):ℚ):ℝ) <
        ((|MvPolynomial.eval c (S i)|:ℚ):ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] using hsmallR
    exact_mod_cast hcast
  have hh : (0:ℚ) ≤ 1/N := by positivity
  have hh1 : (1:ℚ)/N ≤ 1 := by
    have hNr : (1:ℚ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos)
    exact (div_le_one (by positivity : (0:ℚ) < N)).mpr hNr
  exact ⟨i, (MvPolynomial.eval c (S i))⁻¹,
    normalized_residual_lt (S i) c (1/N) hc hh hh1 hsmall⟩

theorem realEval_affineSubstitution {m : ℕ} (p : InputPoly m)
    (c : Fin m → ℚ) (h : ℚ) (v : Fin m → ℝ) :
    realEval (affineSubstitution p c h) v =
      realEval p (fun j => (c j:ℝ) + (h:ℝ)*v j) := by
  have hcomp : (MvPolynomial.eval₂Hom (Rat.castHom ℝ) v).comp MvPolynomial.C = Rat.castHom ℝ := by
    ext r
    simp
  have he := MvPolynomial.eval₂_comp_left (MvPolynomial.eval₂Hom (Rat.castHom ℝ) v)
      MvPolynomial.C
      (fun i => MvPolynomial.C (c i) + MvPolynomial.C h * MvPolynomial.X i) p
  rw [hcomp] at he
  simpa [realEval, affineSubstitution, Function.comp_def] using he

theorem grid_has_no_common_real_zero {m k N : ℕ} (S : Fin k → InputPoly m)
    (hcert : ConstantGridCertificates S N) : NoCommonRealZero S := by
  classical
  intro u hu
  obtain ⟨a, v, hv, huv⟩ := grid_coverage m N hcert.1 u hu
  obtain ⟨i, t, ht⟩ := hcert.2 a
  refine ⟨i, ?_⟩
  intro hzero
  let c : Fin m → ℚ := fun j => gridCenter N (a j)
  let q : InputPoly m := 1-affineSubstitution (S i) c (1/N)*MvPolynomial.C t
  have heq : (fun j => (c j:ℝ) + ((1/(N:ℚ):ℚ):ℝ)*v j) = u := by
    funext j
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, c] using (huv j).symm
  have hlocal : realEval (affineSubstitution (S i) c (1/N)) v = 0 := by
    rw [realEval_affineSubstitution, heq, hzero]
  have heval : realEval q v = 1 := by
    simp only [q, realEval, map_sub, map_one, map_mul, MvPolynomial.eval₂Hom_C]
    change 1-realEval (affineSubstitution (S i) c (1/N)) v * (t:ℝ) = 1
    rw [hlocal]; ring
  have hb := realEval_abs_le_coeffL1 q v hv
  rw [heval] at hb
  have htr : (coeffL1 q:ℝ) < 1 := by exact_mod_cast ht
  norm_num at hb
  linarith

theorem no_common_real_zero_iff_grid {m k : ℕ} (S : Fin k → InputPoly m) :
    NoCommonRealZero S ↔ ∃ N, ConstantGridCertificates S N := by
  constructor
  · exact no_common_real_zero_has_grid S
  · rintro ⟨N,hN⟩
    exact grid_has_no_common_real_zero S hN

end LocalAtlas
