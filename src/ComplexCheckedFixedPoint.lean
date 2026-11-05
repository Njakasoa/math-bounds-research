import ComplexPolynomialBounds
import BoxContractionChecker

/-!
# Complex fixed points of every accepted absolute box certificate

The unchanged rational checker also certifies a self-map and a contraction on
closed complex polydiscs. Banach is applied to the complete closed-ball subtype,
so the theorem includes zero state dimension and zero radius. No complex
analytic continuation or holomorphic limit theorem is used here.
-/
namespace ComplexCheckedFixedPoint

open BoxPolynomialBounds

variable {m n : ℕ}

/-- The complex polydisc, represented by the closed supremum-norm ball. -/
def boxSet (d : ℕ) (r : ℚ) : Set (Fin d → ℂ) :=
  Metric.closedBall 0 (r : ℝ)

/-- Complex interpretation of the same checked polynomial syntax. -/
noncomputable def map (P : Fin n → Expr m n) (u : Fin m → ℂ) (x : Fin n → ℂ) :
    Fin n → ℂ := fun i => (P i).evalComplex u x

theorem boxSet_nonempty {d : ℕ} {r : ℚ} (hr : 0 ≤ r) :
    (boxSet d r).Nonempty := by
  exact ⟨0, Metric.mem_closedBall_self (by exact_mod_cast hr)⟩

theorem boxSet_isClosed (d : ℕ) (r : ℚ) : IsClosed (boxSet d r) :=
  Metric.isClosed_closedBall

theorem boxSet_isComplete (d : ℕ) (r : ℚ) : IsComplete (boxSet d r) :=
  (boxSet_isClosed d r).isComplete

theorem coordinate_bound {d : ℕ} {r : ℚ} {x : Fin d → ℂ}
    (hx : x ∈ boxSet d r) (i : Fin d) : ‖x i‖ ≤ (r : ℝ) := by
  have h := dist_le_pi_dist x (0 : Fin d → ℂ) i
  simp only [Pi.zero_apply, dist_zero_right] at h
  exact h.trans (by simpa only [boxSet, Metric.mem_closedBall, dist_zero_right] using hx)

theorem mem_boxSet_iff {d : ℕ} {r : ℚ} (hr : 0 ≤ r) (x : Fin d → ℂ) :
    x ∈ boxSet d r ↔ ∀ i, ‖x i‖ ≤ (r : ℝ) := by
  constructor
  · exact fun hx i => coordinate_bound hx i
  · intro hx
    apply (dist_pi_le_iff (show (0 : ℝ) ≤ r by exact_mod_cast hr)).2
    simpa only [Pi.zero_apply, dist_zero_right] using hx

/-- The rational amplitude checks also establish complex invariance. -/
theorem map_self (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : BoxContractionChecker.check P B r K = true)
    (u : Fin m → ℂ) (hu : u ∈ boxSet m B) :
    Set.MapsTo (map P u) (boxSet n r) (boxSet n r) := by
  obtain ⟨hB, hr, _, _, hbounds⟩ :=
    (BoxContractionChecker.check_iff P B r K).mp hcheck
  intro x hx
  apply (mem_boxSet_iff hr _).mpr
  intro i
  exact ((P i).evalComplex_norm_le_amp hB hr (coordinate_bound hu) (coordinate_bound hx)).trans
    (by exact_mod_cast (hbounds i).1)

/-- The same rational Lipschitz rate bounds the complex state map. -/
theorem map_dist_le (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : BoxContractionChecker.check P B r K = true)
    (u : Fin m → ℂ) (hu : u ∈ boxSet m B)
    (x : Fin n → ℂ) (hx : x ∈ boxSet n r)
    (y : Fin n → ℂ) (hy : y ∈ boxSet n r) :
    dist (map P u x) (map P u y) ≤ (K : ℝ) * dist x y := by
  obtain ⟨hB, hr, hK, _, hbounds⟩ :=
    (BoxContractionChecker.check_iff P B r K).mp hcheck
  apply (dist_pi_le_iff (mul_nonneg (by exact_mod_cast hK) dist_nonneg)).mpr
  intro i
  change dist ((P i).evalComplex u x) ((P i).evalComplex u y) ≤ _
  rw [dist_eq_norm]
  exact ((P i).evalComplex_sub_norm_le_lip hB hr (coordinate_bound hu)
    (coordinate_bound hx) (coordinate_bound hy)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (hbounds i).2) dist_nonneg)

/-- An accepted certificate yields a unique fixed point in every complex input
fiber, uniformly over the full closed input polydisc. -/
theorem checked_uniform_existsUnique (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : BoxContractionChecker.check P B r K = true) :
    ∀ u ∈ boxSet m B, ∃! x : boxSet n r, map P u x = x := by
  obtain ⟨_, hr, hK0, hK1, _⟩ :=
    (BoxContractionChecker.check_iff P B r K).mp hcheck
  let κ : NNReal := ⟨(K : ℝ), by exact_mod_cast hK0⟩
  have hκ : κ < 1 := by
    change (K : ℝ) < 1
    exact_mod_cast hK1
  let : Nonempty (boxSet n r) := (boxSet_nonempty hr).to_subtype
  let : CompleteSpace (boxSet n r) := (boxSet_isComplete n r).completeSpace_coe
  intro u hu
  let g : boxSet n r → boxSet n r := fun x => ⟨map P u x, map_self P hcheck u hu x.property⟩
  have hg : ContractingWith κ g := by
    refine ⟨hκ, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact map_dist_le P hcheck u hu x x.property y y.property
  refine ⟨ContractingWith.fixedPoint g hg, ?_, ?_⟩
  · exact congrArg Subtype.val hg.fixedPoint_isFixedPt
  · intro y hy
    apply hg.fixedPoint_unique
    exact Subtype.ext hy

/-- Ambient-space interface, with uniqueness restricted to the certified ball. -/
theorem checked_uniform_existsUnique_mem (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : BoxContractionChecker.check P B r K = true) :
    ∀ u ∈ boxSet m B, ∃! x : Fin n → ℂ, x ∈ boxSet n r ∧ map P u x = x := by
  intro u hu
  obtain ⟨x, hx, huniq⟩ := checked_uniform_existsUnique P hcheck u hu
  refine ⟨x, ⟨x.property, hx⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (huniq ⟨y, hy.1⟩ hy.2)

/-- Coordinatewise interface for evaluating polynomial output identities. -/
theorem checked_exists_coordinates (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : BoxContractionChecker.check P B r K = true)
    (u : Fin m → ℂ) (hu : ∀ i, ‖u i‖ ≤ (B : ℝ)) :
    ∃ x : Fin n → ℂ, (∀ i, ‖x i‖ ≤ (r : ℝ)) ∧
      ∀ i, (P i).evalComplex u x = x i := by
  obtain ⟨hB, hr, _⟩ := (BoxContractionChecker.check_iff P B r K).mp hcheck
  obtain ⟨x, hx, _⟩ := checked_uniform_existsUnique_mem P hcheck u ((mem_boxSet_iff hB u).mpr hu)
  exact ⟨x, (mem_boxSet_iff hr x).mp hx.1, fun i => congrFun hx.2 i⟩

end ComplexCheckedFixedPoint
