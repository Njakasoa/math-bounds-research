import BoxPolynomialBounds
import UniformStationaryBanach

/-!
# An executable box-contraction checker with uniform stationary soundness

The input consists solely of finite polynomial syntax and rational numbers.
`check` verifies rational magnitude and Lipschitz bounds; it has no oracle,
existence premise, derivative bound premise, or semantic proposition as input.
A successful check proves invariance and a uniform contraction on a complete,
nonempty closed box. Banach then supplies a unique stationary state for every
input in the real input box. The conclusion is local to the certified state box.
The field is `x - map P u x`, with identity preconditioner, so its residual map is
exactly the supplied polynomial map. This is not a continuous-time stability claim.
-/
namespace BoxContractionChecker

open BoxPolynomialBounds

variable {m n : ℕ}

/-- Finite rational conditions checked by `check`. -/
def Conditions (P : Fin n → Expr m n) (B r K : ℚ) : Prop :=
  0 ≤ B ∧ 0 ≤ r ∧ 0 ≤ K ∧ K < 1 ∧
    ∀ i, (P i).amp B r ≤ r ∧ (P i).lip B r ≤ K

/-- Total executable checker; all quantifiers range over finite indices. -/
def check (P : Fin n → Expr m n) (B r K : ℚ) : Bool :=
  decide (0 ≤ B ∧ 0 ≤ r ∧ 0 ≤ K ∧ K < 1 ∧
    ∀ i, (P i).amp B r ≤ r ∧ (P i).lip B r ≤ K)

/-- Compute a sufficient uniform candidate rate without asking for one as input. -/
def autoRate (P : Fin n → Expr m n) (B r : ℚ) : ℚ :=
  (List.ofFn (fun i => (P i).lip B r)).foldl max 0

/-- Automatic-rate variant. The checker still verifies every row bound. -/
def autoCheck (P : Fin n → Expr m n) (B r : ℚ) : Bool :=
  check P B r (autoRate P B r)

@[simp] theorem check_iff (P : Fin n → Expr m n) (B r K : ℚ) :
    check P B r K = true ↔ Conditions P B r K := by
  simp only [check, decide_eq_true_eq, Conditions]

/-- The closed supremum-norm ball, hence the closed coordinate box. -/
def boxSet (d : ℕ) (r : ℚ) : Set (Fin d → ℝ) :=
  Metric.closedBall 0 (r : ℝ)

/-- Polynomial residual-map semantics. -/
noncomputable def map (P : Fin n → Expr m n) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ := fun i => (P i).eval u x

/-- The stationarity equation, with a trivial parameter type. -/
noncomputable def field (P : Fin n → Expr m n) (_θ : Unit)
    (u : Fin m → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  x - map P u x

theorem boxSet_nonempty {d : ℕ} {r : ℚ} (hr : 0 ≤ r) :
    (boxSet d r).Nonempty := by
  exact ⟨0, Metric.mem_closedBall_self (by exact_mod_cast hr)⟩

theorem boxSet_isClosed (d : ℕ) (r : ℚ) : IsClosed (boxSet d r) :=
  Metric.isClosed_closedBall

theorem boxSet_isComplete (d : ℕ) (r : ℚ) : IsComplete (boxSet d r) :=
  (boxSet_isClosed d r).isComplete

theorem coordinate_bound {d : ℕ} {r : ℚ} {x : Fin d → ℝ}
    (hx : x ∈ boxSet d r) (i : Fin d) : |x i| ≤ (r : ℝ) := by
  have h := dist_le_pi_dist x (0 : Fin d → ℝ) i
  simp only [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs] at h
  exact h.trans (by simpa only [boxSet, Metric.mem_closedBall, dist_zero_right] using hx)

theorem mem_boxSet_iff {d : ℕ} {r : ℚ} (hr : 0 ≤ r) (x : Fin d → ℝ) :
    x ∈ boxSet d r ↔ ∀ i, |x i| ≤ (r : ℝ) := by
  constructor
  · exact fun hx i => coordinate_bound hx i
  · intro hx
    apply (dist_pi_le_iff (show (0 : ℝ) ≤ r by exact_mod_cast hr)).2
    simpa only [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs] using hx

/-- Every checked map preserves its entire real state box for every admissible input. -/
theorem map_self (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) (u : Fin m → ℝ) (hu : u ∈ boxSet m B) :
    Set.MapsTo (map P u) (boxSet n r) (boxSet n r) := by
  obtain ⟨hB, hr, _, _, hbounds⟩ := (check_iff P B r K).mp hcheck
  intro x hx
  apply (mem_boxSet_iff hr _).mpr
  intro i
  exact ((P i).eval_abs_le_amp hB hr (coordinate_bound hu) (coordinate_bound hx)).trans
    (by exact_mod_cast (hbounds i).1)

/-- One rational Lipschitz bound works for all real inputs and state pairs in the boxes. -/
theorem map_dist_le (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) (u : Fin m → ℝ) (hu : u ∈ boxSet m B)
    (x : Fin n → ℝ) (hx : x ∈ boxSet n r)
    (y : Fin n → ℝ) (hy : y ∈ boxSet n r) :
    dist (map P u x) (map P u y) ≤ (K : ℝ) * dist x y := by
  obtain ⟨hB, hr, hK, _, hbounds⟩ := (check_iff P B r K).mp hcheck
  apply (dist_pi_le_iff (mul_nonneg (by exact_mod_cast hK) dist_nonneg)).mpr
  intro i
  change dist ((P i).eval u x) ((P i).eval u y) ≤ _
  rw [Real.dist_eq]
  exact ((P i).eval_sub_abs_le_lip hB hr (coordinate_bound hu)
    (coordinate_bound hx) (coordinate_bound hy)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (hbounds i).2) dist_nonneg)

/-- Identity preconditioning makes the residual equal to the checked polynomial map. -/
@[simp] theorem residual_eq_map (P : Fin n → Expr m n) (u : Fin m → ℝ) :
    UniformStationaryBanach.residualMap (field P) (LinearMap.id :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) () u = map P u := by
  funext x
  simp [UniformStationaryBanach.residualMap, field]

/-- Soundness of the executable checker: existence is derived, not assumed.
The same rational certificate covers every real input in the closed input box. -/
theorem checked_uniform_existsUnique (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) :
    ∀ u ∈ boxSet m B, ∃! x : boxSet n r, field P () u x = 0 := by
  obtain ⟨_, hr, hK0, hK1, _⟩ := (check_iff P B r K).mp hcheck
  let κ : NNReal := ⟨(K : ℝ), by exact_mod_cast hK0⟩
  have hκ : κ < 1 := by
    change (K : ℝ) < 1
    exact_mod_cast hK1
  apply UniformStationaryBanach.uniform_existsUnique_stationary
    (field P) (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (fun _ _ h => h) () (boxSet m B) (boxSet n r)
    (boxSet_nonempty hr) (boxSet_isComplete n r) hκ
  · intro u hu
    simpa only [residual_eq_map] using map_self P hcheck u hu
  · intro u hu x hx y hy
    rw [residual_eq_map]
    change dist (map P u x) (map P u y) ≤ (K : ℝ) * dist x y
    exact map_dist_le P hcheck u hu x hx y hy

/-- Equivalent ambient-space interface, with uniqueness restricted to the certified box. -/
theorem checked_uniform_existsUnique_mem (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) :
    ∀ u ∈ boxSet m B, ∃! x : Fin n → ℝ, x ∈ boxSet n r ∧ field P () u x = 0 := by
  intro u hu
  obtain ⟨x, hx, huniq⟩ := checked_uniform_existsUnique P hcheck u hu
  refine ⟨x, ⟨x.property, hx⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (huniq ⟨y, hy.1⟩ hy.2)

/-- A successful check also proves that the input and state domains are nonempty. -/
theorem checked_domains_nonempty (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) :
    (boxSet m B).Nonempty ∧ (boxSet n r).Nonempty := by
  obtain ⟨hB, hr, _⟩ := (check_iff P B r K).mp hcheck
  exact ⟨boxSet_nonempty hB, boxSet_nonempty hr⟩

/-- Explicitly non-vacuous stationary existence for at least one admissible input. -/
theorem checked_exists_admissible_stationary (P : Fin n → Expr m n) {B r K : ℚ}
    (hcheck : check P B r K = true) :
    ∃ u ∈ boxSet m B, ∃ x ∈ boxSet n r, field P () u x = 0 := by
  obtain ⟨u, hu⟩ := (checked_domains_nonempty P hcheck).1
  obtain ⟨x, hx, _⟩ := checked_uniform_existsUnique_mem P hcheck u hu
  exact ⟨u, hu, x, hx.1, hx.2⟩

/-- Automatic-rate soundness, requiring only polynomial syntax and two rational radii. -/
theorem autoChecked_uniform_existsUnique (P : Fin n → Expr m n) {B r : ℚ}
    (hcheck : autoCheck P B r = true) :
    ∀ u ∈ boxSet m B, ∃! x : boxSet n r, field P () u x = 0 :=
  checked_uniform_existsUnique P hcheck

end BoxContractionChecker
