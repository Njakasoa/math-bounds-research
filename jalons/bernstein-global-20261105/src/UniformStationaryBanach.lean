import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Uniform stationary existence from a residual contraction

For a fixed parameter `θ`, the residual map is `x ↦ x - C (F θ u x)`.
The input type is arbitrary: it need not be finite or discretized. The same
constant `K < 1` controls all admissible inputs, but only on `stateSet`.

The main theorem constructs a fixed point with `ContractingWith.fixedPoint` on
the complete, nonempty subtype `stateSet`. Injectivity of the linear map `C`
turns fixed points into zeros of `F θ u`. Existence of a stationary state is
therefore a conclusion, not a hypothesis. Completeness can be supplied directly,
or obtained from closedness in a complete normed space.

These are analytic existence theorems. They do not provide a finite exact solver,
a polynomial certificate of the Lipschitz hypotheses, or continuous-time ODE
stability. The optional convergence result concerns residual-map iteration only.
-/

namespace UniformStationaryBanach

open Function Filter
open scoped Topology

variable {Θ U E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The preconditioned residual self-map associated with the stationarity equation. -/
def residualMap (F : Θ → U → E → E) (C : E →ₗ[ℝ] E) (θ : Θ) (u : U) (x : E) : E :=
  x - C (F θ u x)

/-- Injectivity is essential: a zero residual correction must imply a zero field. -/
theorem residualMap_fixedPoint_iff (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (u : U) (x : E) :
    IsFixedPt (residualMap F C θ u) x ↔ F θ u x = 0 := by
  change x - C (F θ u x) = x ↔ F θ u x = 0
  rw [sub_eq_self, C.map_eq_zero_iff hC]

/-- Restriction to the invariant state set. No global contraction is required. -/
def restrictedResidual (F : Θ → U → E → E) (C : E →ₗ[ℝ] E) (θ : Θ)
    (stateSet : Set E) (u : U)
    (hself : Set.MapsTo (residualMap F C θ u) stateSet stateSet) :
    stateSet → stateSet := fun x => ⟨residualMap F C θ u x, hself x.property⟩

theorem restrictedResidual_fixedPoint_iff (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (stateSet : Set E) (u : U)
    (hself : Set.MapsTo (residualMap F C θ u) stateSet stateSet) (x : stateSet) :
    IsFixedPt (restrictedResidual F C θ stateSet u hself) x ↔ F θ u x = 0 := by
  change (⟨residualMap F C θ u x, hself x.property⟩ : stateSet) = x ↔ _
  rw [Subtype.ext_iff]
  exact residualMap_fixedPoint_iff F C hC θ u x

/-- The distance inequality on the state set is exactly the needed contraction. -/
theorem restrictedResidual_contracting (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (θ : Θ) (stateSet : Set E) (u : U) {K : NNReal} (hK : K < 1)
    (hself : Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ContractingWith K (restrictedResidual F C θ stateSet u hself) := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  exact hLip x x.property y y.property

/-- Banach supplies existence and uniqueness for every admissible input.
The constant `K` and the parameter `θ` are fixed before quantifying over inputs. -/
theorem uniform_existsUnique_stationary (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hcomplete : IsComplete stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ∀ u ∈ inputSet, ∃! x : stateSet, F θ u x = 0 := by
  let : Nonempty stateSet := hne.to_subtype
  let : CompleteSpace stateSet := hcomplete.completeSpace_coe
  intro u hu
  let g := restrictedResidual F C θ stateSet u (hself u hu)
  have hg : ContractingWith K g :=
    restrictedResidual_contracting F C θ stateSet u hK (hself u hu) (hLip u hu)
  refine ⟨ContractingWith.fixedPoint g hg, ?_, ?_⟩
  · exact (restrictedResidual_fixedPoint_iff F C hC θ stateSet u (hself u hu) _).mp
      hg.fixedPoint_isFixedPt
  · intro y hy
    exact hg.fixedPoint_unique
      ((restrictedResidual_fixedPoint_iff F C hC θ stateSet u (hself u hu) y).mpr hy)

/-- Ambient-space formulation, with uniqueness among states in `stateSet`. -/
theorem uniform_existsUnique_stationary_mem (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hcomplete : IsComplete stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ∀ u ∈ inputSet, ∃! x : E, x ∈ stateSet ∧ F θ u x = 0 := by
  intro u hu
  obtain ⟨x, hx, huniq⟩ :=
    uniform_existsUnique_stationary F C hC θ inputSet stateSet hne hcomplete hK hself hLip u hu
  refine ⟨x, ⟨x.property, hx⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (huniq ⟨y, hy.1⟩ hy.2)

/-- Convenient interface when the uniform contraction is given as `LipschitzOnWith`. -/
theorem uniform_existsUnique_stationary_of_lipschitzOnWith
    (F : Θ → U → E → E) (C : E →ₗ[ℝ] E) (hC : Function.Injective C)
    (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hcomplete : IsComplete stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, LipschitzOnWith K (residualMap F C θ u) stateSet) :
    ∀ u ∈ inputSet, ∃! x : stateSet, F θ u x = 0 :=
  uniform_existsUnique_stationary F C hC θ inputSet stateSet hne hcomplete hK hself
    (fun u hu => (hLip u hu).dist_le_mul)

/-- Ambient-space interface for `LipschitzOnWith`. -/
theorem uniform_existsUnique_stationary_mem_of_lipschitzOnWith
    (F : Θ → U → E → E) (C : E →ₗ[ℝ] E) (hC : Function.Injective C)
    (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hcomplete : IsComplete stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, LipschitzOnWith K (residualMap F C θ u) stateSet) :
    ∀ u ∈ inputSet, ∃! x : E, x ∈ stateSet ∧ F θ u x = 0 :=
  uniform_existsUnique_stationary_mem F C hC θ inputSet stateSet hne hcomplete hK hself
    (fun u hu => (hLip u hu).dist_le_mul)

/-- Closed-state-set corollary in a complete ambient space. -/
theorem uniform_existsUnique_stationary_of_isClosed [CompleteSpace E]
    (F : Θ → U → E → E) (C : E →ₗ[ℝ] E) (hC : Function.Injective C)
    (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hclosed : IsClosed stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ∀ u ∈ inputSet, ∃! x : stateSet, F θ u x = 0 :=
  uniform_existsUnique_stationary F C hC θ inputSet stateSet hne hclosed.isComplete hK hself hLip

/-- Nonempty inputs make the uniform stationary conclusion explicitly non-vacuous. -/
theorem exists_admissible_stationary (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (inputSet : Set U) (stateSet : Set E)
    (hinput : inputSet.Nonempty) (hne : stateSet.Nonempty)
    (hcomplete : IsComplete stateSet) {K : NNReal} (hK : K < 1)
    (hself : ∀ u ∈ inputSet, Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ u ∈ inputSet, ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ∃ u ∈ inputSet, ∃ x ∈ stateSet, F θ u x = 0 := by
  obtain ⟨u, hu⟩ := hinput
  obtain ⟨x, hx, _⟩ :=
    uniform_existsUnique_stationary_mem F C hC θ inputSet stateSet hne hcomplete hK hself hLip u hu
  exact ⟨u, hu, x, hx.1, hx.2⟩

/-- Banach iteration converges to the unique stationary state, with a geometric
error estimate. This is discrete residual iteration, not ODE stability. -/
theorem exists_stationary_with_iterate_convergence (F : Θ → U → E → E) (C : E →ₗ[ℝ] E)
    (hC : Function.Injective C) (θ : Θ) (stateSet : Set E)
    (hne : stateSet.Nonempty) (hcomplete : IsComplete stateSet) (u : U)
    {K : NNReal} (hK : K < 1)
    (hself : Set.MapsTo (residualMap F C θ u) stateSet stateSet)
    (hLip : ∀ x ∈ stateSet, ∀ y ∈ stateSet,
      dist (residualMap F C θ u x) (residualMap F C θ u y) ≤ (K : ℝ) * dist x y) :
    ∃ xstar : stateSet, F θ u xstar = 0 ∧
      (∀ y : stateSet, F θ u y = 0 → y = xstar) ∧
      ∀ x : stateSet,
        Tendsto (fun n => (restrictedResidual F C θ stateSet u hself)^[n] x)
          atTop (𝓝 xstar) ∧
        ∀ n : ℕ,
          dist ((restrictedResidual F C θ stateSet u hself)^[n] x) xstar ≤
            dist x (restrictedResidual F C θ stateSet u hself x) * (K : ℝ) ^ n / (1 - K) := by
  let : Nonempty stateSet := hne.to_subtype
  let : CompleteSpace stateSet := hcomplete.completeSpace_coe
  let g := restrictedResidual F C θ stateSet u hself
  have hg : ContractingWith K g :=
    restrictedResidual_contracting F C θ stateSet u hK hself hLip
  refine ⟨ContractingWith.fixedPoint g hg, ?_, ?_, ?_⟩
  · exact (restrictedResidual_fixedPoint_iff F C hC θ stateSet u hself _).mp
      hg.fixedPoint_isFixedPt
  · intro y hy
    exact hg.fixedPoint_unique
      ((restrictedResidual_fixedPoint_iff F C hC θ stateSet u hself y).mpr hy)
  · intro x
    exact ⟨hg.tendsto_iterate_fixedPoint x, hg.apriori_dist_iterate_fixedPoint_le x⟩

end UniformStationaryBanach
