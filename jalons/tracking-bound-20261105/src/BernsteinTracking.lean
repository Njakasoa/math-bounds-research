import BernsteinGlobalRealization
import ReciprocalVariation
import TrackingRecurrence

/-! Classical tracking estimate for the previously certified discrete map.
The input-variation hypothesis is essential. No sharpness claim is made. -/
namespace BernsteinTracking
open BernsteinGlobalRealization

noncomputable def target (u : ℝ) : ℝ := 1 / (1 + 4*u^2)
noncomputable def error (u : ℕ → ℝ) (x0 : ℝ) (n : ℕ) : ℝ :=
  |trajectory u x0 n - target (u n)|

theorem target_fixed {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    update u (target u) = target u := by
  have h : target u = equilibrium u := (equilibrium_target hu).symm
  rw [h]
  exact equilibrium_fixed hu

theorem error_nonneg (u : ℕ → ℝ) (x0 : ℝ) (n : ℕ) : 0 ≤ error u x0 n :=
  abs_nonneg _

theorem one_step (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (-1) 1)
    (x0 : ℝ) (n : ℕ) :
    error u x0 (n+1) ≤ (12/13 : ℝ) * error u x0 n +
      2 * |u (n+1) - u n| := by
  have hc := update_contracts (hu n) (trajectory u x0 n) (target (u n))
  rw [target_fixed (hu n)] at hc
  have hv := ReciprocalVariation.target_lipschitz (u n) (u (n+1))
  change |target (u n) - target (u (n+1))| ≤ 2 * |u n - u (n+1)| at hv
  rw [abs_sub_comm (u n) (u (n+1))] at hv
  unfold error
  rw [trajectory]
  calc
    |update (u n) (trajectory u x0 n) - target (u (n+1))| =
        |(update (u n) (trajectory u x0 n) - target (u n)) +
          (target (u n) - target (u (n+1)))| := by congr 1 <;> ring
    _ ≤ |update (u n) (trajectory u x0 n) - target (u n)| +
          |target (u n) - target (u (n+1))| := abs_add_le _ _
    _ ≤ (12/13 : ℝ) * |trajectory u x0 n - target (u n)| +
          2 * |u (n+1) - u n| := add_le_add hc hv

theorem variation_convolution (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (-1) 1) (x0 : ℝ) (n : ℕ) :
    error u x0 n ≤ (12/13 : ℝ)^n * error u x0 0 +
      ∑ j ∈ Finset.range n, (12/13 : ℝ)^(n-1-j) * (2*|u (j+1)-u j|) := by
  exact TrackingRecurrence.recurrence_convolution (by norm_num)
    (error u x0) (fun j => 2*|u (j+1)-u j|) (one_step u hu x0) n

theorem bounded_variation_finite (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (-1) 1) (x0 δ : ℝ)
    (hδ : ∀ n, |u (n+1) - u n| ≤ δ) (n : ℕ) :
    error u x0 n ≤ (12/13 : ℝ)^n * error u x0 0 +
      (2*δ) * (∑ j ∈ Finset.range n, (12/13 : ℝ)^j) := by
  apply TrackingRecurrence.recurrence_bounded_drift (by norm_num) (error u x0)
  intro k
  exact (one_step u hu x0 k).trans (by nlinarith [hδ k])

theorem bounded_variation_closed (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (-1) 1) (x0 δ : ℝ)
    (hδ : ∀ n, |u (n+1) - u n| ≤ δ) (n : ℕ) :
    error u x0 n ≤ (12/13 : ℝ)^n * error u x0 0 +
      26*δ*(1-(12/13 : ℝ)^n) := by
  have hs : ∀ k, error u x0 (k+1) ≤ (12/13 : ℝ)*error u x0 k + 2*δ := by
    intro k
    exact (one_step u hu x0 k).trans (by nlinarith [hδ k])
  have hb := TrackingRecurrence.recurrence_bounded_drift_closed
    (by norm_num : (0 : ℝ) ≤ 12/13) (by norm_num : (12/13 : ℝ) < 1)
    (error u x0) hs n
  convert hb using 1 <;> ring

theorem bounded_variation (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (-1) 1) (x0 δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ n, |u (n+1) - u n| ≤ δ) (n : ℕ) :
    error u x0 n ≤ (12/13 : ℝ)^n * error u x0 0 + 26*δ := by
  have hs : ∀ k, error u x0 (k+1) ≤ (12/13 : ℝ)*error u x0 k + 2*δ := by
    intro k
    exact (one_step u hu x0 k).trans (by nlinarith [hδ k])
  have hb := TrackingRecurrence.recurrence_uniform
    (by norm_num : (0 : ℝ) ≤ 12/13) (by norm_num : (12/13 : ℝ) < 1)
    (by positivity : 0 ≤ 2*δ) (error u x0) hs n
  convert hb using 1 <;> ring

#print axioms one_step
#print axioms bounded_variation_finite
#print axioms bounded_variation
end BernsteinTracking
