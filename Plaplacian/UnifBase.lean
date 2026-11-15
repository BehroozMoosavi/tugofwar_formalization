/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.NearFreq

@[expose] public section

/-!
# The third-derivative bound, uniform in the base point

The near-maximizer moves with the parameter, so the expansion error must be
small uniformly in the base point near the maximum.

At class C two that would need uniform continuity of the Hessian in the
operator norm, which is the topology problem that blocked three routes in the
third layer. At class C three it does not arise: the cubic bound goes through
the flat derivative representation, which supports norms, and it is uniform
in the base point at no cost. Every derivative up to order three is bounded
once, on the closed ball of twice the radius, and every base point within the
radius, with every increment of at most the radius, keeps its segment inside
that ball.

So the C three case of the convergence argument is the one free of the
topology obstruction, and it is the case taken here. Reducing the predicate's
C two test functions to C three is a separate step.

## Main results

- segment_mem_bigBall
- deriv_three_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The third-derivative bound, uniform in the base point

The near-maximizer moves with the parameter, so the expansion error must be
small uniformly in the base point near the maximum. At class C two that
needs uniform continuity of the Hessian in the operator norm --- the topology
problem that blocked three routes in the third layer.

At class C three it does not. The cubic bound goes through the flat
derivative representation, which supports norms, and it becomes uniform in
the base point at no cost: bound every derivative up to order three once, on
the closed ball of radius twice `R`, and then every base point within `R` of
the maximum, with every increment of size at most `R`, keeps the segment inside
that ball.

The constant is the same as for a single base point; only the ball over which
it is taken is larger.
-/


/-- A point of the segment from a base point near the maximum, with a small
increment, lies in the large ball. -/
theorem segment_mem_bigBall {x₀ y z : EuclSpace d} {R t : ℝ}
    (hy : y ∈ closedBall x₀ R) (hz : ‖z‖ ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    y + t • z ∈ closedBall x₀ (2 * R) := by
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  have htz : ‖t • z‖ ≤ ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  calc ‖y + t • z - x₀‖ = ‖(y - x₀) + t • z‖ := by congr 1; abel
    _ ≤ ‖y - x₀‖ + ‖t • z‖ := norm_add_le _ _
    _ ≤ R + R := add_le_add hy (le_trans htz hz)
    _ = 2 * R := by ring

/-- **The third-derivative bound, uniform in the base point.** -/
theorem deriv_three_uniform {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x₀ : EuclSpace d) (R : ℝ) :
    ∃ C : ℝ, ∀ y ∈ closedBall x₀ R, ∀ z : EuclSpace d, ‖z‖ ≤ R →
      ∀ t ∈ Icc (0:ℝ) 1,
        |deriv (deriv (deriv (fun s : ℝ => φ (y + s • z)))) t|
          ≤ 6 * C * ‖z‖ ^ 3 := by
  obtain ⟨C, hC⟩ := exists_bound_all_orders hφ x₀ (2 * R)
  refine ⟨C, fun y hy z hz t ht => ?_⟩
  have hmem := segment_mem_bigBall hy hz ht
  have hbd := norm_iteratedFDeriv_three_comp hφ y z t (hC _ hmem)
  rw [comp_line_eq] at hbd
  rw [← iteratedDeriv_three, ← norm_iteratedFDeriv_eq_abs_iteratedDeriv]
  exact hbd

end

end PLaplacian
