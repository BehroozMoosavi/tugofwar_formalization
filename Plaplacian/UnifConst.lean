/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.HessNorm

/-!
# The localization constants, uniformly

The localization bound carries the Hessian norm in its numerator and the
gradient norm in its denominator, both at the base point. At a moving base
point near the maximum, the first must be bounded above and the second
bounded below.

The Hessian is bounded through the flat second derivative, whose norm agrees
with the curried one. The gradient is bounded below by continuity, being
nonzero at the maximum, so that near it the gradient norm stays above half its
value there and the localization denominator stays away from zero.

## Main results

- hess_bound_uniform
- grad_lower_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The localization's constants, uniformly

The localization bound carries two quantities at the base point: the Hessian
norm in the numerator and the gradient norm in the denominator. At a moving
base point near the maximum, both need uniform control --- the first bounded
above, the second bounded below.

The Hessian is bounded through the flat second derivative. The gradient is
bounded below by continuity, the gradient being nonzero at the maximum: near
it, the gradient's norm stays above half its value there.
-/


/-- **The Hessian is uniformly bounded on a ball.** -/
theorem hess_bound_uniform {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x₀ : EuclSpace d) (R : ℝ) :
    ∃ H : ℝ, ∀ y ∈ closedBall x₀ R, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ H := by
  obtain ⟨C, hC⟩ := exists_bound_all_orders hφ x₀ R
  refine ⟨C, fun y hy => ?_⟩
  rw [norm_hess_eq_flat]
  exact hC y hy 2 (by norm_num)

/-- **The gradient is uniformly bounded below near the maximum.** -/
theorem grad_lower_uniform {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hx : gradient φ x₀ ≠ 0) :
    ∃ ρ > 0, ∀ y ∈ ball x₀ ρ,
      ‖gradient φ x₀‖ / 2 < ‖gradient φ y‖ := by
  have hpos : (0:ℝ) < ‖gradient φ x₀‖ := norm_pos_iff.2 hx
  have hcont : ContinuousAt (fun y => ‖gradient φ y‖) x₀ :=
    (continuous_gradient hφ).norm.continuousAt
  have hev : ∀ᶠ y in nhds x₀, ‖gradient φ x₀‖ / 2 < ‖gradient φ y‖ :=
    hcont.eventually (eventually_gt_nhds (by linarith))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hball⟩ := hev
  exact ⟨ρ, hρ, fun y hy => hball hy⟩

end

end PLaplacian
