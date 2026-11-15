/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ErrRate

@[expose] public section

/-!
# The error under the average

The average expansion carries the Taylor error as an average over the ball.
The cubic rate bounds the integrand by a constant times epsilon cubed
throughout the ball, since the increment there has norm at most epsilon.

The constant is taken as a maximum with zero: the cubic bound could in
principle have a negative constant, nothing in its statement excluding that,
and the step from the cube of the increment to the cube of epsilon requires
nonnegativity to preserve the inequality.

## Main results

- taylorErr_le_on_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The error under the average

The average expansion carries the error as `⨍_{B ε 0} taylorErr φ x z`.
`taylorErr_le_cubic` bounds the integrand by `K ‖z‖³ ≤ K ε³` on the ball, so
the average is bounded by the same --- an average of a bounded function being
bounded.
-/


/-- The integrand, bounded pointwise on the ball. -/
theorem taylorErr_le_on_ball {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) {ε : ℝ} (_hε : 0 < ε) :
    ∃ K : ℝ, ∀ z ∈ ball (0 : EuclSpace d) ε,
      |taylorErr φ x z| ≤ K * ε ^ 3 := by
  obtain ⟨K, hK⟩ := taylorErr_le_cubic hφ x ε
  refine ⟨max K 0, fun z hz => ?_⟩
  have hzn : ‖z‖ ≤ ε := by
    rw [mem_ball, dist_zero_right] at hz
    exact le_of_lt hz
  have h1 := hK z hzn
  have hz3 : ‖z‖ ^ 3 ≤ ε ^ 3 := by
    have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    have hεnn : (0:ℝ) ≤ ε := le_trans h0 hzn
    nlinarith [hzn, h0, hεnn, sq_nonneg (‖z‖ - ε), sq_nonneg (‖z‖ + ε)]
  have hKle : K ≤ max K 0 := le_max_left _ _
  have hK0 : (0:ℝ) ≤ max K 0 := le_max_right _ _
  have hz3nn : (0:ℝ) ≤ ‖z‖ ^ 3 := by positivity
  nlinarith [h1, hz3, hKle, hK0, hz3nn]

end

end PLaplacian
