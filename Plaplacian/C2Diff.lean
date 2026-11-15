/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.PredForm

@[expose] public section

/-!
# The average error at C two

For every prescribed multiple there is a radius within which the Taylor error
is below that multiple of the squared radius throughout the ball. This is the
form the average expansion consumes, and it holds at C two.

The average expansion itself turned out to hold at C two already. Its C three
hypothesis was not load-bearing: every use of it was for continuity, which C
two supplies. Weakening it cost two one-line adjustments downstream, where a C
three hypothesis is passed to a lemma now asking only for C two.

The extreme-value half is different. It uses the Taylor bound at two specific
points rather than under an integral, and substituting the C two estimate
there is real work rather than a hypothesis edit.

## Main results

- taylorErr_le_on_ball_c2
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The differential inequality at C²

`diff_inequality` requires `C³`, because it calls the expansion. The
expansion's own error is now estimated at `C²`, so the inequality can be
restated: the operator's value is the polynomial plus an error, and the error
is controlled at `C²`.

What is needed is the expansion itself at `C²`. The expansion combines the
average and extreme-value halves; each was proved at `C³` because each used
the `C³` Taylor bound. Restating them needs the `C²` estimate substituted at
each use, which is where the two halves differ: the average half uses the
error under an integral, and the extreme-value half uses it at two points.

This file does the average half, which is the simpler of the two and needs
only the bound on the ball.
-/


/-- **The average error at `C²`, bounded on a ball.**

For every prescribed multiple there is a radius within which the Taylor error
is below that multiple of the squared radius, throughout the ball. -/
theorem taylorErr_le_on_ball_c2 {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ z ∈ ball (0 : EuclSpace d) ε, |taylorErr φ x z| ≤ η * ε ^ 2 := by
  obtain ⟨δ, hδ, hbd⟩ := exists_taylorErr_le hφ x hη
  refine ⟨δ, hδ, fun ε hε hεδ z hz => ?_⟩
  have hzn : ‖z‖ < ε := by
    rw [mem_ball, dist_zero_right] at hz
    exact hz
  have hzδ : ‖z‖ < δ := lt_trans hzn hεδ
  have h1 := hbd z hzδ
  have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    nlinarith [hzn, h0, hε]
  nlinarith [h1, hz2, hη.le, sq_nonneg ‖z‖]

end

end PLaplacian
