/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ErrNeg

/-!
# The domination hypothesis

The localization requires that the value at the maximizer dominate the value
at the shifted point. That is true because the shifted point lies in the ball
and the maximizer maximizes there, but it must be derived: maximality is a
statement about the function on a set, while the localization wants an
inequality between two specific points.

The theorem below produces the maximizer together with both hypotheses the
localization needs, which is the piece that was missing: the upper bound on
the supremum yields a maximizer but not the domination fact.

## Main results

- exists_max_with_dom
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The domination hypothesis

`localize_maximizer` requires that the value at the maximizer dominate the
value at the shifted point. That holds because the shifted point lies in the
ball and the maximizer maximizes there --- but it has to be derived, since
`IsMaxOn` is a statement about the function on the set and the hypothesis is
about two specific points.
-/

/-- The maximizer, together with the domination hypothesis. -/
theorem exists_max_with_dom {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      ‖y - x‖ ≤ ε
      ∧ φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x) := by
  obtain ⟨y, hyMem, hyMax⟩ := exists_isMaxOn_closedBall hφ x hε
  refine ⟨y, hyMem, norm_sub_le_of_mem hyMem, ?_⟩
  have hxy : x + (y - x) = y := by abel
  rw [hxy]
  exact hyMax (mem_closedBall_shift x (norm_gradDir hx) hε)

end

end PLaplacian
