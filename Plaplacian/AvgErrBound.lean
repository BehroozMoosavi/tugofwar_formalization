/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.AvgRate

/-!
# The average of the error, bounded cubically

An average of a function bounded above by a constant is bounded by that
constant. Applied to the Taylor error with the uniform bound on the ball, the
average error is of order epsilon cubed.

The monotonicity of the set average used here is the lemma absent from Mathlib
and proved in Plaplacian.Average, which is one of the two upstreamable results
of this development. It is used for its intended purpose only at this point,
some eight hundred lines after being proved.

## Main results

- setAverage_taylorErr_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The average of the error

An average of a function bounded above by a constant is bounded by that
constant, via `setAverage_mono` against the constant function and
`setAverage_const_ball`.

Applied to the Taylor error with the uniform bound of
`Plaplacian.AvgRate`, this gives the average error at a cubic rate --- the
form the expansion of the operator consumes.
-/


/-- **The average of the Taylor error, bounded cubically.** -/
theorem setAverage_taylorErr_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, (⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z)
      ≤ K * ε ^ 3 := by
  obtain ⟨K, hK⟩ := taylorErr_le_on_ball hφ x hε
  refine ⟨K, ?_⟩
  have hmono : (⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z)
      ≤ ⨍ _z in ball (0 : EuclSpace d) ε, K * ε ^ 3 := by
    refine setAverage_mono measurableSet_ball
      (integrableOn_taylorErr (hφ.of_le (by norm_num)) x ε) integrableOn_const ?_
    intro z hz
    have h := hK z hz
    exact le_of_abs_le h
  rw [setAverage_const_ball (K * ε ^ 3) 0 hε] at hmono
  exact hmono

end

end PLaplacian
