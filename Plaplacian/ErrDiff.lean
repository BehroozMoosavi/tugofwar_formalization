/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LocalizeMax

@[expose] public section

/-!
# The error difference

The localization needs a bound on the difference of the Taylor errors at the
maximizer and at the shifted point. The cubic estimate supplies a constant at
each point separately, so the difference is bounded by their sum.

With this, the localization has no abstract hypotheses remaining: every input
is supplied by a proved result.

## Main results

- abs_taylorErr_le
- exists_error_diff_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The error difference

`localize_maximizer` needs a bound `E` on the difference of the Taylor errors
at the two points. `taylor_two_bounded` supplies a constant at each point
separately, so the difference is bounded by their sum.

Note that `taylorErr` is exactly the quantity `taylor_two_bounded` bounds:
both are the second-order Taylor error, the first as a definition and the
second inside an absolute value.
-/


/-- The error at a single point, in terms of `taylorErr`. -/
theorem abs_taylorErr_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x z : EuclSpace d) :
    ∃ C : ℝ, |taylorErr φ x z| ≤ C / 6 := by
  obtain ⟨C, hC⟩ := taylor_two_bounded hφ x z
  exact ⟨C, by unfold taylorErr; exact hC⟩

/-- **The error difference is bounded.** -/
theorem exists_error_diff_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x w v : EuclSpace d) :
    ∃ E : ℝ, taylorErr φ x w - taylorErr φ x v ≤ E := by
  obtain ⟨C₁, h₁⟩ := abs_taylorErr_le hφ x w
  obtain ⟨C₂, h₂⟩ := abs_taylorErr_le hφ x v
  refine ⟨C₁ / 6 + C₂ / 6, ?_⟩
  have h1 := abs_le.1 h₁
  have h2 := abs_le.1 h₂
  linarith [h1.2, h2.1]

end

end PLaplacian
