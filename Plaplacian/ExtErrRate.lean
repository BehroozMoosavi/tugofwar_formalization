/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.AvgErrBound

/-!
# The extreme-value error at a rate

The extreme-value sandwich width has two kinds of term: Taylor errors at
increments in the ball, of order epsilon cubed, and the quadratic comparison,
which the localization puts at order epsilon to the five halves. The second
dominates, and that is the honest rate; it is smaller than epsilon squared, so
the expansion is unaffected.

The theorem here is the input the localization consumes: the difference of
Taylor errors at two increments, bounded cubically.

## Main results

- error_diff_cubic
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The extreme-value error at a rate

The extreme-value sandwich has width built from two kinds of term:

* Taylor errors at increments of norm at most `ε`, which
  `taylorErr_le_cubic` puts at order `ε³`;
* the quadratic comparison `‖D²φ x‖ · ‖(y-x) - εν‖ · 2ε`, where the
  localization gives `‖(y-x) - εν‖` of order `ε^{3/2}`, so the product is of
  order `ε^{5/2}`.

The second dominates, and `ε^{5/2}` is the honest rate. Since
`ε^{5/2} = o(ε²)`, the expansion is unaffected.

This file records the rate for the error difference entering the localization,
which is the input to that estimate.
-/


/-- **The error difference at a cubic rate.**

The difference of Taylor errors at two increments in the ball is at most twice
the cubic bound, which is what the localization consumes as its `E`. -/
theorem error_diff_cubic {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) {ε : ℝ} (_hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w v : EuclSpace d, ‖w‖ ≤ ε → ‖v‖ ≤ ε →
      taylorErr φ x w - taylorErr φ x v ≤ K * ε ^ 3 := by
  obtain ⟨K, hK⟩ := taylorErr_le_cubic hφ x ε
  refine ⟨2 * max K 0, by positivity, fun w v hw hv => ?_⟩
  have hw3 : ‖w‖ ^ 3 ≤ ε ^ 3 := by
    have h0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
    have hεnn : (0:ℝ) ≤ ε := le_trans h0 hw
    nlinarith [hw, h0, hεnn, sq_nonneg (‖w‖ - ε), sq_nonneg (‖w‖ + ε)]
  have hv3 : ‖v‖ ^ 3 ≤ ε ^ 3 := by
    have h0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
    have hεnn : (0:ℝ) ≤ ε := le_trans h0 hv
    nlinarith [hv, h0, hεnn, sq_nonneg (‖v‖ - ε), sq_nonneg (‖v‖ + ε)]
  have hKm : K ≤ max K 0 := le_max_left _ _
  have hKnn : (0:ℝ) ≤ max K 0 := le_max_right _ _
  have h1 := abs_le.1 (hK w hw)
  have h2 := abs_le.1 (hK v hv)
  have hw3nn : (0:ℝ) ≤ ‖w‖ ^ 3 := by positivity
  have hv3nn : (0:ℝ) ≤ ‖v‖ ^ 3 := by positivity
  nlinarith [h1.2, h2.1, hw3, hv3, hKm, hKnn, hw3nn, hv3nn]

end

end PLaplacian
