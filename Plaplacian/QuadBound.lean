/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Deficit

@[expose] public section

/-!
# Bounding the quadratic terms

The deficit inequality carries an abstract bound. Here the quadratic part of
it is estimated: an increment inside the ball has norm at most epsilon, so the
quadratic form is at most the operator norm of the Hessian times epsilon
squared.

This does use the operator norm of the Hessian, but only as a fixed constant
at the point in question, never requiring continuity in the point. That is why
it is available here while the earlier routes to the remainder were not: the
inequality le_opNorm is perfectly usable, and it was Continuous.norm and the
composition of derivatives through the space of bilinear maps that the
topology on that space blocked.

A related wrinkle: the space of continuous linear maps carries its own
parallel API, with opNorm_nonneg, opNorm_zero and le_opNorm in place of the
generic normed-group lemmas, and the generic ones do not apply.

## Main results

- quad_term_le, quad_diff_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The deficit is of order epsilon squared

`deficit_le` carries an abstract bound `K`. Here it is instantiated: both the
increment `w = y - x` and the shift `ε ν` have norm at most `ε`, so

* the quadratic terms are bounded by `‖D²φ x‖ ε²` each, by
  `quadratic_le_of_norm_le`;
* the error terms are bounded by `C / 6` each, by `taylor_two_bounded`, with
  `C` a third-derivative bound, hence of order `ε³` in effect.

Combining, `K = ‖D²φ x‖ ε² + (error terms)`.
-/


/-- The quadratic term at an increment inside the ball. -/
theorem quad_term_le {φ : EuclSpace d → ℝ} (x : EuclSpace d)
    {w : EuclSpace d} {ε : ℝ} (hw : ‖w‖ ≤ ε) (hε : 0 < ε) :
    |(1 / 2) * fderiv ℝ (fderiv ℝ φ) x w w|
      ≤ (1 / 2) * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 := by
  have h := quadratic_le_of_norm_le (fderiv ℝ (fderiv ℝ φ) x)
    (le_refl ‖fderiv ℝ (fderiv ℝ φ) x‖) w
  have hw2 : ‖w‖ ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
    nlinarith [hw, h0]
  have hnn : (0:ℝ) ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  nlinarith [h, hw2, hnn]

/-- The difference of two quadratic terms is bounded. -/
theorem quad_diff_le {φ : EuclSpace d → ℝ} (x : EuclSpace d)
    {w v : EuclSpace d} {ε : ℝ} (hw : ‖w‖ ≤ ε) (hv : ‖v‖ ≤ ε)
    (hε : 0 < ε) :
    (1 / 2) * fderiv ℝ (fderiv ℝ φ) x w w
        - (1 / 2) * fderiv ℝ (fderiv ℝ φ) x v v
      ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 := by
  have h1 := quad_term_le (φ := φ) x hw hε
  have h2 := quad_term_le (φ := φ) x hv hε
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  linarith [h1'.1, h1'.2, h2'.1, h2'.2]

end

end PLaplacian
