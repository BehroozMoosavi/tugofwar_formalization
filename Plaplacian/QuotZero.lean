/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.FreqGen

@[expose] public section

/-!
# The error quotient: the arithmetic core

The quantity to control is twice p plus d, times the error, divided by epsilon
squared. Given the error bounded by a multiple of epsilon squared, the
quotient is bounded by twice p plus d times that multiple.

The bound on the error enters as a hypothesis. That separation is the guard:
the arithmetic cannot be vacuous, the hypothesis being a genuine constraint,
and the analytic content is isolated in the separate task of supplying it.

Three radii interact in that task and their order is the content: the radius
from the C two estimate, depending on the multiple alone; the radius from the
local maximum, depending on the test function and the point; and the
constraint relating the parameter to the second so that the ball is contained.
The order must be the multiple, then its radius, then the parameter below both
radii, then the point. Written any other way the statement is either false or
empty.

## Main results

- quotient_le_of_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The error quotient tends to zero

The quantity to control is `2(p+d) * |E| / ε²` where `E` is the expansion's
error at a near-contact point. The `C²` estimate bounds `|E|` by `η ‖w‖²` for
`‖w‖` below a radius depending on `η` alone, and the increment at a point of
the ball has norm at most `ε`, so the quotient is at most `2(p+d) η`.

Since `η` is arbitrary, the quotient tends to zero.

THE QUANTIFIER ORDER. Three radii interact:

* `δ η` from the `C²` estimate, depending on `η` alone;
* `r` from the local maximum, depending on the test function and the point;
* the constraint `ε < r` for the ball containment.

The order must be: `η` first, then `δ η`, then `ε` below both `δ η` and `r`,
then the point. Writing it any other way yields a statement that is either
false or empty.

This file proves only the arithmetic core, with the bound on the error as a
hypothesis: given that `|E ε| ≤ η ε²` for `ε` small, the quotient is below
`2(p+d) η` for `ε` small. The analytic content --- that the `C²` estimate
supplies that bound --- is separate, and the separation is the guard.
-/

/-- **The arithmetic core.** If the error is bounded by `η ε²` then the
quotient is bounded by `2(p+d) η`. -/
theorem quotient_le_of_bound {p : ℝ} (hpd : 0 < p + (d : ℝ))
    {η : ℝ} {E : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hE : |E ε| ≤ η * ε ^ 2) :
    |(2 * (p + (d : ℝ))) * E ε / ε ^ 2| ≤ 2 * (p + (d : ℝ)) * η := by
  have h2 : (0:ℝ) < ε ^ 2 := by positivity
  have hpd2 : (0:ℝ) < 2 * (p + (d : ℝ)) := by linarith
  rw [abs_div, abs_mul, abs_of_pos hpd2, abs_of_pos h2]
  rw [div_le_iff₀ h2]
  calc 2 * (p + (d : ℝ)) * |E ε|
      ≤ 2 * (p + (d : ℝ)) * (η * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hE (le_of_lt hpd2)
    _ = 2 * (p + (d : ℝ)) * η * ε ^ 2 := by ring

end

end PLaplacian
