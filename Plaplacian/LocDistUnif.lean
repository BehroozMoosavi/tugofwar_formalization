/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupMax

/-!
# The localization distance, uniformly

At the shared maximizer, the localization bounds the distance from the
increment to the shifted point by a square root whose argument carries the
base-point Hessian, gradient and Taylor error. Replacing those by uniform
constants and using the monotonicity of the square root bounds the distance
independently of the base point.

The Taylor-error difference is bounded by twice the uniform cubic constant
times the cube of the parameter, both increments having norm at most the
parameter. Taking that as the error bound keeps the numerator nonnegative,
which the replacement requires.

The bound is of order the parameter to the three halves, the localization's
honest rate, now with a constant that does not move with the base point.

## Main results

- loc_dist_unif
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The localization distance, uniformly

At the shared maximizer, `localize_dist` bounds the distance from the
increment to the shifted point by a square root whose argument carries the
base-point Hessian, gradient and Taylor error. `localize_rhs_le` replaces
those by uniform constants, and the square root is monotone, so the distance
is bounded independently of the base point.

The Taylor-error difference is bounded by twice the uniform cubic constant
times `ε³`, since both increments have norm at most `ε`. Taking that as the
error bound keeps the numerator nonnegative, which `localize_rhs_le` requires.
-/


/-- **The localization distance, bounded uniformly.** -/
theorem loc_dist_unif {φ : EuclSpace d → ℝ} {x y : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε K H g : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hyb : ‖y - x‖ ≤ ε)
    (hdom : φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x))
    (hTy : |taylorErr φ x (y - x)| ≤ K * ε ^ 3)
    (hTs : |taylorErr φ x (ε • gradDir φ x)| ≤ K * ε ^ 3)
    (hH : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H) (hg : 0 < g)
    (hgx : g ≤ ‖gradient φ x‖) :
    ‖y - x - ε • gradDir φ x‖
      ≤ Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g)) := by
  -- the Taylor-error difference
  have hE : taylorErr φ x (y - x) - taylorErr φ x (ε • gradDir φ x)
      ≤ 2 * K * ε ^ 3 := by
    have h1 := (abs_le.1 hTy).2
    have h2 := (abs_le.1 hTs).1
    linarith [h1, h2]
  -- the numerator is nonnegative
  have hε2 : (0:ℝ) ≤ ε ^ 2 := by positivity
  have hε3 : (0:ℝ) ≤ ε ^ 3 := by positivity
  have hHnn : (0:ℝ) ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hnum : 0 ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + 2 * K * ε ^ 3 := by
    have : 0 ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 := mul_nonneg hHnn hε2
    have : 0 ≤ 2 * K * ε ^ 3 := by positivity
    linarith
  have hgpos : 0 < ‖gradient φ x‖ := lt_of_lt_of_le hg hgx
  have hnn : 0 ≤ 2 * ε * ((‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2
      + 2 * K * ε ^ 3) / ‖gradient φ x‖) := by
    have : 0 ≤ (‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + 2 * K * ε ^ 3)
        / ‖gradient φ x‖ := div_nonneg hnum (le_of_lt hgpos)
    positivity
  -- the localization at the base point
  have hloc := localize_dist hx hε hyb hdom hE hnn
  -- the uniform constants
  have hrhs := localize_rhs_le hε hH hg hgx
    (le_refl (2 * K * ε ^ 3)) hnum
  exact le_trans hloc (Real.sqrt_le_sqrt hrhs)

end

end PLaplacian
