/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Sandwich

@[expose] public section

/-!
# Eliminating the maximizer

The upper bound on the supremum carries an error mentioning the maximizer. To
feed it into the expansion the maximizer must be eliminated, by substituting a
bound on the localization distance and the fact that the increment has norm at
most epsilon.

The resulting error is in terms of epsilon and the data at the point alone.

A note on the estimate. The localization bounds the square of the distance, so
extracting the distance itself introduces a square root, and the honest order
is epsilon to the three halves rather than epsilon squared. That is what the
mathematics gives, and it suffices: multiplied by the remaining factor of
epsilon it is epsilon to the five halves, smaller than epsilon squared, so the
expansion is unaffected.

## Main results

- norm_eps_gradDir
- cmp_err_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Eliminating the maximizer

`sSup_upper_infLap` produces a bound whose error mentions the maximizer `y`.
To plug it into `extreme_avg_eq` the `y` must be eliminated, by substituting
the localization bound for `‖(y - x) - ε ν‖` and the ball bound for `‖y - x‖`.

The resulting error is in terms of `ε` and the data at `x` alone.
-/


/-- The norm of the shift. -/
theorem norm_eps_gradDir {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ‖ε • gradDir φ x‖ = ε := by
  rw [norm_smul, norm_gradDir hx, Real.norm_eq_abs, abs_of_pos hε, mul_one]

/-- The comparison error, bounded in terms of the localization distance. -/
theorem cmp_err_le {φ : EuclSpace d → ℝ} {x y : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε D : ℝ} (hε : 0 < ε)
    (hball : ‖y - x‖ ≤ ε)
    (hloc : ‖(y - x) - ε • gradDir φ x‖ ≤ D) (hD : 0 ≤ D) :
    (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
        * ‖(y - x) - ε • gradDir φ x‖
        * (‖y - x‖ + ‖ε • gradDir φ x‖))
      ≤ (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖ * D * (2 * ε)) := by
  rw [norm_eps_gradDir hx hε]
  have hHnn : (0:ℝ) ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hsum : ‖y - x‖ + ε ≤ 2 * ε := by linarith [hball]
  have hdnn : (0:ℝ) ≤ ‖(y - x) - ε • gradDir φ x‖ := norm_nonneg _
  have hsumnn : (0:ℝ) ≤ ‖y - x‖ + ε := by
    have := norm_nonneg (y - x); linarith
  -- step 1: replace the distance by D
  have s1 : ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖y - x - ε • gradDir φ x‖
        * (‖y - x‖ + ε)
      ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * D * (‖y - x‖ + ε) := by
    have hmul : ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖y - x - ε • gradDir φ x‖
        ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * D :=
      mul_le_mul_of_nonneg_left hloc hHnn
    exact mul_le_mul_of_nonneg_right hmul hsumnn
  -- step 2: replace the sum by 2 ε
  have s2 : ‖fderiv ℝ (fderiv ℝ φ) x‖ * D * (‖y - x‖ + ε)
      ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * D * (2 * ε) := by
    have hnn : (0:ℝ) ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * D :=
      mul_nonneg hHnn hD
    exact mul_le_mul_of_nonneg_left hsum hnn
  linarith [s1, s2]

end

end PLaplacian
