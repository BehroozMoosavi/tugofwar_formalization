/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Err2Comb

/-!
# The derivative bound along the ray

The derivative of the second-order error along a ray is bounded by the
prescribed multiple of the squared norm of the direction, uniformly on the
unit interval.

The operator norm of the derivative increment appears here, and only inside an
inequality. That is the distinction the finding on the two derivative
representations turns on: the operator norm is usable through le_opNorm, and
it is continuity in that norm which the topology on the space of continuous
linear maps denies.

## Main results

- err2_deriv_bound
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The C² Taylor error bound

The derivative of the error along a ray is bounded by `η ‖w‖²` for every `t`
in the unit interval, so the mean value inequality bounds the error itself by
the same.

The derivative at `t` is the increment at `t w` applied to `w`, of norm at
most `η ‖t w‖ ‖w‖ ≤ η ‖w‖²` for `t` in the unit interval, using the
operator-norm inequality.
-/


/-- The derivative along the ray is bounded on the unit interval. -/
theorem err2_deriv_bound {φ : EuclSpace d → ℝ} (_hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η δ : ℝ} (hη : 0 < η)
    (hbd : ∀ v : EuclSpace d, ‖v‖ < δ →
      ‖fderiv ℝ φ (x + v) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x v‖ ≤ η * ‖v‖)
    {w : EuclSpace d} (hw : ‖w‖ < δ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fderiv ℝ φ (x + t • w) w - fderiv ℝ φ x w
        - t * fderiv ℝ (fderiv ℝ φ) x w w‖ ≤ η * ‖w‖ ^ 2 := by
  rw [err2_deriv_eq_increment]
  -- the increment at t w
  have htw : ‖t • w‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖w‖ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
      _ = ‖w‖ := one_mul _
      _ < δ := hw
  have hinc := hbd (t • w) htw
  -- the operator-norm inequality
  have hop : ‖(fderiv ℝ φ (x + t • w) - fderiv ℝ φ x
      - fderiv ℝ (fderiv ℝ φ) x (t • w)) w‖
      ≤ ‖fderiv ℝ φ (x + t • w) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x (t • w)‖ * ‖w‖ :=
    ContinuousLinearMap.le_opNorm _ _
  -- and the scaling
  have hscale : ‖t • w‖ ≤ ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖w‖ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hwnn : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  calc ‖(fderiv ℝ φ (x + t • w) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x (t • w)) w‖
      ≤ ‖fderiv ℝ φ (x + t • w) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x (t • w)‖ * ‖w‖ := hop
    _ ≤ (η * ‖t • w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hinc hwnn
    _ ≤ (η * ‖w‖) * ‖w‖ := by
        have : η * ‖t • w‖ ≤ η * ‖w‖ :=
          mul_le_mul_of_nonneg_left hscale (le_of_lt hη)
        exact mul_le_mul_of_nonneg_right this hwnn
    _ = η * ‖w‖ ^ 2 := by ring

end

end PLaplacian
