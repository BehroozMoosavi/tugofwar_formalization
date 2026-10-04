/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupErrUnif

/-!
# The supremum two-sided error, uniformly

The lower half is immediate: the supremum lies above its expansion plus the
Taylor error at the shifted point, and that error is at least minus the
uniform cubic bound. With the upper half, the deviation of the supremum from
its expansion is bounded in absolute value by a quantity free of the base
point and of order the parameter to the five halves.

The upper bound carries an extra nonnegative term that the lower does not, so
the lower bound clears the absolute-value requirement; that nonnegativity is
the one point of arithmetic made explicit.

## Main results

- sup_err_abs
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supremum's two-sided error, uniformly

The lower half is immediate: the supremum lies above its expansion plus the
Taylor error at the shifted point, and that error is at least minus the
uniform cubic bound. Combined with the upper half, the supremum's deviation
from its expansion is bounded in absolute value by a quantity free of the base
point.
-/


/-- **The supremum's two-sided error, uniformly.** -/
theorem sup_err_abs {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε K H g : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K)
    (hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε → |taylorErr φ x z| ≤ K * ε ^ 3)
    (hH : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H) (hg : 0 < g)
    (hgx : g ≤ ‖gradient φ x‖) :
    |sSup (φ '' closedBall x ε)
        - (φ x + ε * ‖gradient φ x‖
            + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
                (fderiv ℝ (fderiv ℝ φ) x))|
      ≤ H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
        + K * ε ^ 3 := by
  -- the upper half
  have hup := sup_err_le hφ hx hε hK hTerr hH hg hgx
  -- the lower half
  have hlow := sSup_lower_infLap hφ hx hε
  have hshift : ‖ε • gradDir φ x‖ = ε := norm_eps_gradDir hx hε
  have hTs := hTerr (ε • gradDir φ x) (le_of_eq hshift)
  have hTs' := (abs_le.1 hTs).1
  -- the upper bound's extra term is nonnegative
  have hHnn : (0:ℝ) ≤ H :=
    le_trans (ContinuousLinearMap.opNorm_nonneg _) hH
  have hsq : (0:ℝ) ≤ Real.sqrt
      (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g)) := Real.sqrt_nonneg _
  have hextra : (0:ℝ) ≤ H * ε * Real.sqrt
      (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g)) := by
    have : (0:ℝ) ≤ H * ε := mul_nonneg hHnn (le_of_lt hε)
    exact mul_nonneg this hsq
  rw [abs_le]
  constructor
  · linarith [hlow, hTs', hextra]
  · exact hup

end

end PLaplacian
