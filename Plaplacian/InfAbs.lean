/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupAbs

/-!
# The infimum two-sided error, by transport

The supremum uniform error, applied to the negation and translated back. The
supremum of the negation is minus the infimum, and the Taylor error, the
Hessian norm and the gradient norm are all unchanged under negation while the
infinity Laplacian flips sign. So the infimum deviates from its expansion by
the same uniform bound.

The linear term enters with the opposite sign to the supremum one, and that
is what cancels in the average. The Hessian norm is the operator norm of a
continuous linear map, so its negation needs the operator-norm lemma rather
than the generic one, the parallel API of that space once more.

## Main results

- inf_err_abs
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The infimum's two-sided error, by transport

The supremum's uniform error, applied to the negation and translated back.
The supremum of the negation is minus the infimum, the gradient norm is
unchanged, the Hessian norm is unchanged, and the infinity Laplacian flips
sign. So the infimum deviates from its expansion --- the value less the
parameter times the gradient norm, plus the same quadratic term --- by the same
uniform bound.

The linear term enters with the opposite sign, and that sign is what cancels
against the supremum's in the average.
-/


/-- **The infimum's two-sided error, uniformly.** -/
theorem inf_err_abs {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε K H g : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K)
    (hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε → |taylorErr φ x z| ≤ K * ε ^ 3)
    (hH : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H) (hg : 0 < g)
    (hgx : g ≤ ‖gradient φ x‖) :
    |sInf (φ '' closedBall x ε)
        - (φ x - ε * ‖gradient φ x‖
            + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
                (fderiv ℝ (fderiv ℝ φ) x))|
      ≤ H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
        + K * ε ^ 3 := by
  -- the negation's hypotheses
  have hψ : ContDiff ℝ 3 (fun y => -φ y) := contDiff_neg' hφ
  have hxψ : gradient (fun y => -φ y) x ≠ 0 := gradient_neg_ne_zero hx
  have hTψ : ∀ z : EuclSpace d, ‖z‖ ≤ ε →
      |taylorErr (fun y => -φ y) x z| ≤ K * ε ^ 3 := by
    intro z hz
    rw [taylorErr_neg, abs_neg]
    exact hTerr z hz
  have hHψ : ‖fderiv ℝ (fderiv ℝ (fun y => -φ y)) x‖ ≤ H := by
    rw [hess_neg, ContinuousLinearMap.opNorm_neg]; exact hH
  have hgψ : g ≤ ‖gradient (fun y => -φ y) x‖ := by
    rw [norm_gradient_neg]; exact hgx
  -- the supremum's error for the negation
  have h := sup_err_abs hψ hxψ hε hK hTψ hHψ hg hgψ
  -- translate back
  have hsup : sSup ((fun y => -φ y) '' closedBall x ε)
      = - sInf (φ '' closedBall x ε) := by
    have := sInf_eq_neg_sSup φ (closedBall x ε)
    linarith [this]
  rw [hsup, norm_gradient_neg, infLaplacianOf_neg] at h
  have heq : - sInf (φ '' closedBall x ε)
      - (-φ x + ε * ‖gradient φ x‖
          + ε ^ 2 / 2 * -infLaplacianOf (gradient φ x)
              (fderiv ℝ (fderiv ℝ φ) x))
      = -(sInf (φ '' closedBall x ε)
          - (φ x - ε * ‖gradient φ x‖
              + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
                  (fderiv ℝ (fderiv ℝ φ) x))) := by ring
  rw [heq, abs_neg] at h
  exact h

end

end PLaplacian
