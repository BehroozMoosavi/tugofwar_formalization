/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.InfTransport

@[expose] public section

/-!
# The upper bound on the infimum

Applying the lower bound on the supremum to the negation and transporting. The
gradient norm is unchanged and the infinity Laplacian flips sign, so negating
the resulting inequality gives the infimum bounded above by the value at the
centre, minus epsilon times the gradient norm, plus the same quadratic term.

The linear term has flipped and the quadratic has not. That is the
cancellation the average of the supremum and the infimum depends on, and
obtaining it by transport rather than by a parallel argument makes it
structural.

The error term is stated for the negation rather than for the original
function. That is honest but awkward for the final statement, and relating the
two is the remaining step.

## Main results

- sInf_upper_infLap
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The upper bound on the infimum

Applying `sSup_lower_infLap` to the negation gives

  `-φ x + ε ‖∇φ x‖ - (ε²/2) I + err' ≤ sSup ((-φ) '' closedBall x ε)`,

using `norm_gradient_neg` and `infLaplacianOf_neg`. Negating and rewriting the
supremum as an infimum by `sInf_eq_neg_sSup`:

  `sInf (φ '' closedBall x ε) ≤ φ x - ε ‖∇φ x‖ + (ε²/2) I - err'`.

The linear term has flipped and the quadratic has not, which is the
cancellation the average needs.
-/

/-- **The upper bound on the infimum.** -/
theorem sInf_upper_infLap {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    sInf (φ '' closedBall x ε)
      ≤ φ x - ε * ‖gradient φ x‖
        + (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x)
        - taylorErr (fun y => -φ y) x
            (ε • gradDir (fun y => -φ y) x) := by
  -- the supremum result for the negation
  have hneg := sSup_lower_infLap (contDiff_neg' hφ)
    (gradient_neg_ne_zero hx) hε
  rw [norm_gradient_neg, infLaplacianOf_neg] at hneg
  -- transport
  have hinf : sInf (φ '' closedBall x ε)
      = - sSup ((fun y => -φ y) '' closedBall x ε) :=
    sInf_eq_neg_sSup φ (closedBall x ε)
  rw [hinf]
  linarith [hneg]

end

end PLaplacian
