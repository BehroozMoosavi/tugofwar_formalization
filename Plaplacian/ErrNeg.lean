/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.InfUpper

/-!
# The error of the negation

The infimum bound carries the Taylor error of the negation at the negation's
gradient direction. Unwinding, each of the four terms of the error negates, so
the error of the negation is minus the error of the original at the same
increment, and the negation direction is minus the original one.

With this, both extreme-value bounds are stated in terms of the original
function alone.

## Main results

- taylorErr_neg, gradDir_neg
- inf_err_eq
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The error of the negation

`sInf_upper_infLap` carries `taylorErr (-φ)` at the direction of the
negation's gradient, which is `-ν`. Unwinding:

  `taylorErr (-φ) x z = -φ (x+z) + φ x - D(-φ) x z - (1/2) D²(-φ) x (z,z)`
                      `= - taylorErr φ x z`,

so the error of the negation is minus the error of the original at the same
increment. And the negation's shift is `ε • (-ν) = -(ε • ν)`.
-/


/-- The Taylor error of the negation. -/
theorem taylorErr_neg (φ : EuclSpace d → ℝ) (x z : EuclSpace d) :
    taylorErr (fun y => -φ y) x z = - taylorErr φ x z := by
  unfold taylorErr
  have h1 : fderiv ℝ (fun y => -φ y) x z = - fderiv ℝ φ x z := by
    rw [show (fun y => -φ y) = -φ from rfl, fderiv_neg]
    rfl
  have h2 : fderiv ℝ (fderiv ℝ (fun y => -φ y)) x z z
      = - fderiv ℝ (fderiv ℝ φ) x z z := by
    rw [hess_neg]
    simp
  rw [h1, h2]
  ring

/-- The negation's shift direction is the negative of the original's. -/
theorem gradDir_neg (φ : EuclSpace d → ℝ) {x : EuclSpace d}
    (_hx : gradient φ x ≠ 0) :
    gradDir (fun y => -φ y) x = - gradDir φ x := by
  unfold gradDir
  rw [gradient_neg', norm_neg]
  simp

/-- **The error in `sInf_upper_infLap`, in terms of the original
function.** -/
theorem inf_err_eq (φ : EuclSpace d → ℝ) {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) (ε : ℝ) :
    taylorErr (fun y => -φ y) x (ε • gradDir (fun y => -φ y) x)
      = - taylorErr φ x (-(ε • gradDir φ x)) := by
  rw [gradDir_neg φ hx, taylorErr_neg]
  congr 2
  module

end

end PLaplacian
