/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.InfSide

/-!
# Transporting through negation

The facts about the negation that the transport of the supremum results
needs. The Hessian flips sign, the gradient norm is unchanged, and therefore
the infinity Laplacian flips sign: the direction minus nu gives the same
quadratic form, but the form itself is negated.

That combination is why the transport produces the correct infimum bound.
Applying the supremum result to minus phi and negating turns the linear term
around while leaving the quadratic term alone, which is the cancellation the
extreme-value expansion depends on.

## Main results

- hess_neg, norm_gradient_neg
- infLaplacianOf_neg
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The transported infimum bound

Applying `sSup_lower_infLap` to the negation and transporting. Two facts are
needed about the negation beyond those of `Plaplacian.InfSide`:

* its Hessian is minus the original's, so `infLaplacianOf` flips sign;
* its gradient norm is the same.
-/


/-- The Hessian of the negation. -/
theorem hess_neg (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    fderiv ℝ (fderiv ℝ (fun y => -φ y)) x
      = - fderiv ℝ (fderiv ℝ φ) x := by
  have h1 : fderiv ℝ (fun y => -φ y) = - fderiv ℝ φ := by
    funext y
    rw [show (fun y => -φ y) = -φ from rfl, fderiv_neg]
    rfl
  rw [h1]
  exact fderiv_neg

/-- The gradient norm is unchanged by negation. -/
theorem norm_gradient_neg (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    ‖gradient (fun y => -φ y) x‖ = ‖gradient φ x‖ := by
  rw [gradient_neg', norm_neg]

/-- **The infinity Laplacian flips sign under negation.** -/
theorem infLaplacianOf_neg (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    infLaplacianOf (gradient (fun y => -φ y) x)
        (fderiv ℝ (fderiv ℝ (fun y => -φ y)) x)
      = - infLaplacianOf (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) := by
  unfold infLaplacianOf
  rw [hess_neg, gradient_neg', norm_neg]
  simp

end

end PLaplacian
