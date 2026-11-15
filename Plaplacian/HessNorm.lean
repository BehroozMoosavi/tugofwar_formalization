/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AvgUnif

@[expose] public section

/-!
# The Hessian norm, curried and flat

The curried Hessian and the flat second derivative have the same norm, through
the first iterated derivative of the derivative.

The point of the equality is that the flat norm is bounded on compact sets
while the curried one cannot be bounded directly, its space not supporting
continuity of the norm. So a uniform bound on the curried Hessian at a moving
base point is obtained by bounding the flat second derivative and transferring
through this equality. That is the fourth time in this development that the
flat representation has been the way past the curried one's topology.

## Main results

- norm_hess_eq_flat
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The Hessian norm, curried and flat

The extreme-value error carries the operator norm of the curried Hessian at a
moving base point. Bounding that uniformly is the topology problem again: the
curried space does not support continuity of the norm.

The flat second derivative does, and `exists_bound_all_orders` bounds it on any
closed ball. What is needed is that the two norms agree. The curried form is
the image of the flat one under the currying equivalence, which is a linear
isometry, so the norms should be equal.

This probe looks for that equality.
-/


/-- **The norms agree.** The curried Hessian and the flat second derivative
have the same norm, through the first iterated derivative of the derivative. -/
theorem norm_hess_eq_flat {φ : EuclSpace d → ℝ} (y : EuclSpace d) :
    ‖fderiv ℝ (fderiv ℝ φ) y‖ = ‖iteratedFDeriv ℝ 2 φ y‖ := by
  rw [← norm_iteratedFDeriv_one (f := fderiv ℝ φ)]
  exact norm_iteratedFDeriv_fderiv (n := 1)

end

end PLaplacian
