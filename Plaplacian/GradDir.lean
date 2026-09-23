/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ExtremeAttain

/-!
# The gradient direction

The algebraic heart of the extreme-value expansion. Where the gradient does
not vanish, let nu be the normalized gradient. Then

  the derivative of phi at x applied to nu equals the norm of the gradient,

so the linear term of the Taylor expansion contributes plus epsilon times the
gradient norm at the point x plus epsilon nu, and minus the same at x minus
epsilon nu. The two cancel in the average of the supremum and the infimum,
leaving only the second-order term, which is the infinity Laplacian.

That cancellation is why the extreme-value half of the operator produces the
infinity Laplacian while the average half produces the ordinary one.

## Main results

- gradDir, norm_gradDir
- fderiv_gradDir, fderiv_eps_gradDir
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The lower bound

`sup ≥ φ (x + ε ν)`, and Taylor at that point gives the leading behaviour.
The key algebraic fact: when `ν` is the normalized gradient,

  `Dφ x (ε ν) = ε ‖∇φ x‖`,

so the linear term contributes `+ ε ‖∇φ x‖` to the supremum and
`- ε ‖∇φ x‖` to the infimum, and the two cancel in the average.
-/


/-- The normalized gradient, where it is defined. -/
def gradDir (φ : EuclSpace d → ℝ) (x : EuclSpace d) : EuclSpace d :=
  ‖gradient φ x‖⁻¹ • gradient φ x

/-- It is a unit vector where the gradient does not vanish. -/
theorem norm_gradDir {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) : ‖gradDir φ x‖ = 1 := by
  unfold gradDir
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)

/-- **The derivative in the gradient direction is the gradient norm.** -/
theorem fderiv_gradDir {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) :
    fderiv ℝ φ x (gradDir φ x) = ‖gradient φ x‖ := by
  rw [← inner_gradient_left]
  unfold gradDir
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖gradient φ x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp

/-- Scaled: the derivative at the shifted increment. -/
theorem fderiv_eps_gradDir {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) (ε : ℝ) :
    fderiv ℝ φ x (ε • gradDir φ x) = ε * ‖gradient φ x‖ := by
  rw [ContinuousLinearMap.map_smul, fderiv_gradDir hx, smul_eq_mul]

end

end PLaplacian
