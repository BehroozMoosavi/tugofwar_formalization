/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.QuadCompare

@[expose] public section

/-!
# The quadratic term is the infinity Laplacian

This is where Layer 3 meets Layer 2. The operator infLaplacianOf, defined in
Plaplacian.Operator as the Hessian evaluated twice at the normalized gradient,
is exactly the quadratic term of the expansion at the shifted point, scaled by
epsilon squared over two.

The normalized gradient of Plaplacian.GradDir and the vector inside
infLaplacianOf are the same by definition, so the content is bilinearity
pulling out the two factors of epsilon. Doing that with sequential rewrites
peels the two arguments asymmetrically; putting map_smul into a simp set
fires it on both at once.

## Main results

- gradDir_eq
- quad_at_shift
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The quadratic term is the infinity Laplacian

This lemma is where Layer 3 meets Layer 2. `infLaplacianOf`, defined in
`Plaplacian.Operator` as the Hessian evaluated twice at the normalized
gradient, is exactly the quadratic term of the expansion at the shifted point,
scaled by `ε²/2`.

`gradDir` and the `‖q‖⁻¹ • q` inside `infLaplacianOf` are the same vector by
definition, so the content is bilinearity pulling out the two factors of `ε`.
-/

/-- `gradDir` is the vector appearing in `infLaplacianOf`. -/
theorem gradDir_eq (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    gradDir φ x = ‖gradient φ x‖⁻¹ • gradient φ x := rfl

/-- **The quadratic term at the shifted point is the infinity Laplacian.** -/
theorem quad_at_shift {φ : EuclSpace d → ℝ} (x : EuclSpace d) (ε : ℝ) :
    (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
        (ε • gradDir φ x)
      = (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
          (fderiv ℝ (fderiv ℝ φ) x) := by
  unfold infLaplacianOf
  rw [gradDir_eq]
  simp only [ContinuousLinearMap.map_smul, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

end

end PLaplacian
