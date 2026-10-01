/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.C2Diff

/-!
# Continuity of the gradient and its direction

The predicate assembly evaluates the operator at a near-contact point and
concludes at the base point, so the operator must be continuous in the
gradient and the Hessian.

The gradient is the inverse Riesz image of the derivative, and the Riesz map
is a linear isometry equivalence, hence continuous both ways; so continuity of
the gradient is continuity of the derivative composed with a continuous map.

The normalized gradient is continuous only away from the singular set, the
normalization dividing by the norm. That is why the regular and singular cases
of the predicate are separate: not only do they have different conclusions,
the operator is not continuous across the boundary between them.

## Main results

- continuous_gradient
- continuousAt_gradDir
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Continuity of the operator in its arguments

The assembly evaluates the operator at a near-contact point and concludes at
the base point, so the operator must be continuous in the gradient and the
Hessian. It is, away from the singular set: the infinity Laplacian divides by
the gradient norm, so continuity fails exactly where the gradient vanishes.

The route: `laplacianOf` is a trace, hence continuous in the Hessian;
`infLaplacianOf` is the Hessian at the normalized gradient, continuous
wherever the normalization is.
-/


/-- The gradient is continuous for a `C²` function. -/
theorem continuous_gradient {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (fun y => gradient φ y) := by
  have hf : Continuous (fun y => fderiv ℝ φ y) :=
    hφ.continuous_fderiv (by norm_num)
  have hiso : Continuous
      (fun L : StrongDual ℝ (EuclSpace d) =>
        (InnerProductSpace.toDual ℝ (EuclSpace d)).symm L) :=
    (InnerProductSpace.toDual ℝ (EuclSpace d)).symm.continuous
  exact hiso.comp hf

/-- The normalized gradient is continuous away from the singular set. -/
theorem continuousAt_gradDir {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hx : gradient φ x₀ ≠ 0) :
    ContinuousAt (fun y => gradDir φ y) x₀ := by
  have hg : ContinuousAt (fun y => gradient φ y) x₀ :=
    (continuous_gradient hφ).continuousAt
  have hn : ContinuousAt (fun y => ‖gradient φ y‖) x₀ := hg.norm
  have hne : ‖gradient φ x₀‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hinv : ContinuousAt (fun y => ‖gradient φ y‖⁻¹) x₀ :=
    hn.inv₀ hne
  unfold gradDir
  exact hinv.smul hg

end

end PLaplacian
