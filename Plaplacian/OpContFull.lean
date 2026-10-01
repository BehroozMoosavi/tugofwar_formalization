/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OpCont

/-!
# Continuity of the operator

The normalized p-Laplacian, as a function of the base point, is continuous
away from the singular set. The ordinary Laplacian is a trace, continuous in
the Hessian everywhere; the infinity Laplacian is the Hessian evaluated twice
at the normalized gradient, continuous wherever the normalization is.

Both go through the evaluation lemma for continuous linear maps, which is the
third time it has been needed and for the same reason each time: evaluating at
a vector lands in the reals, where the metric structure applies, whereas the
space of the maps themselves carries a topology that does not support the
norm.

This supplies the step the predicate assembly needs, where the operator is
evaluated at a near-contact point and the conclusion is wanted at the base
point.

## Main results

- continuousAt_laplacianOf
- continuousAt_infLaplacianOf
- normPLapOf_continuousAt
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Continuity of the operator

`normPLapOf` is the Laplacian plus a multiple of the infinity Laplacian. The
first is a trace, continuous in the Hessian. The second is the Hessian
evaluated twice at the normalized gradient, continuous wherever that is.
-/


/-- The Laplacian is continuous in the base point. -/
theorem continuousAt_laplacianOf {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x₀ : EuclSpace d) :
    ContinuousAt (fun y => laplacianOf (fderiv ℝ (fderiv ℝ φ) y)) x₀ := by
  have hH : Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y) :=
    continuous_hess hφ
  unfold laplacianOf
  refine (continuous_finsetSum _ fun i _ => ?_).continuousAt
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

/-- The infinity Laplacian is continuous away from the singular set. -/
theorem continuousAt_infLaplacianOf {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d} (hx : gradient φ x₀ ≠ 0) :
    ContinuousAt (fun y => infLaplacianOf (gradient φ y)
      (fderiv ℝ (fderiv ℝ φ) y)) x₀ := by
  have hH : ContinuousAt (fun y => fderiv ℝ (fderiv ℝ φ) y) x₀ :=
    (continuous_hess hφ).continuousAt
  have hd : ContinuousAt (fun y => gradDir φ y) x₀ :=
    continuousAt_gradDir hφ hx
  unfold infLaplacianOf
  have hdir : ContinuousAt
      (fun y => ‖gradient φ y‖⁻¹ • gradient φ y) x₀ := by
    have := continuousAt_gradDir hφ hx
    unfold gradDir at this
    exact this
  exact (hH.clm_apply hdir).clm_apply hdir

/-- **The operator is continuous away from the singular set.** -/
theorem normPLapOf_continuousAt {p : ℝ} {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d} (hx : gradient φ x₀ ≠ 0) :
    ContinuousAt (fun y => normPLapOf p (gradient φ y)
      (fderiv ℝ (fderiv ℝ φ) y)) x₀ := by
  unfold normPLapOf
  exact (continuousAt_laplacianOf hφ x₀).add
    (continuousAt_const.mul (continuousAt_infLaplacianOf hφ hx))

end

end PLaplacian
