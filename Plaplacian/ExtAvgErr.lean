/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.InfAbs

@[expose] public section

/-!
# The extreme-value average error, uniformly

The supremum deviates from its expansion with the linear term entering
positively, the infimum with it entering negatively, each by the same uniform
bound. Averaging cancels the linear terms, so the average of the supremum and
the infimum deviates from the value plus the infinity-Laplacian term by at
most that bound.

That cancellation is the one that produces the infinity Laplacian in the
asymptotic expansion; here it is carried through with the error controlled
uniformly in the base point. This is the extreme-value half of the expansion
error made uniform, the half that needed the localization redone at a moving
base point.

## Main results

- ext_avg_err_abs
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The extreme-value average error, uniformly

The supremum deviates from its expansion with the linear term
`+ ε ‖∇φ x‖`, the infimum with `- ε ‖∇φ x‖`, each by at most the same uniform
bound. Averaging, the linear terms cancel and the average of the supremum and
infimum deviates from the value plus the infinity-Laplacian term by at most
that bound.

This is the extreme-value half of the expansion error, uniform in the base
point.
-/


/-- **The extreme-value average error, uniformly.** -/
theorem ext_avg_err_abs {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε K H g : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K)
    (hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε → |taylorErr φ x z| ≤ K * ε ^ 3)
    (hH : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H) (hg : 0 < g)
    (hgx : g ≤ ‖gradient φ x‖) :
    |(sSup (φ '' closedBall x ε) + sInf (φ '' closedBall x ε)) / 2
        - (φ x + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x))|
      ≤ H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
        + K * ε ^ 3 := by
  have hs := sup_err_abs hφ hx hε hK hTerr hH hg hgx
  have hi := inf_err_abs hφ hx hε hK hTerr hH hg hgx
  set B := H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
    + K * ε ^ 3 with hB
  have hs' := abs_le.1 hs
  have hi' := abs_le.1 hi
  rw [abs_le]
  constructor <;> linarith [hs'.1, hs'.2, hi'.1, hi'.2]

end

end PLaplacian
