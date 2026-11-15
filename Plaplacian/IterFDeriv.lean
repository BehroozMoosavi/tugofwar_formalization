/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.TaylorBound

@[expose] public section

/-!
# Uniform bounds via iteratedFDeriv

The average expansion needs a bound on the third derivative that is uniform
over a ball, independent of direction. Three attempts failed, all on the same
point, and the reason is worth recording.

Mathlib represents higher derivatives in two ways, and they are not
interchangeable for analytic purposes. The curried tower, fderiv of fderiv of
a function, lands in a space carrying ContinuousLinearMap.topologicalSpace,
which Lean does not unify with the metric topology induced by the operator
norm; so Continuous.norm is unavailable there, and derivatives cannot be
composed through it either. The flat representation, iteratedFDeriv, lands in
ContinuousMultilinearMap, which does carry the metric instance: Continuous.norm
applies, and ContinuousMultilinearMap.le_opNorm supplies the multilinear
estimate.

Each failed route had tried to do norm estimation in the representation that
does not support it. Differentiation wants the curried tower; norm estimation
wants the flat one; iteratedFDeriv_two_apply is the bridge between them, and a
development at second order and above needs both.

## Main results

- continuous_norm_iteratedFDeriv
- exists_uniform_bound: a single constant over a closed ball.
-/

open Set Topology Filter Metric

namespace PLaplacian
noncomputable section
variable {d : ℕ}

theorem continuous_norm_iteratedFDeriv {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) :
    Continuous (fun y => ‖iteratedFDeriv ℝ 3 φ y‖) := by
  have h : Continuous (fun y => iteratedFDeriv ℝ 3 φ y) :=
    hφ.continuous_iteratedFDeriv (by norm_num)
  exact h.norm

/-- A uniform bound on the third derivative over a closed ball. -/
theorem exists_uniform_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    ∃ C : ℝ, ∀ y ∈ closedBall x ε, ‖iteratedFDeriv ℝ 3 φ y‖ ≤ C := by
  have hc : Continuous (fun y => iteratedFDeriv ℝ 3 φ y) :=
    hφ.continuous_iteratedFDeriv (m := 3) (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x ε).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨C, hC⟩

end
end PLaplacian
