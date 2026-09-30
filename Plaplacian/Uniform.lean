/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LittleO

/-!
# Direction-uniformity of the little-o

For a function of class C two, the derivative map differs from its
linearisation at a point by at most any prescribed multiple of the distance,
within a radius depending only on that multiple.

The quantifier order is the whole content: the radius is chosen before the
increment. We had expected to obtain it from compactness of the sphere and did
not need to. Mathlib encodes differentiability as a little-o statement, and a
filter statement quantifies the neighbourhood before the points in it, so the
uniformity is already present in the encoding.

The lemma that the derivative map is differentiable with derivative the
Hessian was proved in the second layer for the second-order necessary
condition. This is its third distinct use.

## Main results

- err2
- fderiv_increment_small
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Direction-uniformity of the little-o

The uniformity comes from first-order differentiability of the derivative
map, not from compactness of the sphere as we had expected.

Write `g y = φ y - φ x - Dφ x (y - x) - (1/2) D²φ x (y-x, y-x)`. Its
derivative at `y` is `Dφ y - Dφ x - D²φ x (y - x)`, which is small on a small
ball exactly because `Dφ` is differentiable at `x` with derivative `D²φ x`.
The mean value inequality on the segment then bounds `g` itself, and the bound
is uniform in the direction because the derivative bound is.

The norm of the derivative map's increment is needed, which lives in the space
of continuous linear maps. That is the space whose topology blocked three
routes in the third layer --- but only the operator-norm inequality is needed
here, not continuity in that norm, and the inequality is available.
-/

/-- The second-order Taylor error. -/
def err2 (φ : EuclSpace d → ℝ) (x w : EuclSpace d) : ℝ :=
  φ (x + w) - φ x - fderiv ℝ φ x w
    - (1/2) * fderiv ℝ (fderiv ℝ φ) x w w


/-- **The derivative increment is uniformly small.** For every `η > 0` there
is a radius within which the derivative map differs from its linearisation by
at most `η` times the distance --- the little-o form of the above, with the
radius chosen before the increment. -/
theorem fderiv_increment_small {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ w : EuclSpace d, ‖w‖ < δ →
      ‖fderiv ℝ φ (x + w) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x w‖ ≤ η * ‖w‖ := by
  have h := (hasFDerivAt_fderiv hφ x).isLittleO
  rw [Asymptotics.isLittleO_iff] at h
  have hev := h hη
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hsub⟩ := hev
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hx : dist (x + w) x < δ := by
    rw [dist_eq_norm]
    simpa using hw
  have hres := hsub hx
  simpa using hres

end

end PLaplacian
