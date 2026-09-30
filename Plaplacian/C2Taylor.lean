/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Err2Bound

/-!
# The second-order Taylor bound at C two

For a function of class C two, the second-order Taylor error at a point is at
most any prescribed multiple of the squared increment, within a radius
depending only on that multiple. No third derivative appears.

This removes a constraint that had stood over the whole development. The
asymptotic expansion was proved under a C three hypothesis because Mathlib's
several-variable Taylor interface carries no remainder estimate, and we took
that to mean a remainder had to be built from a third derivative.

The route out is not a third derivative. The derivative map of a C two
function is differentiable at the point with derivative the Hessian;
differentiability is already a little-o statement in Mathlib; and a little-o
statement carries its own uniformity, because a filter quantifies the
neighbourhood before the points in it. Integrating the resulting derivative
bound along a ray gives the error bound.

The obstruction was therefore never about the order of differentiability. It
was about searching for a remainder theorem instead of using the definition of
the second derivative.

## Main results

- err2_zero
- err2_le
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The C² Taylor error bound

Integrating the derivative bound along the unit interval. The error vanishes
at the origin, so the mean value inequality bounds the error at `w` by the
derivative bound times the length of the interval, which is one.
-/


/-- The error vanishes at the origin. -/
theorem err2_zero' (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    err2 φ x 0 = 0 := by
  unfold err2
  simp

/-- **The second-order Taylor error bound for a `C²` function.**

Given the derivative bound, the error at `w` is at most the same bound. -/
theorem err2_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η δ : ℝ} (hη : 0 < η)
    (hbd : ∀ v : EuclSpace d, ‖v‖ < δ →
      ‖fderiv ℝ φ (x + v) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x v‖ ≤ η * ‖v‖)
    {w : EuclSpace d} (hw : ‖w‖ < δ) :
    |err2 φ x w| ≤ η * ‖w‖ ^ 2 := by
  -- the scalar function along the ray
  set g : ℝ → ℝ := fun s => err2 φ x (s • w) with hg
  -- its derivative
  have hderiv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt g
        (fderiv ℝ φ (x + t • w) w - fderiv ℝ φ x w
          - t * fderiv ℝ (fderiv ℝ φ) x w w) (Icc (0:ℝ) 1) t := by
    intro t _
    exact (hasDerivAt_err2 hφ x w t).hasDerivWithinAt
  -- and its bound
  have hdbd : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ φ (x + t • w) w - fderiv ℝ φ x w
          - t * fderiv ℝ (fderiv ℝ φ) x w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    exact err2_deriv_bound hφ x hη hbd hw ht
  -- the mean value inequality
  have hmv : ‖g 1 - g 0‖ ≤ η * ‖w‖ ^ 2 * ‖(1:ℝ) - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hdbd
      (convex_Icc 0 1) (by norm_num) (by norm_num)
  -- g 0 = 0 and g 1 = err2 φ x w
  have hg0 : g 0 = 0 := by
    rw [hg]; simp only [zero_smul]; exact err2_zero' φ x
  have hg1 : g 1 = err2 φ x w := by
    rw [hg]; simp only [one_smul]
  rw [hg0, hg1, sub_zero] at hmv
  simpa using hmv

end

end PLaplacian
