/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Err2Deriv

/-!
# The error derivative, combined

Subtracting the three term derivatives gives the derivative of the error along
a ray, and the result is the derivative increment at the scaled direction,
applied to the direction itself. That is exactly the quantity the uniform
estimate bounds, so the mean value inequality now applies.

## Main results

- hasDerivAt_err2
- err2_deriv_eq_increment
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The error's derivative, combined

Subtracting the three term derivatives gives

  `d/dt err2 φ x (t • w)
     = Dφ (x + t w) w - Dφ x w - t D²φ x (w, w)`,

and the right side is the derivative increment at `t w`, applied to `w`.
-/


/-- **The error's derivative along a ray.** -/
theorem hasDerivAt_err2 {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x w : EuclSpace d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => err2 φ x (s • w))
      (fderiv ℝ φ (x + t • w) w - fderiv ℝ φ x w
        - t * fderiv ℝ (fderiv ℝ φ) x w w) t := by
  have h1 := hasDerivAt_ray hφ x w t
  have h2 := hasDerivAt_linear (φ := φ) x w t
  have h3 := hasDerivAt_quad (φ := φ) x w t
  have hfun : (fun s : ℝ => err2 φ x (s • w))
      = fun s : ℝ => φ (x + s • w) - φ x
          - fderiv ℝ φ x (s • w)
          - (1/2) * fderiv ℝ (fderiv ℝ φ) x (s • w) (s • w) := by
    funext s
    unfold err2
    ring
  rw [hfun]
  exact ((h1.sub_const (φ x)).sub h2).sub h3

/-- The derivative equals the increment applied to the direction. -/
theorem err2_deriv_eq_increment {φ : EuclSpace d → ℝ} (x w : EuclSpace d)
    (t : ℝ) :
    fderiv ℝ φ (x + t • w) w - fderiv ℝ φ x w
        - t * fderiv ℝ (fderiv ℝ φ) x w w
      = (fderiv ℝ φ (x + t • w) - fderiv ℝ φ x
          - fderiv ℝ (fderiv ℝ φ) x (t • w)) w := by
  simp only [sub_apply, ContinuousLinearMap.map_smul,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]

end

end PLaplacian
