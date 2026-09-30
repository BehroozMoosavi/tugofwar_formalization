/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Uniform

/-!
# The derivative of the error along a ray

The second-order Taylor error, restricted to a ray and differentiated term by
term. Combining the three gives the derivative as the derivative increment
applied to the direction, which is the quantity the uniform estimate bounds.

Each term is isolated. Attempting the derivative in one step needs several
attempts; term by term each is a short computation, and the chain rule along
the ray is the lemma proved in the second layer for the necessary condition.

## Main results

- hasDerivAt_ray, hasDerivAt_linear, hasDerivAt_quad
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The derivative of the error along a ray

`err2 φ x (t • w)` as a function of `t`. Its derivative is

  `(Dφ (x + t w) - Dφ x - D²φ x (t w)) w`,

which is exactly the quantity `fderiv_increment_small` bounds, applied to `w`.

The computation is term by term. The first term is `φ (x + t w)`, whose
derivative is `Dφ (x + t w) w` by the chain rule --- the lemma
`hasDerivAt_first` of the second layer. The second is constant. The third is
linear in `t`, the fourth quadratic.
-/


/-- The first term's derivative: the chain rule along the ray. -/
theorem hasDerivAt_ray {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x w : EuclSpace d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • w))
      (fderiv ℝ φ (x + t • w) w) t := by
  have h := hasDerivAt_first hφ x w t
  simpa [lineMap] using h

/-- The linear term's derivative. -/
theorem hasDerivAt_linear {φ : EuclSpace d → ℝ} (x w : EuclSpace d)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ x (s • w))
      (fderiv ℝ φ x w) t := by
  have h : (fun s : ℝ => fderiv ℝ φ x (s • w))
      = fun s : ℝ => s * fderiv ℝ φ x w := by
    funext s
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [h]
  simpa using (hasDerivAt_id t).mul_const (fderiv ℝ φ x w)

/-- The quadratic term's derivative. -/
theorem hasDerivAt_quad {φ : EuclSpace d → ℝ} (x w : EuclSpace d)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        (1/2) * fderiv ℝ (fderiv ℝ φ) x (s • w) (s • w))
      (t * fderiv ℝ (fderiv ℝ φ) x w w) t := by
  have h : (fun s : ℝ =>
        (1/2) * fderiv ℝ (fderiv ℝ φ) x (s • w) (s • w))
      = fun s : ℝ => (1/2) * s ^ 2
          * fderiv ℝ (fderiv ℝ φ) x w w := by
    funext s
    simp only [ContinuousLinearMap.map_smul, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  have hd := (hasDerivAt_pow 2 t).const_mul ((1:ℝ)/2)
  have hd2 := hd.mul_const (fderiv ℝ (fderiv ℝ φ) x w w)
  simpa using hd2

end

end PLaplacian
