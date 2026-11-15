/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ExtremeExpansion

@[expose] public section

/-!
# The singular case

Where the gradient vanishes there is no gradient direction, and none of the
machinery of Plaplacian.GradDir applies. The linear term of the Taylor
expansion is simply absent, and the supremum over the ball is governed by the
largest value of the quadratic form, namely epsilon squared times the largest
eigenvalue.

That is exactly the closed-form envelope of Plaplacian.Viscosity: at a
singular point the expansion produces lamMax for the supremum and lamMin for
the infimum, in place of the infinity Laplacian. So the envelope is not an
arbitrary convention but what the asymptotics actually give, which closes the
circle between the viscosity definitions of Layer 2 and the expansion of Layer
3.

## A side condition the informal statement omits

The bound by epsilon squared times lamMax requires lamMax to be nonnegative.
Without that hypothesis it is false: if the form is negative definite then
lamMax is negative, and multiplying by the smaller squared norm gives a larger
value, reversing the inequality. The hypothesis holds where the result is
applied, since at a maximum the relevant form is not negative definite, but it
has to be carried rather than assumed away.

## Main results

- fderiv_eq_zero_of_gradient_eq_zero, decomp_at_singular
- quad_eq_norm_sq_mul
- quad_le_lamMax_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The singular case -/

theorem fderiv_eq_zero_of_gradient_eq_zero {φ : EuclSpace d → ℝ}
    {x : EuclSpace d} (hx : gradient φ x = 0) (z : EuclSpace d) :
    fderiv ℝ φ x z = 0 := by
  rw [← inner_gradient_left, hx, inner_zero_left]

theorem decomp_at_singular {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x = 0) (z : EuclSpace d) :
    φ (x + z) = φ x + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x z z
      + taylorErr φ x z := by
  rw [decomp_at φ x z, fderiv_eq_zero_of_gradient_eq_zero hx]
  ring

/-- The quadratic form at `z`, in terms of the form at the normalized `z`. -/
theorem quad_eq_norm_sq_mul (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    {z : EuclSpace d} (hz : z ≠ 0) :
    X z z = ‖z‖ ^ 2 * infLaplacianOf z X := by
  unfold infLaplacianOf
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  simp only [ContinuousLinearMap.map_smul, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  field_simp

/-- **The quadratic form over the ball is at most `ε²` times the largest
eigenvalue**, provided that eigenvalue is nonnegative --- which holds whenever
the form is not negative definite, and in particular at a maximum. -/
theorem quad_le_lamMax_ball (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    {z : EuclSpace d} {ε : ℝ} (hz : ‖z‖ ≤ ε) (hzne : z ≠ 0)
    (hpos : 0 ≤ lamMax X) :
    X z z ≤ ε ^ 2 * lamMax X := by
  rw [quad_eq_norm_sq_mul X hzne]
  have h1 : infLaplacianOf z X ≤ lamMax X :=
    infLaplacianOf_le_lamMax hzne X
  have h2 : ‖z‖ ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    nlinarith [hz, h0]
  have h3 : (0:ℝ) ≤ ‖z‖ ^ 2 := by positivity
  nlinarith [h1, h2, h3, hpos]

end

end PLaplacian
