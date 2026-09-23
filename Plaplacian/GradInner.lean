/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Localize

/-!
# The derivative in terms of the gradient direction

The localization bound needs a lower bound on the inner product of the
normalized gradient with the increment. These lemmas convert derivatives into
that form.

The identity generalizes fderiv_gradDir from the direction itself to an
arbitrary increment: the derivative equals the gradient norm times the inner
product with the direction. Paired with Cauchy-Schwarz, which bounds that
inner product by the norm of the increment, it pins the inner product to
within order epsilon squared of epsilon, which is what the localization
consumes.

## Main results

- fderiv_eq_norm_mul_inner, fderiv_eq_at_shift
- inner_gradDir_le
- quadratic_le_of_norm_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The derivative in terms of the gradient direction

`norm_sub_shift_le` needs a lower bound on the inner product of the gradient
direction with the increment. The identity below converts the derivative into
exactly that form, generalising `fderiv_gradDir` from the direction itself to
an arbitrary increment.
-/

/-- **The derivative at an arbitrary increment.** -/
theorem fderiv_eq_norm_mul_inner {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) (w : EuclSpace d) :
    fderiv ℝ φ x w = ‖gradient φ x‖ * inner ℝ (gradDir φ x) w := by
  rw [← inner_gradient_left]
  unfold gradDir
  rw [real_inner_smul_left]
  have hn : ‖gradient φ x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp

/-- The derivative at the shifted increment, as a special case. -/
theorem fderiv_eq_at_shift {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) (ε : ℝ) :
    fderiv ℝ φ x (ε • gradDir φ x) = ε * ‖gradient φ x‖ := by
  rw [fderiv_eq_norm_mul_inner hx, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_gradDir hx]
  ring

/-- Cauchy--Schwarz in the form the localization needs: the inner product with
the unit direction is at most the norm of the increment. -/
theorem inner_gradDir_le {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) (w : EuclSpace d) :
    inner ℝ (gradDir φ x) w ≤ ‖w‖ := by
  have h := real_inner_le_norm (gradDir φ x) w
  rwa [norm_gradDir hx, one_mul] at h


/-- A bilinear form of small norm has small quadratic form. Proved here rather
than in the Taylor files, where it was first needed, so that the deficit chain
has it available. -/
theorem quadratic_le_of_norm_le (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    {η : ℝ} (hX : ‖X‖ ≤ η) (z : EuclSpace d) :
    |X z z| ≤ η * ‖z‖ ^ 2 := by
  have h1 : ‖X z z‖ ≤ ‖X z‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖X z‖ ≤ ‖X‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
  have hz : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  simp only [Real.norm_eq_abs] at h1
  nlinarith [h1, h2, hz, norm_nonneg (X z)]

end

end PLaplacian
