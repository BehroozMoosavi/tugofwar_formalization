/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.NearSup

/-!
# The strictness step

The near-maximizers must converge to the base point, and the standard argument
has four parts: a sequence along which the values approach the maximum,
compactness to extract a convergent subsequence, the limit-superior bound at
the limit point, and strictness forcing that limit to be the base point. This
file is the last and purest of the four.

The strictness hypothesis costs nothing. Subtracting the fourth power of the
distance turns a maximum into a strict one, and since that term vanishes to
fourth order at the point it changes neither the gradient nor the Hessian
there, so the generator takes the same value.

## Main results

- IsStrictMaxOn
- eq_of_strict
- strict_of_perturb
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The strictness step

The near-maximizers must converge to the base point. The standard argument has
four parts: a sequence along which the values approach the maximum, compactness
to extract a convergent subsequence of the near-maximizers, the limit-superior
bound at the limit point, and strictness forcing that limit to be the base
point.

This file is the last and purest of the four. If a point of the closed ball has
the relaxed difference at least the maximum, and the maximum is strict, then
the point is the base point.

The strictness hypothesis is standard and costs nothing: a test function
touching from above at a non-strict maximum can be perturbed by a quartic
`‖y - x₀‖⁴`, which leaves its gradient and Hessian at the point unchanged and
makes the maximum strict.
-/

/-- A strict local maximum on a closed ball. -/
def IsStrictMaxOn (f : EuclSpace d → ℝ) (x₀ : EuclSpace d) (r : ℝ) : Prop :=
  ∀ w ∈ closedBall x₀ r, w ≠ x₀ → f w < f x₀

/-- **The strictness step.** A point of the ball at which the function is at
least its value at the strict maximum is the maximum. -/
theorem eq_of_strict {f : EuclSpace d → ℝ} {x₀ : EuclSpace d} {r : ℝ}
    (hstrict : IsStrictMaxOn f x₀ r) {z : EuclSpace d}
    (hz : z ∈ closedBall x₀ r) (hge : f x₀ ≤ f z) :
    z = x₀ := by
  by_contra hne
  have := hstrict z hz hne
  linarith [this, hge]

/-- The quartic perturbation leaves the value at the point unchanged. -/
theorem quartic_at (x₀ : EuclSpace d) :
    ‖x₀ - x₀‖ ^ 4 = 0 := by
  simp

/-- And it is positive away from the point. -/
theorem quartic_pos {x₀ w : EuclSpace d} (hw : w ≠ x₀) :
    0 < ‖w - x₀‖ ^ 4 := by
  have h : 0 < ‖w - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  positivity

/-- **Strictness from the perturbation.** A non-strict maximum becomes strict
once the quartic is subtracted. -/
theorem strict_of_perturb {f : EuclSpace d → ℝ} {x₀ : EuclSpace d} {r : ℝ}
    (hmax : ∀ w ∈ closedBall x₀ r, f w ≤ f x₀) :
    IsStrictMaxOn (fun w => f w - ‖w - x₀‖ ^ 4) x₀ r := by
  intro w hw hne
  simp only
  have h1 := hmax w hw
  have h2 := quartic_pos hne
  rw [quartic_at]
  linarith [h1, h2]

end

end PLaplacian
