/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.QuadInf

/-!
# The extreme-value expansion

The supremum over the closed ball equals the value at the centre, plus epsilon
times the gradient norm, plus epsilon squared over two times the infinity
Laplacian, up to an explicit error.

The lower bound follows from the value at the shifted point. The upper bound
uses the maximizer, whose quadratic term is compared to the one at the shifted
point by the bilinear estimate, with the comparison controlled by the
localization.

The error is left explicit rather than collapsed into a little-o, since that
is the form a convergence proof consumes and since the quantitative content
would otherwise be discarded.

Combined with the average expansion of Plaplacian.AvgExpansion, this gives
both halves of the asymptotic expansion of the step operator: the average part
produces the ordinary Laplacian, the extreme-value part the infinity
Laplacian, and the weights alpha and beta combine them into the normalized
p-Laplacian.

## Main results

- sSup_lower_infLap
- sSup_upper_infLap
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The extreme-value expansion

Packaging the sandwich. Write `Q = (ε²/2) Δ^N_∞ φ x` for the target quadratic
term and `L = ε ‖∇φ x‖` for the linear one. The lower bound gives

  `φ x + L + Q + err_s ≤ sup`,

using `quad_at_shift` to identify the quadratic term. The upper bound gives a
maximizer `y` with

  `sup ≤ φ x + L + (1/2) D²φ x (w,w) + err_y`,   `w = y - x`,

and `quad_diff_bound` with `quad_at_shift` bounds
`(1/2) D²φ x (w,w) - Q` by half the quadratic comparison error.

The statement below is the two-sided form with the error left explicit, since
that is what a convergence proof consumes and since collapsing it into a
little-o would discard the quantitative content.
-/

/-- **The lower bound, with the infinity Laplacian identified.** -/
theorem sSup_lower_infLap {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    φ x + ε * ‖gradient φ x‖
        + (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x)
        + taylorErr φ x (ε • gradDir φ x)
      ≤ sSup (φ '' closedBall x ε) := by
  have h := sSup_lower_bound hφ hx hε
  rwa [quad_at_shift x ε] at h

/-- **The upper bound, with the quadratic term compared to the target.** -/
theorem sSup_upper_infLap {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      sSup (φ '' closedBall x ε)
        ≤ φ x + ε * ‖gradient φ x‖
          + (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
              (fderiv ℝ (fderiv ℝ φ) x)
          + (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
              * ‖(y - x) - ε • gradDir φ x‖
              * (‖y - x‖ + ‖ε • gradDir φ x‖))
          + taylorErr φ x (y - x) := by
  obtain ⟨y, hyMem, hyLe⟩ := sSup_upper_bound hφ hx hε
  refine ⟨y, hyMem, ?_⟩
  have hcmp := quad_diff_bound (fderiv ℝ (fderiv ℝ φ) x) (y - x)
    (ε • gradDir φ x)
  have hcmp' := (abs_le.1 hcmp).2
  have hq := quad_at_shift (φ := φ) x ε
  -- the quadratic term at the maximizer, in terms of the target
  have hstep : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
      ≤ (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x)
        + (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
            * ‖(y - x) - ε • gradDir φ x‖
            * (‖y - x‖ + ‖ε • gradDir φ x‖)) := by
    have hqq : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
        (ε • gradDir φ x)
        = (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x) := hq
    linarith [hcmp', hqq]
  linarith [hyLe, hstep]

end

end PLaplacian
