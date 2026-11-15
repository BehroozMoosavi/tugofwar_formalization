/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LocUnif

@[expose] public section

/-!
# The supremum bound at an exported maximizer

The earlier upper bound on the supremum returns some point with a bound, but
does not say the point is the maximizer, and the localization needs exactly
that, at the same point. So the witness of one could not be handed to the
other.

The maximizer is obtained once here and three properties derived at it: it
attains the supremum, it dominates the shifted point, and the upper bound
holds. Sharing the witness is what lets the localization act on the very point
the bound speaks about.

This is another instance of a statement that does not export what the next
step consumes, the failure recorded among the findings on assembling a chain
from both ends.

## Main results

- sup_upper_at_max
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supremum's upper bound at an exported maximizer

`sSup_upper_infLap` returns some point with an upper bound, but does not say
the point is the maximizer. The localization needs exactly that, at the same
point: its domination hypothesis is that the value there dominates the value at
the shifted point. So one lemma's witness cannot be handed to the other.

This is the junction problem once more --- a statement that does not export
what the next step consumes. The remedy is to obtain the maximizer once and
derive at it all three properties the uniform argument needs: that it attains
the supremum, that it dominates the shifted point, and the upper bound. The
steps are those of the earlier upper bound, kept in one proof so that the
witness is shared.
-/


/-- **The maximizer, with attainment, domination and the upper bound.** -/
theorem sup_upper_at_max {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      sSup (φ '' closedBall x ε) = φ y
      ∧ φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x)
      ∧ sSup (φ '' closedBall x ε)
          ≤ φ x + ε * ‖gradient φ x‖
            + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
                (fderiv ℝ (fderiv ℝ φ) x)
            + (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
                * ‖(y - x) - ε • gradDir φ x‖
                * (‖y - x‖ + ‖ε • gradDir φ x‖))
            + taylorErr φ x (y - x) := by
  obtain ⟨y, hyMem, hySup⟩ := exists_sSup_closedBall hφ.continuous x hε
  have hxy : x + (y - x) = y := by abel
  -- domination: the maximizer's value is the supremum, which dominates
  have hdom : φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x) := by
    rw [hxy, ← hySup]
    exact le_sSup_shift hφ.continuous x (norm_gradDir hx) hε
  refine ⟨y, hyMem, hySup, hdom, ?_⟩
  -- the decomposed value at the maximizer
  have hval : sSup (φ '' closedBall x ε)
      = φ x + ‖gradient φ x‖ * inner ℝ (gradDir φ x) (y - x)
        + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
        + taylorErr φ x (y - x) := by
    rw [hySup]
    conv_lhs => rw [← hxy]
    rw [decomp_at φ x (y - x), fderiv_eq_norm_mul_inner hx]
  -- the linear term is at most ε times the gradient norm
  have hcs : inner ℝ (gradDir φ x) (y - x) ≤ ε := by
    have h1 := inner_gradDir_le hx (y - x)
    have h2 := norm_sub_le_of_mem hyMem
    linarith [h1, h2]
  have hgnn : (0:ℝ) ≤ ‖gradient φ x‖ := norm_nonneg _
  -- the quadratic term, compared with the one at the shifted point
  have hcmp := quad_diff_bound (fderiv ℝ (fderiv ℝ φ) x) (y - x)
    (ε • gradDir φ x)
  have hcmp' := (abs_le.1 hcmp).2
  have hq := quad_at_shift (φ := φ) x ε
  have hstep : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
      ≤ ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x)
        + (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
            * ‖(y - x) - ε • gradDir φ x‖
            * (‖y - x‖ + ‖ε • gradDir φ x‖)) := by
    have hqq : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
        (ε • gradDir φ x)
        = ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x) := hq
    linarith [hcmp', hqq]
  rw [hval]
  nlinarith [hcs, hgnn, hstep]

end

end PLaplacian
