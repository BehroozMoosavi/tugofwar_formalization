/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Domination

@[expose] public section

/-!
# The lower bound on the infimum

The dual of the supremum upper bound, obtained the same way: apply it to the
negation and negate. Together with the upper bound on the infimum this
completes the infimum sandwich, so all four hypotheses of the sandwich-to-
equality conversion are available.

The error terms remain stated for the negation. That is acceptable, since the
conversion takes the error bounds abstractly.

## Main results

- sInf_lower_infLap
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The lower bound on the infimum

The dual of `sSup_upper_infLap`, obtained the same way: apply the supremum
upper bound to the negation and negate. The infimum is then bounded **below**,
which together with `sInf_upper_infLap` completes the infimum sandwich.

As with the supremum, the bound carries a minimizer, and the error terms are
those of the negation.
-/


/-- **The lower bound on the infimum.** -/
theorem sInf_lower_infLap {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      φ x - ε * ‖gradient φ x‖
          + (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
              (fderiv ℝ (fderiv ℝ φ) x)
          - (1 / 2) * (‖fderiv ℝ (fderiv ℝ (fun z => -φ z)) x‖
              * ‖(y - x) - ε • gradDir (fun z => -φ z) x‖
              * (‖y - x‖ + ‖ε • gradDir (fun z => -φ z) x‖))
          - taylorErr (fun z => -φ z) x (y - x)
        ≤ sInf (φ '' closedBall x ε) := by
  obtain ⟨y, hyMem, hyLe⟩ := sSup_upper_infLap (contDiff_neg' hφ)
    (gradient_neg_ne_zero hx) hε
  refine ⟨y, hyMem, ?_⟩
  rw [norm_gradient_neg, infLaplacianOf_neg] at hyLe
  have hinf : sInf (φ '' closedBall x ε)
      = - sSup ((fun z => -φ z) '' closedBall x ε) :=
    sInf_eq_neg_sSup φ (closedBall x ε)
  rw [hinf]
  linarith [hyLe]

end

end PLaplacian
