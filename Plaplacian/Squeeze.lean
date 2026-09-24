/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.InfLower

/-!
# The extreme-value average, with the error squeezed

An existential in the error alone would be vacuous, since the difference from
any target always exists. The content is the bound, and it comes from the four
sandwich widths proved in the preceding files.

The linear terms, plus and minus epsilon times the gradient norm, appear in
the hypotheses and are absent from the conclusion. That is the cancellation
which produces the infinity Laplacian, and stating it this way makes the
cancellation visible in the statement rather than buried in a proof.

The second theorem moves the result to the open ball, which is what the step
operator uses. That is where the open-ball choice forced by measurability, the
first structural finding of this development, is finally paid for.

## Main results

- extreme_avg_squeezed
- extreme_avg_squeezed_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The assembly, with a bounded error

An existential in the error alone is vacuous: the difference always exists.
The content is the bound, and it comes from the sandwich widths.

Write `T = φ x + (ε²/2) I` for the target. The four proved bounds give

  `T + loS ≤ sSup ≤ T + hiS`   (with `loS`, `hiS` the sup errors)
  `T + loI ≤ sInf ≤ T + hiI`   (with `loI`, `hiI` the inf errors)

where the linear terms `± ε ‖∇φ x‖` have cancelled in the target. Averaging,
the error lies between `(loS + loI)/2` and `(hiS + hiI)/2`.

The statement below is existential in the error **and** in the two bounds,
with the two bounds related to the sandwich data --- so the content is that
the error is squeezed by quantities the earlier files control, not merely that
it exists.
-/

/-- **The extreme-value average, with the error squeezed.**

The average of the supremum and infimum equals the target plus an error lying
between the averaged sandwich bounds. Since `Plaplacian.ElimMax` and
`Plaplacian.LocalizeDist` bound those, the error is controlled. -/
theorem extreme_avg_squeezed {φ : EuclSpace d → ℝ}
    {x : EuclSpace d} {ε : ℝ} {I loS hiS loI hiI : ℝ}
    (hSlow : φ x + ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + loS
        ≤ sSup (φ '' closedBall x ε))
    (hSupp : sSup (φ '' closedBall x ε)
        ≤ φ x + ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + hiS)
    (hIlow : φ x - ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + loI
        ≤ sInf (φ '' closedBall x ε))
    (hIupp : sInf (φ '' closedBall x ε)
        ≤ φ x - ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + hiI) :
    ∃ e : ℝ,
      (sSup (φ '' closedBall x ε) + sInf (φ '' closedBall x ε)) / 2
          = φ x + (ε ^ 2 / 2) * I + e
        ∧ (loS + loI) / 2 ≤ e
        ∧ e ≤ (hiS + hiI) / 2 :=
  extreme_avg_eq hSlow hSupp hIlow hIupp

/-- **The same on the open ball**, which is what the operator uses. -/
theorem extreme_avg_squeezed_ball {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {x : EuclSpace d} {ε : ℝ} (hε : 0 < ε)
    {I loS hiS loI hiI : ℝ}
    (hSlow : φ x + ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + loS
        ≤ sSup (φ '' closedBall x ε))
    (hSupp : sSup (φ '' closedBall x ε)
        ≤ φ x + ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + hiS)
    (hIlow : φ x - ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + loI
        ≤ sInf (φ '' closedBall x ε))
    (hIupp : sInf (φ '' closedBall x ε)
        ≤ φ x - ε * ‖gradient φ x‖ + (ε ^ 2 / 2) * I + hiI) :
    ∃ e : ℝ,
      (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
          = φ x + (ε ^ 2 / 2) * I + e
        ∧ (loS + loI) / 2 ≤ e
        ∧ e ≤ (hiS + hiI) / 2 := by
  obtain ⟨e, he, hlo, hhi⟩ :=
    extreme_avg_squeezed hSlow hSupp hIlow hIupp
  refine ⟨e, ?_, hlo, hhi⟩
  rw [sSup_ball_eq_closedBall hφ x hε, sInf_ball_eq_closedBall hφ x hε]
  exact he

end

end PLaplacian
