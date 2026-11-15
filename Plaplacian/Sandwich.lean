/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.OpExpansion

@[expose] public section

/-!
# From sandwich to equality

The extreme-value expansion gives two-sided bounds; the expansion of the
operator wants an equality with an error term. The conversion is formal:
define the error as the difference from the target, and the sandwich bounds
it.

The case that matters is the average of the supremum and the infimum. There
the linear terms, plus epsilon times the gradient norm in the supremum
sandwich and minus the same in the infimum sandwich, cancel on averaging,
leaving the value at the centre plus the infinity-Laplacian term plus a
bounded error. That cancellation is the reason the extreme-value half of the
operator produces the infinity Laplacian, and it is visible in the statement
of extreme_avg_eq.

With this, the extreme-value hypothesis of the expansion theorem is
discharged from proved results rather than assumed.

## Main results

- eq_add_err_of_le_of_le, eq_add_err_of_sandwich
- extreme_avg_eq
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## From sandwich to equality

`Plaplacian.ExtremeExpansion` gives two-sided bounds on the supremum. The
expansion theorem wants an equality with an error term. The conversion is
formal: define the error as the difference, and the sandwich bounds it.

Stated generally, since the same conversion applies to the supremum, the
infimum, and their average.
-/

/-- **Sandwich to equality.** Any quantity lying between two bounds equals the
lower one plus a nonnegative error at most the sandwich width. -/
theorem eq_add_err_of_le_of_le {a S U : ℝ} (hlow : a ≤ S) (hupp : S ≤ U) :
    ∃ e : ℝ, S = a + e ∧ 0 ≤ e ∧ e ≤ U - a := by
  refine ⟨S - a, by ring, by linarith, by linarith⟩

/-- The version with a target value and a symmetric error, which is the form
the expansion consumes. -/
theorem eq_add_err_of_sandwich {T S lo hi : ℝ}
    (hlow : T + lo ≤ S) (hupp : S ≤ T + hi) :
    ∃ e : ℝ, S = T + e ∧ lo ≤ e ∧ e ≤ hi := by
  refine ⟨S - T, by ring, by linarith, by linarith⟩

/-- **The average of the extreme values, as an equality.**

Given the sandwich on the supremum and the dual on the infimum, their average
equals the value at the centre plus the infinity-Laplacian term plus an error
bounded by the two sandwich widths. -/
theorem extreme_avg_eq {φ : EuclSpace d → ℝ} {x : EuclSpace d} {ε : ℝ}
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
      (sSup (φ '' closedBall x ε) + sInf (φ '' closedBall x ε)) / 2
          = φ x + (ε ^ 2 / 2) * I + e
        ∧ (loS + loI) / 2 ≤ e ∧ e ≤ (hiS + hiI) / 2 := by
  refine ⟨(sSup (φ '' closedBall x ε) + sInf (φ '' closedBall x ε)) / 2
    - (φ x + (ε ^ 2 / 2) * I), by ring, by linarith, by linarith⟩

end

end PLaplacian
